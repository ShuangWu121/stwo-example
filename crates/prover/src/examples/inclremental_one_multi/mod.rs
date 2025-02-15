
use num_traits::Zero;

use crate::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator, //assert_constraints,
};

use crate::core::air::ComponentProver;
use crate::core::air::Component;
use crate::core::backend::simd::column::BaseColumn;
use crate::core::backend::simd::m31::LOG_N_LANES;
use crate::core::backend::simd::SimdBackend;
use crate::core::channel::{Blake2sChannel};
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::SecureField;
use crate::core::pcs::{CommitmentSchemeProver, PcsConfig};
use crate::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use crate::core::poly::BitReversedOrder;
use crate::core::prover::prove;
use crate::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use crate::core::ColumnVec;
use crate::core::pcs::CommitmentSchemeVerifier;
use itertools::chain;
use itertools::Itertools;

use crate::core::prover::verify;


pub type IncrementalOneComponent = FrameworkComponent<IncrementalOneEval>;


#[derive(Clone)]
pub struct IncrementalOneEval {
    pub log_n_rows: u32,
}
impl FrameworkEval for IncrementalOneEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a_next = &eval.next_interaction_mask(1, [1])[0];
        let b = eval.next_trace_mask();

        eval.add_constraint(b.clone() - a_next.clone());

        eval
    }
}

#[derive(Clone)]
pub struct IncrementalOneCircuitTrace {
    pub a: BaseColumn,
    pub b: BaseColumn,
}
pub fn gen_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_size).circle_domain();

    let range = 0..(1 << log_size);
    // Generate `a` and `b` as mutable vectors first
    let mut a: Vec<_> = range.clone().map(|i| i.into()).collect(); 
    let mut b: Vec<_> = range
        .clone()
        .map(|i| {
            if i == (1 << log_size) - 1 {
                0.into() // Last element is 0
            } else {
                (i + 1).into() // Increment for all other elements
            }
        })
        .collect(); 
    println!("a is {:?}", a); // a = [0, 1, 2, ..., n]
    println!("b is {:?}", b); // b = [1, 2, ..., 0]
    // Reorder `a` and `b` before assigning them to the struct
    crate::core::utils::bit_reverse_coset_to_circle_domain_order(&mut a);
    crate::core::utils::bit_reverse_coset_to_circle_domain_order(&mut b);

    // Assign reordered `a` and `b` to the struct
    let circuit = IncrementalOneCircuitTrace {
        a: a.iter().map(|&i: &i32| i.into()).collect(),
        b: b.iter().map(|&i: &i32| i.into()).collect(),
    };
    println!("trace a is {:?}", circuit.a);
    println!("trace b is {:?}", circuit.b);

    [&circuit.a, &circuit.b]
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval.clone()))
        .collect()
}

#[allow(unused)]
pub fn prove_verify_incremental_one<'a>(
    log_n_rows: u32,
    config: PcsConfig,
) {
    assert!(log_n_rows >= LOG_N_LANES);

    

    // Precompute twiddles
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );
    

    // Setup protocol.
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    // Preprocessed columns.

    let mut tree_builder = commitment_scheme.tree_builder();
    let constants_trace_location = tree_builder.extend_evals([]);
    tree_builder.commit(channel);
    //channel.mix_u64(log_n_rows as u64);
    //channel.mix_u64((log_n_rows-1) as u64);

    // Trace.
    let trace_0 = gen_trace(log_n_rows);
    let trace_1 = gen_trace(log_n_rows-1);

    println!("\n trace_0 is {:?} \n", trace_0);
    println!("\n trace_1 is {:?} \n", trace_1);

    let trace = chain![trace_0.clone(), trace_1.clone()].collect_vec();

    let mut tree_builder = commitment_scheme.tree_builder();
    let base_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    // create the first component
    let mut tree_span_provider = &mut TraceLocationAllocator::default();
    let component0 = IncrementalOneComponent::new(
        tree_span_provider,
        IncrementalOneEval { log_n_rows:log_n_rows },
        (SecureField::zero(), None),
    );

    let component1 = IncrementalOneComponent::new(
        tree_span_provider,
        IncrementalOneEval { log_n_rows:log_n_rows-1 },
        (SecureField::zero(), None),
    );

    let components = &[&component0 as &dyn ComponentProver<SimdBackend>, &component1 as &dyn ComponentProver<SimdBackend>];

    let components_verifier = &[&component0 as &dyn Component, &component1 as &dyn Component];

    //Sanity check. Remove for production.
    // let trace_polys = commitment_scheme
    //     .trees
    //     .as_ref()
    //     .map(|t| t.polynomials.iter().cloned().collect_vec());
    // assert_constraints(
    //     &trace_polys,
    //     CanonicCoset::new(log_n_rows),
    //     |mut eval| {
    //         component0.evaluate(eval);
    //     },
    //     (SecureField::zero(), None),
    // );

    println!("\n starting to generate proof.................. \n");
    println!("log_n_rows is {:?}", log_n_rows);

    let proof = prove(components, channel, commitment_scheme).unwrap();
    println!("proof commitment are {:?}", proof.commitments);

    println!("\n proof is generated.................. \n");

    // Verify.
        // TODO: Create Air instance independently.
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme_verifier = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        // Decommit.
        // Retrieve the expected column sizes in each commitment interaction, from the AIR.
        // Preprocessed columns.
        commitment_scheme_verifier.commit(proof.commitments[0], &[], channel);

        // Trace columns.
        commitment_scheme_verifier.commit(proof.commitments[1], &[log_n_rows,log_n_rows,log_n_rows-1,log_n_rows-1], channel);

        verify(components_verifier, channel, commitment_scheme_verifier, proof).unwrap();

}

#[cfg(test)]
mod tests {
    use std::env;
    use crate::core::fri::FriConfig;
    use crate::core::pcs::PcsConfig;
    use crate::examples::inclremental_one_multi::prove_verify_incremental_one;

    #[test]
    fn test_simd_prove_multi() {
        // Get from environment variable:
        let log_n_instances = env::var("LOG_N_INSTANCES")
            .unwrap_or_else(|_| "6".to_string())
            .parse::<u32>()
            .unwrap();
        let config = PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(0, 1, 100),
        };
        println!(
            "starting test_simd_plonk_prove with log_n_instances: {}",
            log_n_instances
        );
        // Prove.
        prove_verify_incremental_one(log_n_instances, config);

        
    }
}
