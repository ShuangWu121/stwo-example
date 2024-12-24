use itertools::Itertools;
use num_traits::One;

use crate::constraint_framework::{
    assert_constraints, EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use crate::core::backend::simd::column::BaseColumn;
use crate::core::backend::simd::m31::LOG_N_LANES;
use crate::core::backend::simd::SimdBackend;
use crate::core::channel::Blake2sChannel;
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::SecureField;
use crate::core::pcs::{CommitmentSchemeProver, PcsConfig};
use crate::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use crate::core::poly::BitReversedOrder;
use crate::core::prover::{prove, StarkProof};
use crate::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use crate::core::ColumnVec;

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
    circuit: &IncrementalOneCircuitTrace,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_size).circle_domain();
    [&circuit.a, &circuit.b]
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval.clone()))
        .collect()
}

#[allow(unused)]
pub fn prove_incremental_one(
    log_n_rows: u32,
    config: PcsConfig,
) -> (IncrementalOneComponent, StarkProof<Blake2sMerkleHasher>) {
    assert!(log_n_rows >= LOG_N_LANES);

    let range = 0..(1 << log_n_rows);
    // Generate `a` and `b` as mutable vectors first
    let mut a: Vec<_> = range.clone().map(|i| i.into()).collect(); 
    let mut b: Vec<_> = range
        .clone()
        .map(|i| {
            if i == (1 << log_n_rows) - 1 {
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
    let mut circuit = IncrementalOneCircuitTrace {
        a: a.iter().map(|&i: &i32| i.into()).collect(),
        b: b.iter().map(|&i: &i32| i.into()).collect(),
    };
    println!("trace a is {:?}", circuit.a);
    println!("trace b is {:?}", circuit.b);

    // Precompute twiddles
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );
    println!("twiddles is {:?}", twiddles.root_coset);

    // Setup protocol.
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    let constants_trace_location = tree_builder.extend_evals([]);
    tree_builder.commit(channel);

    // Trace.
    let trace = gen_trace(log_n_rows, &circuit);
    let mut tree_builder = commitment_scheme.tree_builder();
    let base_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    // Prove constraints.
    let component = IncrementalOneComponent::new(
        &mut TraceLocationAllocator::default(),
        IncrementalOneEval { log_n_rows },
        (SecureField::one(), None),
    );

    // Sanity check. Remove for production.
    let trace_polys = commitment_scheme
        .trees
        .as_ref()
        .map(|t| t.polynomials.iter().cloned().collect_vec());
    assert_constraints(
        &trace_polys,
        CanonicCoset::new(log_n_rows),
        |mut eval| {
            component.evaluate(eval);
        },
        (SecureField::one(), None),
    );

    let proof = prove(&[&component], channel, commitment_scheme).unwrap();

    (component, proof)
}

#[cfg(test)]
mod tests {
    use std::env;

    use crate::core::air::Component;
    use crate::core::channel::Blake2sChannel;
    use crate::core::fri::FriConfig;
    use crate::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
    use crate::core::prover::verify;
    use crate::core::vcs::blake2_merkle::Blake2sMerkleChannel;
    use crate::examples::incremental_one::prove_incremental_one;

    #[test]
    fn test_simd_plonk_prove() {
        // Get from environment variable:
        let log_n_instances = env::var("LOG_N_INSTANCES")
            .unwrap_or_else(|_| "4".to_string())
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
        let (component, proof) = prove_incremental_one(log_n_instances, config);

        // Verify.
        // TODO: Create Air instance independently.
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        // Decommit.
        // Retrieve the expected column sizes in each commitment interaction, from the AIR.
        let sizes = component.trace_log_degree_bounds();

        // Preprocessed columns.
        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);

        // Trace columns.
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);

        verify(&[&component], channel, commitment_scheme, proof).unwrap();
    }
}
