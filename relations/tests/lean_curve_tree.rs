extern crate relations;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_pallas::Fq as PallasBase;
use ark_pallas::PallasConfig;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use rand::prelude::SliceRandom;
use relations::curve_tree::{CurveTree, Root, SelRerandParameters};
use relations::lean_curve_tree::LeanCurveTree;
use std::collections::BTreeSet;

mod common;
use common::check_proof;

#[test]
pub fn insert_small() {
    check_inserts::<2, PallasBase, PallasConfig, VestaConfig>(1, 11, 2, 2, true);
    check_inserts::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, 4, 4, true);
    check_inserts::<2, PallasBase, PallasConfig, VestaConfig>(3, 11, 8, 4, true);
    check_inserts::<2, PallasBase, PallasConfig, VestaConfig>(4, 11, 16, 10, true);
    check_inserts::<3, PallasBase, PallasConfig, VestaConfig>(2, 11, 9, 5, true);
    check_inserts::<3, PallasBase, PallasConfig, VestaConfig>(3, 11, 27, 10, true);
    check_inserts::<4, PallasBase, PallasConfig, VestaConfig>(1, 11, 4, 4, true);
    check_inserts::<4, PallasBase, PallasConfig, VestaConfig>(2, 11, 16, 10, true);
    check_inserts::<4, PallasBase, PallasConfig, VestaConfig>(3, 11, 64, 10, true);
    check_inserts::<4, PallasBase, PallasConfig, VestaConfig>(4, 11, 256, 10, true);
    check_inserts::<5, PallasBase, PallasConfig, VestaConfig>(2, 11, 25, 10, true);
    check_inserts::<5, PallasBase, PallasConfig, VestaConfig>(3, 11, 125, 10, true);
}

#[test]
pub fn insert_large() {
    check_inserts::<256, PallasBase, PallasConfig, VestaConfig>(3, 13, 200, 20, false);
    check_inserts::<256, PallasBase, PallasConfig, VestaConfig>(4, 13, 200, 20, false);
    check_inserts::<256, PallasBase, PallasConfig, VestaConfig>(5, 13, 200, 20, false);
    check_inserts::<512, PallasBase, PallasConfig, VestaConfig>(3, 13, 200, 20, false);
    check_inserts::<512, PallasBase, PallasConfig, VestaConfig>(4, 13, 200, 20, false);
    check_inserts::<512, PallasBase, PallasConfig, VestaConfig>(5, 13, 200, 20, false);
}

/// Insert leaf in the lean curve tree, check that proof verifies (only verify for certain no of leaves) and once all leaves
/// are added, the root should be same as root of the vanilla curve tree (created using `from_leaves`)
pub fn check_inserts<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    height: u8,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
    compare_with_vanilla_curve_tree: bool,
) {
    let mut rng = rand::thread_rng();
    // let mut rng = StdRng::seed_from_u64(0);
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let leaves = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeSet::new();
    while proof_indices.len() < num_proofs {
        proof_indices.insert(possible_proof_indices.choose(&mut rng).unwrap());
    }

    let vanilla_curve_tree = compare_with_vanilla_curve_tree
        .then(|| CurveTree::<L, 1, P0, P1>::from_leaves(&leaves, &sr_params, None));

    let mut lean_curve_tree = LeanCurveTree::<L, P0, P1>::new(height, &sr_params);
    assert_eq!(lean_curve_tree.height, height);
    assert_eq!(
        lean_curve_tree.odd_level_default_nodes.len()
            + lean_curve_tree.even_level_default_nodes.len(),
        height as usize
    );
    assert_eq!(lean_curve_tree.next_leaf_index, 0);

    // The root should be equal to the correct default node for an empty tree
    if height % 2 == 1 {
        match lean_curve_tree.root_node() {
            Root::Odd(n) => {
                let default = lean_curve_tree.odd_level_default_nodes.last().unwrap();
                assert_eq!(n.commitments[0], default.commitment);
                for i in 0..L {
                    assert_eq!(n.x_coord_children[0][i], default.x_coord);
                }
            }
            _ => panic!("Expected odd root but found even"),
        }
    } else {
        match lean_curve_tree.root_node() {
            Root::Even(n) => {
                let default = lean_curve_tree.even_level_default_nodes.last().unwrap();
                assert_eq!(n.commitments[0], default.commitment);
                for i in 0..L {
                    assert_eq!(n.x_coord_children[0][i], default.x_coord);
                }
            }
            _ => panic!("Expected even root but found odd"),
        }
    }

    // Insert leaves
    for i in 0..num_leaves {
        let path = lean_curve_tree.insert_and_return_path(leaves[i], &sr_params);

        assert_eq!(lean_curve_tree.next_leaf_index, i as u64 + 1);

        if proof_indices.contains(&i) {
            let root = lean_curve_tree.root_node();

            check_proof(&mut rng, leaves[i], path, &root, &sr_params)
        }
    }

    if compare_with_vanilla_curve_tree {
        let curve_tree = vanilla_curve_tree.unwrap();
        if height % 2 == 1 {
            match (curve_tree.root_node(), lean_curve_tree.root_node()) {
                (Root::Odd(n1), Root::Odd(n2)) => {
                    assert_eq!(n1.x_coord_children, n2.x_coord_children);
                    assert_eq!(n1.commitments, n2.commitments);
                }
                _ => panic!("roots odd even"),
            }
        } else {
            match (curve_tree.root_node(), lean_curve_tree.root_node()) {
                (Root::Even(n1), Root::Even(n2)) => {
                    assert_eq!(n1.x_coord_children, n2.x_coord_children);
                    assert_eq!(n1.commitments, n2.commitments);
                }
                _ => panic!("roots odd even"),
            }
        }
    }
}
