extern crate relations;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_pallas::Fq as PallasBase;
use ark_pallas::PallasConfig;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use relations::curve_tree::SelRerandParameters;
use relations::lean_curve_tree::LeanCurveTree;
use relations::partial_curve_tree::PartialCurveTree;
mod common;
use common::check_proof;

#[test]
fn insert_only() {
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(1, 11, vec![0, 1], 0, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![0, 1, 2, 3], 0, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(
        3,
        11,
        (0..8).into_iter().collect(),
        0,
        None,
    );
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(
        4,
        11,
        (0..16).into_iter().collect(),
        0,
        None,
    );
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(
        5,
        12,
        (0..32).into_iter().collect(),
        0,
        None,
    );
    check_updates::<4, PallasBase, PallasConfig, VestaConfig>(
        1,
        11,
        (0..4).into_iter().collect(),
        0,
        None,
    );
    check_updates::<4, PallasBase, PallasConfig, VestaConfig>(
        2,
        11,
        (0..16).into_iter().collect(),
        0,
        None,
    );
    check_updates::<4, PallasBase, PallasConfig, VestaConfig>(
        3,
        11,
        (0..64).into_iter().collect(),
        0,
        None,
    );
}

#[test]
fn insert_and_update_small() {
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(1, 11, vec![0], 1, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![0], 1, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![0], 2, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![1], 1, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![1], 2, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![0, 1], 2, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![1, 2], 1, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(3, 11, vec![1, 4], 2, Some(2));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(3, 11, vec![3, 5], 2, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(3, 11, vec![2, 4], 2, Some(1));
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(4, 11, vec![1, 3, 5, 9], 4, None);
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(
        4,
        11,
        vec![1, 3, 5, 7, 9, 11],
        2,
        None,
    );
    check_updates::<2, PallasBase, PallasConfig, VestaConfig>(
        4,
        11,
        vec![2, 4, 6, 8, 10, 12],
        2,
        None,
    );
    check_updates::<4, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![4, 8, 9], 2, Some(0));
    check_updates::<4, PallasBase, PallasConfig, VestaConfig>(2, 11, vec![0, 1, 2], 11, Some(3));
}

#[test]
fn insert_and_update_large() {
    check_updates::<256, PallasBase, PallasConfig, VestaConfig>(
        2,
        13,
        vec![256, 512, 513, 2048],
        100,
        None,
    );
    check_updates::<256, PallasBase, PallasConfig, VestaConfig>(
        3,
        13,
        vec![256, 512, 513, 2048],
        100,
        None,
    );
}

/// Insert some leaves including the ones in `leaf_indices_to_track`. The indices in `leaf_indices_to_track` are tracked and their
/// parents are never removed from the tree. Other leaves inserted in the tree (not part of `leaf_indices_to_track`) are added
/// but their parents can be removed when `clear_full_nodes` is called.
/// `num_updates_after_last_tracked_leaf` are the number of leaves to insert after the largest index of `leaf_indices_to_track` is inserted.
/// `nodes_removed_during_clear` are the expected number of full nodes that will be removed which are not on the path of the leaves being tracked.
pub fn check_updates<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    height: u8,
    generators_length_log_2: usize,
    mut leaf_indices_to_track: Vec<u64>,
    num_updates_after_last_tracked_leaf: u64,
    nodes_removed_during_clear: Option<u64>,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    leaf_indices_to_track.sort();

    let num_leaves =
        (leaf_indices_to_track.last().unwrap() + 1 + num_updates_after_last_tracked_leaf) as usize;
    let leaves = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();

    let mut lean_curve_tree = LeanCurveTree::<L, P0, P1>::new(height, &sr_params);

    let mut partial_curve_tree = PartialCurveTree::<L, P0, P1>::new(height, &sr_params).unwrap();

    // Leaves inserted in partial tree
    let mut leaves_inserted = 0;
    for i in 0..num_leaves {
        lean_curve_tree.insert(leaves[i], &sr_params);
        if leaf_indices_to_track.len() > leaves_inserted
            && leaf_indices_to_track[leaves_inserted] == i as u64
        {
            if leaves_inserted != 0 {
                // Last inserted leaf in partial tree
                let leaf_index_to_prove = leaf_indices_to_track[leaves_inserted - 1];
                // Update partial tree with updates happened since last insert in partial tree
                partial_curve_tree
                    .update_on_leaves(
                        leaves[(leaf_index_to_prove + 1) as usize..i].to_vec(),
                        &sr_params,
                    )
                    .unwrap();

                // Get path for previous leaf from partial tree
                let path = partial_curve_tree
                    .get_path_to_leaf(leaf_index_to_prove)
                    .unwrap();

                // Create and verify proof for the previous leaf
                let root = partial_curve_tree.root_node();
                check_proof(
                    &mut rng,
                    leaves[leaf_index_to_prove as usize],
                    path,
                    &root,
                    &sr_params,
                )
            }
            partial_curve_tree
                .insert_leaf(
                    i as u64,
                    leaves[i],
                    lean_curve_tree.odd_level_path_nodes.clone(),
                    lean_curve_tree.even_level_path_nodes.clone(),
                )
                .unwrap();
            leaves_inserted += 1;
        }
    }

    // For proving the last index in `leaf_indices_to_insert`
    let leaf_index_to_prove = *leaf_indices_to_track.last().unwrap();
    partial_curve_tree
        .update_on_leaves(
            leaves[(leaf_index_to_prove + 1) as usize..].to_vec(),
            &sr_params,
        )
        .unwrap();
    let path = partial_curve_tree
        .get_path_to_leaf(leaf_index_to_prove)
        .unwrap();
    let root = partial_curve_tree.root_node();
    check_proof(
        &mut rng,
        leaves[leaf_index_to_prove as usize],
        path,
        &root,
        &sr_params,
    );

    if let Some(expected) = nodes_removed_during_clear {
        assert_eq!(partial_curve_tree.clear_full_nodes(), expected);

        // Check all leaves still have valid proofs
        let root = partial_curve_tree.root_node();
        for i in leaf_indices_to_track {
            let path = partial_curve_tree.get_path_to_leaf(i).unwrap();
            check_proof(&mut rng, leaves[i as usize], path, &root, &sr_params)
        }
    }
}
