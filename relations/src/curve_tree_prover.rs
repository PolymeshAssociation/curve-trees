use bulletproofs::r1cs::*;

use crate::error::Error;
use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizePath};

use ark_ec::{
    models::short_weierstrass::{SWCurveConfig, Projective}, short_weierstrass::Affine, CurveGroup,
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    fmt::{Debug, Formatter},
    vec::Vec,
};
use core::ops::Mul;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::Rng;
use zeroize::{Zeroize, ZeroizeOnDrop};
use crate::select::{multi_select_public_set_ext_challenge};
use ark_std::string::ToString;

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    /// Generate witness node for this node and add that witness to `current_level_witness_nodes` and
    /// then call this function for its immediate child as well. The witness is the `self`'s child on path
    /// from root to the leaf with index `leaf_index` and x-coordinates of all the children of `self`
    /// Recursively traverse from top to bottom
    pub fn generate_witness_node_for_this_and_children(
        &self,
        leaf_index: usize,
        tree_index: usize,
        current_level_witness_nodes: &mut Vec<WitnessNode<L, P0, P1>>,
        other_level_witness_nodes: &mut Vec<WitnessNode<L, P1, P0>>,
    ) {
        if let Self::InnerNode(inner_node) = &self {
            let child_node_index_to_rerandomize = self.child_index(leaf_index).unwrap();
            let child_node_to_rerandomize = inner_node.get_child(child_node_index_to_rerandomize);

            current_level_witness_nodes.push(WitnessNode {
                x_coord_children: inner_node.x_coord_children[tree_index],
                child_node_to_randomize: child_node_to_rerandomize.commitment(tree_index),
            });

            // recursively add the remaining path
            child_node_to_rerandomize.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                other_level_witness_nodes,
                current_level_witness_nodes,
            );
        }
    }
}

/// Implements prover operations on the Curve Tree
impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTree<L, M, P0, P1>
{
    /// Produce a witness of the path (root to leaf) to the commitment at `index` including siblings.
    /// The witness consists of "nodes" of the path where each "node" contains x-coordinates of the children (plus delta)
    /// and a non-hiding commitment to those x-coordinates as well.
    /// This does not randomize the commitments in the "node" but just fetches it.
    pub fn get_path_to_leaf_for_proof(
        &self,
        leaf_index: usize,
        tree_index: usize,
    ) -> CurveTreeWitnessPath<L, P0, P1> {
        let mut even_internal_nodes: Vec<WitnessNode<L, P0, P1>> = Vec::new();
        let mut odd_internal_nodes: Vec<WitnessNode<L, P1, P0>> = Vec::new();

        match self {
            Self::Even(ct) => ct.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                &mut even_internal_nodes,
                &mut odd_internal_nodes,
            ),
            Self::Odd(ct) => ct.generate_witness_node_for_this_and_children(
                leaf_index,
                tree_index,
                &mut odd_internal_nodes,
                &mut even_internal_nodes,
            ),
        }

        debug_assert_eq!(
            self.height(),
            even_internal_nodes.len() + odd_internal_nodes.len()
        );
        CurveTreeWitnessPath {
            even_internal_nodes,
            odd_internal_nodes,
        }
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        leaf_index: usize,
        tree_index: usize,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        let witness = self.get_path_to_leaf_for_proof(leaf_index, tree_index);
        witness.select_and_rerandomize_prover_gadget(even_prover, odd_prover, parameters, rng)
    }
}

/// A single node on the witness path.
/// Contains the information needed to prove the single level select and rerandomize relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct WitnessNode<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    /// x-coordinates of all children of this node, including `child_node_to_randomize`
    pub x_coord_children: [P0::ScalarField; L],
    /// The child node of this node that is on the path from root to the desired leaf.
    pub child_node_to_randomize: Affine<P1>,
}

impl<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> Debug
    for WitnessNode<L, P0, P1>
{
    // This is a dummy implementation to allow unwrapping the result of converting a vector into an array of the same size.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "CurveTreeWitness")
    }
}

/// A witness of a Curve Tree path including siblings for all nodes on the path.
/// Contains all information needed to prove the select and rerandomize relation.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct CurveTreeWitnessPath<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
{
    /// list of witnesses of generated by taking children of even level internal nodes. The children are themselves odd level nodes.
    pub even_internal_nodes: Vec<WitnessNode<L, P0, P1>>,
    /// list of witnesses of generated by taking children of odd level internal nodes. The children are themselves even level nodes.
    pub odd_internal_nodes: Vec<WitnessNode<L, P1, P0>>,
}

#[derive(Clone)]
pub enum RootChildrenCoords<F0: PrimeField, F1: PrimeField> {
    Even(Vec<LinearCombination<F0>>),
    Odd(Vec<LinearCombination<F1>>),
}

/// Prove a single inclusion using a CurveTreeWitnessPath
impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessPath<L, P0, P1>
{
    fn root_is_even(&self) -> bool {
        // The leaf is even and included in the internal even nodes.
        // If the number of internal even and odd nodes is equal,
        // then the first odd node is the parent of the first even node and a child of the even root.
        let even = self.even_internal_nodes.len() == self.odd_internal_nodes.len();
        // Otherwise there must be an additional even node which has the odd root as parent.
        if !even {
            debug_assert_eq!(
                self.even_internal_nodes.len() + 1,
                self.odd_internal_nodes.len()
            )
        };
        even
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        let (
            odd_rerandomized_nodes,
            even_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            re_randomization_of_leaf,
        ) = self.randomize_nodes(parameters, rng);

        let root_is_even = self.root_is_even();

        if root_is_even {
            self.even_internal_nodes[0].root_level_select_and_rerandomize_prover_gadget(
                even_prover,
                &parameters.odd_parameters,
                odd_rerandomization_scalars[0],
            );
        } else {
            self.odd_internal_nodes[0].root_level_select_and_rerandomize_prover_gadget(
                odd_prover,
                &parameters.even_parameters,
                even_rerandomization_scalars[0],
            );
        }

        self.select_and_rerandomize_prover_gadget_non_root_nodes(
            even_prover,
            odd_prover,
            parameters,
            root_is_even,
            &even_rerandomized_nodes,
            &odd_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
        );

        (
            SelectAndRerandomizePath {
                odd_commitments: odd_rerandomized_nodes,
                even_commitments: even_rerandomized_nodes,
            },
            re_randomization_of_leaf, // This is the scalar applied to the selected leaf for rerandomization
        )
    }

    /// Allocate x-coordinates of children of root and enforce set-membership constraint
    pub fn process_root_nodes_for_given_paths_with_common_root(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<RootChildrenCoords<F0, F1>, Error> {
        let is_root_even = paths[0].root_is_even();

        if is_root_even {
            let mut child_nodes_to_randomize = Vec::with_capacity(paths.len());
            let x_coords_root_children = paths[0].even_internal_nodes[0].x_coord_children;

            child_nodes_to_randomize.push(paths[0].even_internal_nodes[0].child_node_to_randomize + parameters.odd_parameters.delta);

            for path in &paths[1..] {
                let this_root_is_even = path.root_is_even();
                if !this_root_is_even {
                    return Err(Error::InvalidRootTypeForPath);
                }
                if x_coords_root_children != path.even_internal_nodes[0].x_coord_children {
                    return Err(Error::MismatchedXCoordsChildren);
                }
                child_nodes_to_randomize.push(path.even_internal_nodes[0].child_node_to_randomize + parameters.odd_parameters.delta);
            }

            let child_nodes_to_randomize = Projective::normalize_batch(&child_nodes_to_randomize);
            let c = even_prover.transcript().challenge_scalar(b"challenge-for-multi_select");
            let x_coords_children = child_nodes_to_randomize.iter().map(|c| {
                even_prover.allocate(Some(c.x)).unwrap().into()
            }).collect::<Vec<_>>();
            multi_select_public_set_ext_challenge(
                even_prover,
                x_coords_children.clone(),
                &x_coords_root_children,
                c
            );
            Ok(RootChildrenCoords::Even(x_coords_children))
        } else {
            let mut child_nodes_to_randomize = Vec::with_capacity(paths.len());
            let x_coords_root_children = paths[0].odd_internal_nodes[0].x_coord_children;

            child_nodes_to_randomize.push(paths[0].odd_internal_nodes[0].child_node_to_randomize + parameters.even_parameters.delta);

            for path in &paths[1..] {
                let this_root_is_even = path.root_is_even();
                if this_root_is_even {
                    return Err(Error::InvalidRootTypeForPath);
                }
                if x_coords_root_children != path.odd_internal_nodes[0].x_coord_children {
                    return Err(Error::MismatchedXCoordsChildren);
                }
                child_nodes_to_randomize.push(path.odd_internal_nodes[0].child_node_to_randomize + parameters.even_parameters.delta);
            }

            let child_nodes_to_randomize = Projective::normalize_batch(&child_nodes_to_randomize);
            let c = odd_prover.transcript().challenge_scalar(b"challenge-for-multi_select");
            let x_coords_children = child_nodes_to_randomize.iter().map(|c| {
                odd_prover.allocate(Some(c.x)).unwrap().into()
            }).collect::<Vec<_>>();
            multi_select_public_set_ext_challenge(
                odd_prover,
                x_coords_children.clone(),
                &x_coords_root_children,
                c
            );
            Ok(RootChildrenCoords::Odd(x_coords_children))
        }

    }

    /// Called after process_root_nodes_for_given_paths_with_common_root.
    /// Returns the rerandomization scalars of leaves for each path
    pub fn process_non_root_nodes_for_given_paths_with_common_root<R: Rng>(
        paths: &[Self],
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        mut root_children_coords: RootChildrenCoords<F0, F1>,
        rng: &mut R,
    ) -> Result<(Vec<SelectAndRerandomizePath<L, P0, P1>>, Vec<P0::ScalarField>), Error> {
        if paths.is_empty() {
            return Err(Error::PathsLengthMustBeGreaterThanZero);
        }
        let is_root_even = paths[0].root_is_even();

        let mut randomized_paths = Vec::with_capacity(paths.len());
        let mut scalars = Vec::with_capacity(paths.len());

        for path in paths {
            // Randomize nodes for this path
            let (
                odd_rerandomized_nodes,
                even_rerandomized_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
                re_randomization_of_leaf,
            ) = path.randomize_nodes(parameters, rng);

            // Validate root node using the batched coordinates
            match &mut root_children_coords {
                RootChildrenCoords::Even(coords) => {
                    if !is_root_even {
                        return Err(Error::RootTypeMismatch { expected: "even".to_string(), got: "odd".to_string() });
                    }
                    even_prover.transcript().append(b"rerandomized_child", &odd_rerandomized_nodes[0]);
                    let x_var = coords.remove(0);
                    let child_plus_delta = Some((path.even_internal_nodes[0].child_node_to_randomize + parameters.odd_parameters.delta).into_affine());
                    validate_point_and_re_randomize(
                        even_prover,
                        &parameters.odd_parameters,
                        &odd_rerandomized_nodes[0],
                        x_var,
                        child_plus_delta,
                        Some(odd_rerandomization_scalars[0]),
                    );
                }
                RootChildrenCoords::Odd(coords) => {
                    if is_root_even {
                        return Err(Error::RootTypeMismatch { expected: "odd".to_string(), got: "even".to_string() });
                    }
                    odd_prover.transcript().append(b"rerandomized_child", &even_rerandomized_nodes[0]);
                    let x_var = coords.remove(0);
                    let child_plus_delta = Some((path.odd_internal_nodes[0].child_node_to_randomize + parameters.even_parameters.delta).into_affine());
                    validate_point_and_re_randomize(
                        odd_prover,
                        &parameters.even_parameters,
                        &even_rerandomized_nodes[0],
                        x_var,
                        child_plus_delta,
                        Some(even_rerandomization_scalars[0]),
                    );
                }
            }

            // Process non-root nodes
            path.select_and_rerandomize_prover_gadget_non_root_nodes(
                even_prover,
                odd_prover,
                parameters,
                is_root_even,
                &even_rerandomized_nodes,
                &odd_rerandomized_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
            );

            randomized_paths.push(SelectAndRerandomizePath {
                odd_commitments: odd_rerandomized_nodes,
                even_commitments: even_rerandomized_nodes,
            });
            scalars.push(re_randomization_of_leaf);
        }

        Ok((randomized_paths, scalars))
    }

    /// Randomizes the nodes in the witness path and returns the randomized nodes and scalars.
    /// Returns: (odd_rerandomized_nodes, even_rerandomized_nodes, even_rerandomization_scalars, odd_rerandomization_scalars, re_randomization_of_leaf)
    fn randomize_nodes<R: Rng>(
        &self,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (
        Vec<Affine<P1>>,
        Vec<Affine<P0>>,
        Vec<P0::ScalarField>,
        Vec<P1::ScalarField>,
        P0::ScalarField,
    ) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_nodes: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_nodes: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        // TODO: A small (since height is small) optimization is to compute the all blindings at once.

        // For each node on even levels in the witness path, randomize its child (odd level node) by adding `B_blinding * r_1`
        for even in &self.even_internal_nodes {
            let rerandomization = F1::rand(rng);
            let blinding = parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            odd_rerandomization_scalars.push(rerandomization);
            odd_rerandomized_nodes.push((even.child_node_to_randomize + blinding).into());
        }

        let mut re_randomization_of_leaf = F0::default();
        for (i, odd) in self.odd_internal_nodes.iter().enumerate() {
            let rerandomization = F0::rand(rng);
            let blinding = parameters
                .even_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            let rerandomized = (odd.child_node_to_randomize + blinding).into();
            even_rerandomization_scalars.push(rerandomization);
            // Since leaf is always at even level, the parent of leaf is always at odd level. If
            // current node is the last (lowest) odd level node, then its `child_node_to_randomize` is the
            // leaf node whose proof if being created.
            even_rerandomized_nodes.push(rerandomized);
            if i == self.odd_internal_nodes.len() - 1 {
                // The lowest odd level node
                re_randomization_of_leaf = rerandomization;
            }
        }

        (
            odd_rerandomized_nodes,
            even_rerandomized_nodes,
            even_rerandomization_scalars,
            odd_rerandomization_scalars,
            re_randomization_of_leaf,
        )
    }

    /// Proves select and rerandomize for all non-root nodes in the witness path.
    fn select_and_rerandomize_prover_gadget_non_root_nodes(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        root_is_even: bool,
        even_rerandomized_nodes: &[Affine<P0>],
        odd_rerandomized_nodes: &[Affine<P1>],
        mut even_rerandomization_scalars: Vec<P0::ScalarField>,
        mut odd_rerandomization_scalars: Vec<P1::ScalarField>,
    ) {
        let even_length = self.even_internal_nodes.len();
        let odd_length = self.odd_internal_nodes.len();

        let prove_even = |prover: &mut Prover<MerlinTranscript, Affine<P0>>| {
            for i in 0..even_length {
                let index = if root_is_even {i+1} else {i};
                if self.even_internal_nodes.len() == index {
                    continue;
                }
                self.even_internal_nodes[index].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.odd_parameters,
                    &even_rerandomized_nodes[i],
                    even_rerandomization_scalars[i],
                    odd_rerandomization_scalars[index],
                );
            }
        };

        let prove_odd = |prover: &mut Prover<MerlinTranscript, Affine<P1>>| {
            for i in 0..odd_length {
                let index = if !root_is_even {i+1} else {i};
                if self.odd_internal_nodes.len() == index {
                    continue;
                }
                self.odd_internal_nodes[index].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.even_parameters,
                    &odd_rerandomized_nodes[i],
                    odd_rerandomization_scalars[i],
                    even_rerandomization_scalars[index],
                );
            }
        };

        #[cfg(not(feature = "parallel"))]
        prove_even(even_prover);

        #[cfg(not(feature = "parallel"))]
        prove_odd(odd_prover);

        #[cfg(feature = "parallel")]
        rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        Zeroize::zeroize(&mut odd_rerandomization_scalars);
        Zeroize::zeroize(&mut even_rerandomization_scalars);
    }
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > WitnessNode<L, P0, P1>
{
    /// Allocates variables for the children and proves select and rerandomize for one.
    /// If the parent is the root, the variables are allocated directly, otherwise by allocating commitment to the parent.
    pub fn single_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        child_level_parameters: &SingleLayerParameters<P1>,
        self_node_rerandomized: &Affine<P0>,
        self_rerandomization_scalar: P0::ScalarField,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        // In this case this (`self`) is a non-root inner node and the children (and the scalar used for rerandomizing) are part of the witness.
        // Allocate variables for x-coordinates (which are committed in `self_node_rerandomized`) of child nodes with `self_rerandomization_scalar` as the blinding
        let children = prover.vars_for_committed_vec(
            self_node_rerandomized,
            &self.x_coord_children,
            self_rerandomization_scalar,
        ).iter()
            .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
            .collect();
        self.single_level_select_and_rerandomize_prover_gadget_helper(
            prover,
            child_level_parameters,
            child_rerandomization_scalar,
            children,
        );
    }

    pub fn root_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        child_level_parameters: &SingleLayerParameters<P1>,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        self.root_level_select_and_rerandomize_prover_gadget_helper(
            prover,
            child_level_parameters,
            child_rerandomization_scalar,
            &self.x_coord_children,
        );
    }

    /// Proves the select and rerandomize for one of the children represented by the variables.
    pub fn single_level_select_and_rerandomize_prover_gadget_helper(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parameters: &SingleLayerParameters<P1>,
        child_rerandomization_scalar: P1::ScalarField,
        all_children_vars: Vec<LinearCombination<<P0>::ScalarField>>,
    ) {
        // Randomize the child node
        let child_commitment = self.child_node_to_randomize;
        let blinding = parameters.pc_gens.B_blinding * child_rerandomization_scalar;
        let rerandomized_child = child_commitment + blinding.into_affine();

        single_level_select_and_rerandomize(
            prover,
            parameters,
            &rerandomized_child.into(),
            all_children_vars,
            Some((child_commitment + parameters.delta).into_affine()),
            Some(child_rerandomization_scalar),
        );
    }

    /// Proves the select and rerandomize for one of the children represented by the variables.
    pub fn root_level_select_and_rerandomize_prover_gadget_helper(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        parameters: &SingleLayerParameters<P1>,
        child_rerandomization_scalar: P1::ScalarField,
        children_of_root: &[P0::ScalarField],
    ) {
        // Randomize the child node
        let child_commitment = self.child_node_to_randomize;
        let blinding = parameters.pc_gens.B_blinding * child_rerandomization_scalar;
        let rerandomized_child = child_commitment + blinding.into_affine();

        root_level_select_and_rerandomize(
            prover,
            parameters,
            &rerandomized_child.into(),
            children_of_root,
            Some((child_commitment + parameters.delta).into_affine()),
            Some(child_rerandomization_scalar),
        );
    }
}
