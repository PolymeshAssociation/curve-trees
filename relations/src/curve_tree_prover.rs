use bulletproofs::r1cs::*;

use crate::single_level_select_and_rerandomize::*;

use crate::curve_tree::{
    CurveTree, CurveTreeNode, SelRerandParameters, SelectAndRerandomizePath,
};

use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, CurveGroup};
use ark_ff::PrimeField;
use ark_std::fmt::Debug;
use ark_std::fmt::Formatter;
use ark_std::Zero;
use dock_crypto_utils::transcript::{MerlinTranscript};
use rand::Rng;
use std::ops::Mul;

impl<
        const L: usize,
        const M: usize,
        P0: SWCurveConfig + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
    > CurveTreeNode<L, M, P0, P1>
{
    /// Recursively traverse from top to bottom
    pub fn select_and_rerandomize_prover_witness(
        &self,
        index: usize,
        tree_index: usize,
        current_level_nodes: &mut Vec<WitnessNode<L, P0, P1>>,
        next_level_nodes: &mut Vec<WitnessNode<L, P1, P0>>,
    ) {
        if let Self::InnerNode(inner_node) = &self
        {
            let child_node_index_to_rerandomize = self.child_index(index).unwrap();
            let child_node_to_rerandomize = inner_node.get_child(child_node_index_to_rerandomize);
            // // x-coordinates of all children of this node, including `node_to_rerandomize`
            // let x_coord_children = x_coordinates(children, next_level_delta, tree_index);

            current_level_nodes.push(WitnessNode {
                x_coord_children: inner_node.x_coord_children[tree_index],
                child_node_to_randomize: child_node_to_rerandomize.commitment(tree_index),
            });

            // recursively add the remaining path
            child_node_to_rerandomize.select_and_rerandomize_prover_witness(
                index, tree_index, next_level_nodes, current_level_nodes
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
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > CurveTree<L, M, P0, P1>
{
    /// Produce a witness of the path (root to leaf, including the root, excluding the leaf) to the commitment at `index` including siblings.
    /// Thw witness consists of "nodes" of the path where each "node" contains x-coordinates of the children (plus delta)
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
            Self::Even(ct) => ct.select_and_rerandomize_prover_witness(
                leaf_index,
                tree_index,
                &mut even_internal_nodes,
                &mut odd_internal_nodes,
            ),
            Self::Odd(ct) => ct.select_and_rerandomize_prover_witness(
                leaf_index,
                tree_index,
                &mut odd_internal_nodes,
                &mut even_internal_nodes,
            ),
        }

        assert_eq!(
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
#[derive(Copy, Clone)]
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "CurveTreeWitness")
    }
}

/// A witness of a Curve Tree path including siblings for all nodes on the path.
/// Contains all information needed to prove the select and rerandomize relation.
#[derive(Clone, Default)]
pub struct CurveTreeWitnessPath<const L: usize, P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy>
{
    /// list of internal even nodes including the selected leaf.
    pub even_internal_nodes: Vec<WitnessNode<L, P0, P1>>,
    /// list of internal odd nodes
    pub odd_internal_nodes: Vec<WitnessNode<L, P1, P0>>,
    // the root is not explicitly represented
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
            assert!(self.even_internal_nodes.len() + 1 == self.odd_internal_nodes.len())
        };
        even
    }

    /// Commits to the root and rerandomizations of the path to the leaf specified by `index`
    /// and proves the Select and rerandomize relation for each level.
    /// Returns the rerandomized commitments on the path to (and including) the selected leaf
    /// and the rerandomization scalar of the selected leaf.
    pub fn select_and_rerandomize_prover_gadget<R: Rng>(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &SelRerandParameters<P0, P1>,
        rng: &mut R,
    ) -> (SelectAndRerandomizePath<L, P0, P1>, P0::ScalarField) {
        // for each even internal node, there must be a rerandomization of a commitment in the odd curve
        let even_length = self.even_internal_nodes.len();
        let mut odd_rerandomization_scalars: Vec<P1::ScalarField> = Vec::with_capacity(even_length);
        let mut odd_rerandomized_commitments: Vec<Affine<P1>> = Vec::with_capacity(even_length);
        // and vice versa
        let odd_length = self.odd_internal_nodes.len();
        let mut even_rerandomization_scalars: Vec<P0::ScalarField> = Vec::with_capacity(odd_length);
        let mut even_rerandomized_commitments: Vec<Affine<P0>> = Vec::with_capacity(odd_length);

        // TODO: A small (since height is small) optimization is to compute the all blindigs at once.

        // For each node on even levels in the witness path, randomize its child (on the path to leaf) by adding `B_blinding * r_1`
        for even in &self.even_internal_nodes {
            let rerandomization = F1::rand(rng);
            let blinding = parameters
                .odd_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            odd_rerandomization_scalars.push(rerandomization);
            odd_rerandomized_commitments.push((even.child_node_to_randomize + blinding).into());
        }

        let mut rerandomization_scalar_of_leaf = F0::default();
        let mut rerandomization_of_leaf = Affine::<P0>::default();
        for (i, odd) in self.odd_internal_nodes.iter().enumerate() {
            let rerandomization = F0::rand(rng);
            let blinding = parameters
                .even_parameters
                .pc_gens
                .B_blinding
                .mul(rerandomization)
                .into_affine();
            let rerandomized = (odd.child_node_to_randomize + blinding).into();
            // Since leaf is always at even level, the parent of leaf is always at odd level. If
            // current node is the last (lowest) odd level node, then its `child_node_to_randomize` is the
            // leaf node whose proof if being created.
            if i < self.odd_internal_nodes.len() - 1 {
                // Not the lowest odd level node
                even_rerandomization_scalars.push(rerandomization);
                even_rerandomized_commitments.push(rerandomized);
            } else {
                // The lowest odd level node
                even_rerandomization_scalars.push(rerandomization);
                rerandomization_scalar_of_leaf = rerandomization;
                rerandomization_of_leaf = rerandomized;
            }
        }

        let prove_even = |prover: &mut Prover<MerlinTranscript, Affine<P0>>| {
            for i in 0..even_length {
                let current_node_rerandomization = if self.root_is_even() {
                    if i == 0 {
                        // the parent is the root and thus not rerandomized
                        F0::zero()
                    } else {
                        even_rerandomization_scalars[i - 1]
                    }
                } else {
                    even_rerandomization_scalars[i]
                };
                self.even_internal_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.even_parameters,
                    &parameters.odd_parameters,
                    current_node_rerandomization,
                    odd_rerandomization_scalars[i],
                );
            }
        };

        let prove_odd = |prover: &mut Prover<MerlinTranscript, Affine<P1>>| {
            for i in 0..odd_length {
                let current_node_rerandomization = if !self.root_is_even() {
                    if i == 0 {
                        // the parent is the root and thus not rerandomized
                        F1::zero()
                    } else {
                        odd_rerandomization_scalars[i - 1]
                    }
                } else {
                    odd_rerandomization_scalars[i]
                };
                self.odd_internal_nodes[i].single_level_select_and_rerandomize_prover_gadget(
                    prover,
                    &parameters.odd_parameters,
                    &parameters.even_parameters,
                    current_node_rerandomization,
                    even_rerandomization_scalars[i],
                );
            }
        };

        // #[cfg(not(feature = "parallel"))]
        prove_even(even_prover);

        // #[cfg(not(feature = "parallel"))]
        prove_odd(odd_prover);

        // #[cfg(feature = "parallel")]
        // rayon::join(|| prove_even(even_prover), || prove_odd(odd_prover));

        (
            SelectAndRerandomizePath {
                selected_commitment: rerandomization_of_leaf,
                odd_commitments: odd_rerandomized_commitments,
                even_commitments: even_rerandomized_commitments,
            },
            rerandomization_scalar_of_leaf, // This is the scalar applied to the selected leaf for rerandomization
        )
    }
}

/// A witness of M paths in M independently generated Curve Trees including siblings for all nodes on the paths.
/// Contains all information needed to prove M batched select and rerandomize relations.
#[derive(Clone)]
pub struct CurveTreeWitnessMultiPath<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
> {
    // list of internal even nodes including the selected leaves
    pub even_internal_nodes: Vec<[WitnessNode<L, P0, P1>; M]>,
    // list of internal odd nodes
    pub odd_internal_nodes: Vec<[WitnessNode<L, P1, P0>; M]>,
}

impl<
        const L: usize,
        F: PrimeField,
        P0: SWCurveConfig<BaseField = F> + Copy,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = F> + Copy,
    > WitnessNode<L, P0, P1>
{
    /// Allocates variables for the children and proves select and rerandomize for one.
    /// If the parent is the root, the variables are allocated directly, otherwise by committing to the parent.
    pub fn single_level_select_and_rerandomize_prover_gadget(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        current_level_parameters: &SingleLayerParameters<P0>,
        child_level_parameters: &SingleLayerParameters<P1>,
        self_rerandomization_scalar: P0::ScalarField,
        child_rerandomization_scalar: P1::ScalarField,
    ) {
        let children_vars = if self_rerandomization_scalar.is_zero() {
            // In this case this (`self`) is the root and the children are treated as public input to the circuit.
            self.x_coord_children.map(constant).to_vec()
        } else {
            // TODO: We can pass the commitment directly and avoid creating again. Should be a variation of `commit_vec` like `alloc_for_commitment`.
            // The witness path doesn't need to be updated as the previous (upper) node contains commitment to next node.
            // Only randomization of the commitment is needed.

            // In this case this (`self`) is a rerandomized commitment and the children (and the scalar used for rerandomizing) are part of the witness.
            // Commit to x-coordinates of child nodes with `self_rerandomization_scalar` as the blinding
            let (_, children_vars) = prover.commit_vec(
                &self.x_coord_children,
                self_rerandomization_scalar,
                &current_level_parameters.bp_gens,
            );
            children_vars
                .iter()
                .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
                .collect()
        };
        self.single_level_select_and_rerandomize_prover_gadget_helper(
            prover,
            child_level_parameters,
            child_rerandomization_scalar,
            children_vars,
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
}
