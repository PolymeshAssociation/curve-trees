use crate::batched_curve_tree_prover::{
    CurveTreeWitnessMultiPath, RootChildrenForMultiPath, WitnessMultiPathForSameRoot,
};
use crate::curve::{checked_curve_addition_helper, curve_check, PointRepresentation};
use crate::curve_tree::{
    SelectAndRerandomizeMultiPath, SelectAndRerandomizeMultiPathWithDivisorComms,
};
use crate::curve_tree_prover::WitnessNode;
use crate::error::{Error, Result};
use crate::prover::{constraints_for_dlogs_presummed, create_and_commit_divisor, DlogItem};
use crate::select::{multi_select_public_set, select, select_public_set};
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms, PointWithDlog};

use crate::parameters::{SelRerandProofParametersRef, SingleLayerProofParametersNew};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::{PrimeField, Zero};
use ark_std::marker::PhantomData;
use ark_std::vec;
use ark_std::{boxed::Box, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, Variable};
use bulletproofs::BulletproofGens;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
        P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessMultiPath<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize prover gadget.
    /// Returns path commitments, leaf rerandomizations, and divisor commitments for root, non-root levels, and leaves.
    pub fn batched_select_and_rerandomize_prover_gadget_new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        rng: &mut R,
    ) -> Result<(
        SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>,
        Vec<P0::ScalarField>,
    )> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_indices = self.num_indices();
        if num_indices > M as u32 {
            return Err(Error::MoreIndicesThanSupportedBatchSize(
                self.num_indices(),
                M as u32,
            ));
        }

        let (
            even_rerandomized_sum_of_nodes,
            odd_rerandomized_sum_of_nodes,
            mut even_rerandomization_scalars,
            mut odd_rerandomization_scalars,
            rerandomizations_of_selected,
            rerandomization_scalars_of_selected,
        ) = self.randomize_nodes((even_parameters.pc_gens(), odd_parameters.pc_gens()), rng);

        let root_is_even = self.root_is_even();
        let height = self.even_internal_nodes.len() + self.odd_internal_nodes.len();

        let mut even_node_divisors = Vec::new();
        let mut even_node_comms = Vec::new();
        let mut odd_node_divisors = Vec::new();
        let mut odd_node_comms = Vec::new();

        // A height 1 tree's root is itself the parent of the leaves. The loop below selects each
        // leaf from the public root x-coords, so there is no level to sum at height 1.
        if height > 1 {
            if root_is_even {
                let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                    Self::create_and_commit_divisor_for_root::<_, Parameters0>(
                        rng,
                        even_prover,
                        num_indices,
                        &self.even_internal_nodes[0],
                        odd_rerandomized_sum_of_nodes[0],
                        odd_rerandomization_scalars[0],
                        odd_parameters,
                        &even_parameters.sl_params.bp_gens,
                    )?;
                even_node_comms.push(divisor_comms);
                even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            } else {
                let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                    CurveTreeWitnessMultiPath::<L, M, P1, P0>::create_and_commit_divisor_for_root::<
                        _,
                        Parameters1,
                    >(
                        rng,
                        odd_prover,
                        num_indices,
                        &self.odd_internal_nodes[0],
                        even_rerandomized_sum_of_nodes[0],
                        even_rerandomization_scalars[0],
                        even_parameters,
                        &odd_parameters.sl_params.bp_gens,
                    )?;
                odd_node_comms.push(divisor_comms);
                odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            }
        }

        // Process the non-root levels and the leaf level for this multi-path.
        let (
            nr_even_comms,
            nr_even_divisors,
            nr_odd_comms,
            nr_odd_summed_divisors,
            odd_leaf_divisors,
        ) = self.process_non_root_nodes::<_, Parameters0, Parameters1>(
            rng,
            even_prover,
            odd_prover,
            parameters,
            num_indices,
            root_is_even,
            &even_rerandomized_sum_of_nodes,
            &odd_rerandomized_sum_of_nodes,
            &even_rerandomization_scalars,
            &odd_rerandomization_scalars,
            &rerandomizations_of_selected,
            &rerandomization_scalars_of_selected,
        )?;
        even_node_comms.extend(nr_even_comms);
        even_node_divisors.extend(nr_even_divisors);
        odd_node_comms.extend(nr_odd_comms);
        odd_node_divisors.extend(nr_odd_summed_divisors);

        constraints_for_dlogs_presummed::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_prover,
            odd_prover,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
            odd_leaf_divisors,
        )?;

        Zeroize::zeroize(&mut odd_rerandomization_scalars);
        Zeroize::zeroize(&mut even_rerandomization_scalars);

        Ok((
            SelectAndRerandomizeMultiPathWithDivisorComms {
                path: SelectAndRerandomizeMultiPath {
                    even_commitments: even_rerandomized_sum_of_nodes,
                    odd_commitments: odd_rerandomized_sum_of_nodes,
                    selected_commitments: rerandomizations_of_selected,
                },
                even_divisor_comms: even_node_comms,
                odd_divisor_comms: odd_node_comms,
            },
            rerandomization_scalars_of_selected,
        ))
    }

    /// Process the non-root nodes of a single multi-path, producing
    /// the per-level divisor commitments and dlog items for each parity. The root is assumed to
    /// be already processed by the caller.
    fn process_non_root_nodes<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        num_indices: u32,
        root_is_even: bool,
        even_rerandomized_sum_of_nodes: &[Affine<P0>],
        odd_rerandomized_sum_of_nodes: &[Affine<P1>],
        even_rerandomization_scalars: &[F0],
        odd_rerandomization_scalars: &[F1],
        rerandomizations_of_selected: &[Affine<P0>],
        rerandomization_scalars_of_selected: &[F0],
    ) -> Result<(
        Vec<DivisorComms<Affine<P0>>>,
        Vec<DlogItem<F0, Parameters0>>,
        Vec<DivisorComms<Affine<P1>>>,
        Vec<DlogItem<F1, Parameters1>>,
        Vec<DlogItem<F1, Parameters1>>,
    )> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let mut even_node_comms = Vec::new();
        let mut even_node_divisors = Vec::new();
        let mut odd_node_comms = Vec::new();
        let mut odd_node_divisors = Vec::new();
        // Leaf dlog items are kept separate from the summed (root/non-root) items: leaves are not
        // sums of curve-checked points, so they keep their on-curve check (see constraints_for_dlogs_presummed).
        let mut odd_leaf_divisors = Vec::new();

        // Process even non-root nodes
        for i in 0..self.even_internal_nodes.len() {
            let index = if root_is_even { i + 1 } else { i };
            if self.even_internal_nodes.len() == index {
                continue;
            }

            let (sum_x_var, sum_y_var, x, y, divisor_comms, p) =
                Self::select_and_commit_divisor_for_non_root::<_, Parameters0>(
                    rng,
                    even_prover,
                    num_indices,
                    &self.even_internal_nodes[index],
                    odd_rerandomized_sum_of_nodes[index],
                    odd_rerandomization_scalars[index],
                    &even_rerandomized_sum_of_nodes[i],
                    even_rerandomization_scalars[i],
                    odd_parameters,
                    &even_parameters.sl_params.bp_gens,
                )?;
            even_node_comms.push(divisor_comms);
            even_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
        }

        // Process odd non-root nodes (except last level which has leaves)
        for i in 0..self.odd_internal_nodes.len() {
            let index = if !root_is_even { i + 1 } else { i };
            if self.odd_internal_nodes.len() == index {
                continue;
            }

            if index < (self.odd_internal_nodes.len() - 1) {
                let (sum_x_var, sum_y_var, x, y, divisor_comms, p) = CurveTreeWitnessMultiPath::<L, M, P1, P0>::select_and_commit_divisor_for_non_root::<_, Parameters1>(
                    rng,
                    odd_prover,
                    num_indices,
                    &self.odd_internal_nodes[index],
                    even_rerandomized_sum_of_nodes[index],
                    even_rerandomization_scalars[index],
                    &odd_rerandomized_sum_of_nodes[i],
                        odd_rerandomization_scalars[i],
                    even_parameters,
                    &odd_parameters.sl_params.bp_gens,
                )?;
                odd_node_comms.push(divisor_comms);
                odd_node_divisors.push((sum_x_var, sum_y_var, x, y, p));
            }
        }

        // Process leaf level - for each leaf, membership check and individual divisor proofs
        {
            let last_odd_index = self.odd_internal_nodes.len() - 1;
            let nodes = &self.odd_internal_nodes[last_odd_index];

            // Parent info for allocating variables
            let parent_index = if !root_is_even && last_odd_index > 0 {
                last_odd_index - 1
            } else {
                last_odd_index
            };
            let parent_scalar = if parent_index < odd_rerandomization_scalars.len() {
                odd_rerandomization_scalars[parent_index]
            } else {
                F1::zero()
            };

            // Gather the children x-coords. At height 1 the leaf's parent is the public root, so its
            // children are always public, otherwise they are committed in the parent's commitment
            // and selected as committed variables.
            let parent_is_root = parent_scalar.is_zero();
            let mut children_x_coords: Vec<F1> = Vec::with_capacity(L * num_indices as usize);
            for node in nodes {
                children_x_coords.extend_from_slice(node.x_coord_children.as_slice());
            }

            let committed_children: Vec<LinearCombination<F1>> = if parent_is_root {
                Vec::new()
            } else {
                let parent_node = &odd_rerandomized_sum_of_nodes[parent_index];
                odd_prover
                    .vars_for_committed_vec(parent_node, &children_x_coords, parent_scalar)
                    .iter()
                    .map(|v| (*v).into())
                    .collect()
            };

            // Split into chunks for each index
            let chunk_size = children_x_coords.len() / num_indices as usize;

            for i in 0..num_indices as usize {
                // leaf node point + delta
                let child_plus_delta = (nodes[i].child_node_to_randomize
                    + even_parameters.sl_params.delta)
                    .into_affine();

                // Allocate x, y variables for leaf on odd prover as leaf is always even
                let (x_var, y_var) = allocate_leaf_coords(odd_prover, child_plus_delta);

                if parent_is_root {
                    select_public_set(
                        odd_prover,
                        x_var.into(),
                        &children_x_coords[i * chunk_size..(i + 1) * chunk_size],
                    )?;
                } else {
                    select(
                        odd_prover,
                        x_var.into(),
                        committed_children[i * chunk_size..(i + 1) * chunk_size]
                            .iter()
                            .cloned(),
                    )?;
                }

                // Add transcript entry for rerandomized leaf
                odd_prover
                    .transcript()
                    .append(b"rerandomized_child", &rerandomizations_of_selected[i]);

                let rerandomized_plus_delta = (rerandomizations_of_selected[i]
                    + even_parameters.sl_params.delta)
                    .into_affine();
                let (x, y) = rerandomized_plus_delta
                    .xy()
                    .ok_or_else(|| Error::PointCantBeZero)?;

                let (divisor_comms, p) = create_and_commit_divisor::<_, F1, F0, P1, P0, Parameters1>(
                    rng,
                    odd_prover,
                    rerandomization_scalars_of_selected[i],
                    &even_parameters.table_b_blinding,
                    &odd_parameters.sl_params.bp_gens,
                )?;

                odd_node_comms.push(divisor_comms);
                odd_leaf_divisors.push((x_var.into(), y_var.into(), x, y, p));
            }
        }

        Ok((
            even_node_comms,
            even_node_divisors,
            odd_node_comms,
            odd_node_divisors,
            odd_leaf_divisors,
        ))
    }

    fn create_and_commit_divisor_for_root<R: CryptoRngCore, Parameters0: DiscreteLogParameters>(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        num_indices: u32,
        witness_nodes: &[WitnessNode<L, P0, P1>], // 1 for each root in the batch
        re_randomized_sum_of_children: Affine<P1>,
        child_re_randomization: F1,
        parameters: &SingleLayerProofParametersNew<P1, Parameters0>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        LinearCombination<F0>,
        LinearCombination<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters0>>,
    )> {
        // x-coordinates of all children of all the roots
        let mut all_children_x = Vec::with_capacity(L * num_indices as usize);
        let mut selected_children_plus_delta = Vec::with_capacity(num_indices as usize);

        for i in 0..num_indices as usize {
            all_children_x.extend_from_slice(witness_nodes[i].x_coord_children.as_slice());
            selected_children_plus_delta.push(
                (witness_nodes[i].child_node_to_randomize + parameters.sl_params.delta)
                    .into_affine(),
            );
        }

        // Do membership check on root's children's x-coords and get the sum of selected children
        let (sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F0, P1, _>(
            prover,
            num_indices,
            &all_children_x,
            Some(&selected_children_plus_delta),
        )?;

        // Compute the target point for discrete log verification
        let shifted_rerandomized = (re_randomized_sum_of_children
            + (parameters.sl_params.delta * P1::ScalarField::from(num_indices as u64)))
        .into_affine();
        let (x, y) = shifted_rerandomized
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        // Create single divisor proof for the sum
        let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters0>(
            rng,
            prover,
            child_re_randomization,
            &parameters.table_b_blinding,
            bp_gens,
        )?;
        Ok((sum_x_var, sum_y_var, x, y, divisor_comms, p))
    }

    fn select_and_commit_divisor_for_non_root<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
    >(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        num_indices: u32,
        witness_nodes: &[WitnessNode<L, P0, P1>],
        re_randomized_sum_of_children: Affine<P1>,
        child_re_randomization: F1,
        parent_node: &Affine<P0>,
        parent_rerandomization_scalar: F0,
        parameters: &SingleLayerProofParametersNew<P1, Parameters0>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        LinearCombination<F0>,
        LinearCombination<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters0>>,
    )> {
        let children_vars = WitnessNode::allocate_multi_node_variables(
            witness_nodes,
            prover,
            parent_node,
            parent_rerandomization_scalar,
        );

        let mut selected_children_plus_delta = vec![Projective::<P1>::zero(); num_indices as usize];
        for j in 0..num_indices as usize {
            selected_children_plus_delta[j] =
                witness_nodes[j].child_node_to_randomize + parameters.sl_params.delta;
        }
        let selected_children_plus_delta =
            Projective::normalize_batch(&selected_children_plus_delta);

        let (sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root(
            prover,
            num_indices,
            children_vars,
            Some(&selected_children_plus_delta),
        )?;

        let shifted_rerandomized = (re_randomized_sum_of_children
            + (parameters.sl_params.delta * P1::ScalarField::from(num_indices)))
        .into_affine();
        let (x, y) = shifted_rerandomized
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;

        let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters0>(
            rng,
            prover,
            child_re_randomization,
            &parameters.table_b_blinding,
            bp_gens,
        )?;
        Ok((sum_x_var, sum_y_var, x, y, divisor_comms, p))
    }

    /// Process the shared root of several multi-paths at once. Each multi-path's selected
    /// children of the root are proven members of the root's public x-coords with a single
    /// multi-select per root (across all multi-paths), then each multi-path's children
    /// are summed up and a divisor is created for each
    fn process_shared_root_for_multi_paths<R: CryptoRngCore, Parameters: DiscreteLogParameters>(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        root_x_coords: &[[F0; L]],
        selected_children_per_mp: &[Vec<Affine<P1>>],
        rerandomized_sums: &[Affine<P1>],
        rerandomization_scalars: &[F1],
        parameters: &SingleLayerProofParametersNew<P1, Parameters>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(Vec<DivisorComms<Affine<P0>>>, Vec<DlogItem<F0, Parameters>>)> {
        let num_multi_paths = selected_children_per_mp.len();
        let delta = parameters.sl_params.delta;
        // maximum number of leaves in any multi-path
        let max_leaves_mp = selected_children_per_mp
            .iter()
            .map(|c| c.len())
            .max()
            .unwrap_or(0);

        let children_plus_delta_per_mp: Vec<Vec<Affine<P1>>> = selected_children_per_mp
            .iter()
            .map(|children| {
                let proj: Vec<Projective<P1>> = children.iter().map(|c| *c + delta).collect();
                Projective::normalize_batch(&proj)
            })
            .collect();

        // Membership check per root. Collect the child x-vars per root and then do its membership
        // check. This means there are at most M (multi-set) checks regardless of the total number
        // of children
        let mut x_vars_per_mp: Vec<Vec<LinearCombination<F0>>> = vec![Vec::new(); num_multi_paths];
        for root_idx in 0..max_leaves_mp {
            let mut xs = Vec::new();
            // for each multi-path, take its child corresponding to `root_idx`-th root
            for (mp_idx, children) in children_plus_delta_per_mp.iter().enumerate() {
                if let Some(child) = children.get(root_idx) {
                    let x_lc: LinearCombination<F0> =
                        prover.allocate(Some(child.x)).unwrap().into();
                    xs.push(x_lc.clone());
                    x_vars_per_mp[mp_idx].push(x_lc);
                }
            }
            multi_select_public_set(prover, xs.clone(), &root_x_coords[root_idx])?;
        }

        // Per multi-path - sum its selected children and commit a divisor for the rerandomized sum.
        let mut comms = Vec::with_capacity(num_multi_paths);
        let mut divisors = Vec::with_capacity(num_multi_paths);
        for mp_idx in 0..num_multi_paths {
            let (sum_x, sum_y) = accumulate_selected_children(
                prover,
                &x_vars_per_mp[mp_idx],
                Some(&children_plus_delta_per_mp[mp_idx]),
            )?;
            let num_idx = children_plus_delta_per_mp[mp_idx].len() as u64;
            let shifted = (rerandomized_sums[mp_idx] + (delta * P1::ScalarField::from(num_idx)))
                .into_affine();
            let (x, y) = shifted.xy().ok_or(Error::PointCantBeZero)?;
            let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters>(
                rng,
                prover,
                rerandomization_scalars[mp_idx],
                &parameters.table_b_blinding,
                bp_gens,
            )?;
            comms.push(divisor_comms);
            divisors.push((sum_x, sum_y, x, y, p));
        }
        Ok((comms, divisors))
    }
}

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
        P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    > WitnessMultiPathForSameRoot<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize prover gadget for several batched multi-paths
    /// that share a common root. The root is processed once and the non-root levels and leaves
    /// are processed per multi-path. Returns the per multi-path randomized nodes and divisor
    /// commitments, and the per multi-path leaf rerandomization scalars.
    pub fn batched_select_and_rerandomize_prover_gadget_new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        rng: &mut R,
    ) -> Result<(
        Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>>,
        Vec<Vec<P0::ScalarField>>, // leaf rerandomization scalars
    )> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let multi_paths = self.to_individual_multi_paths();
        if multi_paths.is_empty() {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }
        let num_multi_paths = multi_paths.len();
        let root_is_even = multi_paths[0].root_is_even();
        let height =
            multi_paths[0].even_internal_nodes.len() + multi_paths[0].odd_internal_nodes.len();

        // All multi-paths must share the same root parity and respect the batch size.
        for p in &multi_paths {
            if p.root_is_even() != root_is_even {
                return Err(Error::RootTypeMismatch {
                    expected: if root_is_even { "even" } else { "odd" }.to_string(),
                    got: if root_is_even { "odd" } else { "even" }.to_string(),
                });
            }
            if p.num_indices() > M as u32 {
                return Err(Error::MoreIndicesThanSupportedBatchSize(
                    p.num_indices(),
                    M as u32,
                ));
            }
        }

        // Randomize the nodes of every multi-path.
        let mut all_even_sum = Vec::with_capacity(num_multi_paths);
        let mut all_odd_sum = Vec::with_capacity(num_multi_paths);
        let mut all_even_scalars = Vec::with_capacity(num_multi_paths);
        let mut all_odd_scalars = Vec::with_capacity(num_multi_paths);
        let mut all_rerand_leaves = Vec::with_capacity(num_multi_paths);
        let mut all_rerand_leaves_scalars = Vec::with_capacity(num_multi_paths);
        for p in &multi_paths {
            let (even_sum, odd_sum, even_scalars, odd_scalars, rerand_leaves, leaves_scalars) =
                p.randomize_nodes((even_parameters.pc_gens(), odd_parameters.pc_gens()), rng);
            all_even_sum.push(even_sum);
            all_odd_sum.push(odd_sum);
            all_even_scalars.push(even_scalars);
            all_odd_scalars.push(odd_scalars);
            all_rerand_leaves.push(rerand_leaves);
            all_rerand_leaves_scalars.push(leaves_scalars);
        }

        // Per multi-path divisors flattened, in multi-path order.
        let mut even_node_comms: Vec<Vec<DivisorComms<Affine<P0>>>> =
            vec![Vec::new(); num_multi_paths];
        let mut even_node_divisors: Vec<Vec<DlogItem<F0, Parameters0>>> =
            vec![Vec::new(); num_multi_paths];
        let mut odd_node_comms: Vec<Vec<DivisorComms<Affine<P1>>>> =
            vec![Vec::new(); num_multi_paths];
        let mut odd_node_divisors: Vec<Vec<DlogItem<F1, Parameters1>>> =
            vec![Vec::new(); num_multi_paths];
        // For leaf per multi-path, kept separate from the summed items
        let mut leaf_divisors: Vec<Vec<DlogItem<F1, Parameters1>>> =
            vec![Vec::new(); num_multi_paths];

        if height == 1 {
            // The shared root is itself the parent of the leaves. Membership of every multi-path's
            // leaves is combined and each leaf then gets its own divisor. The root is always odd at height 1.
            let root_x_coords = match &self.root_children {
                RootChildrenForMultiPath::Odd { x_coords, .. } => x_coords,
                RootChildrenForMultiPath::Even { .. } => {
                    return Err(Error::MalformedProofInput(
                        "height-1 tree must have an odd root".to_string(),
                    ))
                }
            };
            let even_delta = even_parameters.sl_params.delta;

            let leaves_plus_delta_per_mp: Vec<Vec<Affine<P0>>> = multi_paths
                .iter()
                .map(|p| {
                    let proj = p.odd_internal_nodes[0]
                        .iter()
                        .map(|n| n.child_node_to_randomize + even_delta)
                        .collect::<Vec<_>>();
                    Projective::normalize_batch(&proj)
                })
                .collect();
            // maximum number of leaves in any multi-path
            let max_leaves_mp = leaves_plus_delta_per_mp
                .iter()
                .map(|c| c.len())
                .max()
                .unwrap_or(0);

            // Membership check per root. Collect the leaf x-vars per root and then do its membership
            // check. This means there are at most M (multi-set) checks regardless of the total number
            // of leaves
            let mut leaf_x_vars_per_mp: Vec<Vec<LinearCombination<F1>>> =
                vec![Vec::new(); num_multi_paths];
            for root_idx in 0..max_leaves_mp {
                let mut xs = Vec::new();
                // for each multi-path, take its leaf corresponding to `root_idx`-th root
                for (mp_idx, leaves) in leaves_plus_delta_per_mp.iter().enumerate() {
                    if let Some(leaf) = leaves.get(root_idx) {
                        let x_lc: LinearCombination<F1> =
                            odd_prover.allocate(Some(leaf.x)).unwrap().into();
                        xs.push(x_lc.clone());
                        leaf_x_vars_per_mp[mp_idx].push(x_lc);
                    }
                }
                multi_select_public_set(odd_prover, xs, &root_x_coords[root_idx])?;
            }

            // Per leaf - allocate y coordinate, create and commit its divisor.
            for mp_idx in 0..num_multi_paths {
                for root_idx in 0..leaves_plus_delta_per_mp[mp_idx].len() {
                    let leaf_plus_delta = leaves_plus_delta_per_mp[mp_idx][root_idx];
                    let y_var: LinearCombination<F1> =
                        odd_prover.allocate(Some(leaf_plus_delta.y)).unwrap().into();
                    odd_prover
                        .transcript()
                        .append(b"rerandomized_child", &all_rerand_leaves[mp_idx][root_idx]);
                    let rerandomized_plus_delta =
                        (all_rerand_leaves[mp_idx][root_idx] + even_delta).into_affine();
                    let (x, y) = rerandomized_plus_delta.xy().ok_or(Error::PointCantBeZero)?;
                    let (divisor_comms, p) =
                        create_and_commit_divisor::<_, F1, F0, P1, P0, Parameters1>(
                            rng,
                            odd_prover,
                            all_rerand_leaves_scalars[mp_idx][root_idx],
                            &even_parameters.table_b_blinding,
                            &odd_parameters.sl_params.bp_gens,
                        )?;
                    odd_node_comms[mp_idx].push(divisor_comms);
                    leaf_divisors[mp_idx].push((
                        leaf_x_vars_per_mp[mp_idx][root_idx].clone(),
                        y_var,
                        x,
                        y,
                        p,
                    ));
                }
            }
        } else {
            // Process the shared root once
            if root_is_even {
                let root_x_coords = match &self.root_children {
                    RootChildrenForMultiPath::Even { x_coords, .. } => x_coords.as_slice(),
                    RootChildrenForMultiPath::Odd { .. } => unreachable!(),
                };
                let selected_children_per_mp: Vec<Vec<Affine<P1>>> = multi_paths
                    .iter()
                    .map(|mp| {
                        mp.even_internal_nodes[0]
                            .iter()
                            .map(|n| n.child_node_to_randomize)
                            .collect()
                    })
                    .collect();
                let rerand_sums = all_odd_sum.iter().map(|s| s[0]).collect::<Vec<_>>();
                let rerand_scalars = all_odd_scalars.iter().map(|s| s[0]).collect::<Vec<_>>();
                let (comms, divisors) =
                    CurveTreeWitnessMultiPath::<L, M, P0, P1>::process_shared_root_for_multi_paths::<
                        _,
                        Parameters0,
                    >(
                        rng,
                        even_prover,
                        root_x_coords,
                        &selected_children_per_mp,
                        &rerand_sums,
                        &rerand_scalars,
                        odd_parameters,
                        &even_parameters.sl_params.bp_gens,
                    )?;
                for (i, (c, d)) in comms.into_iter().zip(divisors).enumerate() {
                    even_node_comms[i].push(c);
                    even_node_divisors[i].push(d);
                }
            } else {
                let root_x_coords = match &self.root_children {
                    RootChildrenForMultiPath::Odd { x_coords, .. } => x_coords.as_slice(),
                    RootChildrenForMultiPath::Even { .. } => unreachable!(),
                };
                let selected_children_per_mp: Vec<Vec<Affine<P0>>> = multi_paths
                    .iter()
                    .map(|mp| {
                        mp.odd_internal_nodes[0]
                            .iter()
                            .map(|n| n.child_node_to_randomize)
                            .collect()
                    })
                    .collect();
                let rerand_sums = all_even_sum.iter().map(|s| s[0]).collect::<Vec<_>>();
                let rerand_scalars = all_even_scalars.iter().map(|s| s[0]).collect::<Vec<_>>();
                let (comms, divisors) =
                    CurveTreeWitnessMultiPath::<L, M, P1, P0>::process_shared_root_for_multi_paths::<
                        _,
                        Parameters1,
                    >(
                        rng,
                        odd_prover,
                        root_x_coords,
                        &selected_children_per_mp,
                        &rerand_sums,
                        &rerand_scalars,
                        even_parameters,
                        &odd_parameters.sl_params.bp_gens,
                    )?;
                for (i, (c, d)) in comms.into_iter().zip(divisors).enumerate() {
                    odd_node_comms[i].push(c);
                    odd_node_divisors[i].push(d);
                }
            }

            // Process each multi-path's non-root levels and leaves
            for mp_idx in 0..num_multi_paths {
                let (nrc_e, nrd_e, nrc_o, nrd_o_summed, nrd_o_leaf) = multi_paths[mp_idx]
                    .process_non_root_nodes::<_, Parameters0, Parameters1>(
                    rng,
                    even_prover,
                    odd_prover,
                    parameters,
                    multi_paths[mp_idx].num_indices(),
                    root_is_even,
                    &all_even_sum[mp_idx],
                    &all_odd_sum[mp_idx],
                    &all_even_scalars[mp_idx],
                    &all_odd_scalars[mp_idx],
                    &all_rerand_leaves[mp_idx],
                    &all_rerand_leaves_scalars[mp_idx],
                )?;
                even_node_comms[mp_idx].extend(nrc_e);
                even_node_divisors[mp_idx].extend(nrd_e);
                odd_node_comms[mp_idx].extend(nrc_o);
                odd_node_divisors[mp_idx].extend(nrd_o_summed);
                leaf_divisors[mp_idx].extend(nrd_o_leaf);
            }
        }

        // One discrete-log challenge per curve across all multi-paths, applied to the flattened items.
        constraints_for_dlogs_presummed::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_prover,
            odd_prover,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors.into_iter().flatten(),
            odd_node_divisors.into_iter().flatten(),
            leaf_divisors.into_iter().flatten(),
        )?;

        all_even_scalars.zeroize();
        all_odd_scalars.zeroize();

        // All six per-multi-path vecs have same length `num_multi_paths`
        debug_assert!([
            all_even_sum.len(),
            all_odd_sum.len(),
            all_rerand_leaves.len(),
            even_node_comms.len(),
            odd_node_comms.len(),
            all_rerand_leaves_scalars.len(),
        ]
        .iter()
        .all(|&len| len == num_multi_paths));

        let (result, leaf_scalars): (Vec<_>, Vec<_>) = all_even_sum
            .into_iter()
            .zip(all_odd_sum)
            .zip(all_rerand_leaves)
            .zip(even_node_comms)
            .zip(odd_node_comms)
            .zip(all_rerand_leaves_scalars)
            .map(
                |(((((even_sum, odd_sum), rerand_leaves), even_comms), odd_comms), leaf_scalar)| {
                    (
                        SelectAndRerandomizeMultiPathWithDivisorComms {
                            path: SelectAndRerandomizeMultiPath {
                                even_commitments: even_sum,
                                odd_commitments: odd_sum,
                                selected_commitments: rerand_leaves,
                            },
                            even_divisor_comms: even_comms,
                            odd_divisor_comms: odd_comms,
                        },
                        leaf_scalar,
                    )
                },
            )
            .unzip();
        Ok((result, leaf_scalars))
    }
}

/// Ensure x-coordinates of all selected children of root are part of corresponding root's x-coordinates
/// and return coordinates of the sum of the selected children
#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
pub fn batched_select_and_accumulate_root<
    F: PrimeField,
    C: SWCurveConfig<BaseField = F> + Copy,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    num_indices: u32, // The number of parallel selections
    all_children_x_coords: &[F],
    selected_children_plus_delta: Option<&[Affine<C>]>,
) -> Result<(LinearCombination<F>, LinearCombination<F>)> {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };

    let chunk_size = all_children_x_coords.len() / (num_indices as usize);
    let chunks: Vec<_> = all_children_x_coords.chunks_exact(chunk_size).collect();

    for (i, chunk) in chunks.iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();

        // Select from public set
        select_public_set(cs, x_var.into(), chunk)?;

        // Curve check
        curve_check(cs, x_var.into(), y_var.into(), C::COEFF_A, C::COEFF_B);

        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            point: ith_selected_witness,
        };

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    Ok((sum_of_selected.x, sum_of_selected.y))
}

/// Enforce membership check on each child's x-coord and that each child's x,y coords are valid and
/// return the x,y coords of the sum of all children
pub fn batched_select_and_accumulate_non_root<
    F: PrimeField,
    C: SWCurveConfig<BaseField = F> + Copy,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    num_indices: u32, // The number of parallel selections
    all_children_x_coords: Vec<LinearCombination<F>>,
    selected_children_plus_delta: Option<&[Affine<C>]>,
) -> Result<(LinearCombination<F>, LinearCombination<F>)> {
    // Initialize the accumulated sum of the selected children to dummy values.
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };

    let chunk_size = all_children_x_coords.len() / (num_indices as usize);
    let chunks: Vec<_> = all_children_x_coords.chunks_exact(chunk_size).collect();

    for (i, chunk) in chunks.iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let x_var = cs.allocate(ith_selected_witness.map(|xy| xy.x)).unwrap();
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();

        // Select from public set
        select(cs, x_var.into(), chunk.iter().cloned())?;

        // Curve check
        curve_check(cs, x_var.into(), y_var.into(), C::COEFF_A, C::COEFF_B);

        let ith_selected = PointRepresentation {
            x: x_var.into(),
            y: y_var.into(),
            point: ith_selected_witness,
        };

        // Update the cumulated sum of selected children
        if i == 0 {
            // In the first iteration, the sum is the first selected child.
            sum_of_selected = ith_selected;
        } else {
            // In the consecutive iterations, add the ith selected child to the accumulated sum
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    Ok((sum_of_selected.x, sum_of_selected.y))
}

/// Sum a set of already-selected children whose x-coordinates have already been
/// constrained to be members of the relevant set. Allocates each y-coordinate, enforces the curve
/// equation, and returns the running sum's `(x, y)`.
pub fn accumulate_selected_children<
    F: PrimeField,
    C: SWCurveConfig<BaseField = F> + Copy,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    x_vars: &[LinearCombination<F>],
    selected_children_plus_delta: Option<&[Affine<C>]>,
) -> Result<(LinearCombination<F>, LinearCombination<F>)> {
    let mut sum_of_selected = PointRepresentation {
        x: Variable::One(PhantomData).into(),
        y: Variable::One(PhantomData).into(),
        point: None,
    };

    for (i, x_var) in x_vars.iter().enumerate() {
        let ith_selected_witness = selected_children_plus_delta.map(|xy| xy[i]);
        let y_var = cs.allocate(ith_selected_witness.map(|xy| xy.y)).unwrap();

        curve_check(cs, x_var.clone(), y_var.into(), C::COEFF_A, C::COEFF_B);

        let ith_selected = PointRepresentation {
            x: x_var.clone(),
            y: y_var.into(),
            point: ith_selected_witness,
        };

        if i == 0 {
            sum_of_selected = ith_selected;
        } else {
            sum_of_selected = checked_curve_addition_helper(cs, sum_of_selected, ith_selected)?;
        }
    }

    Ok((sum_of_selected.x, sum_of_selected.y))
}

/// Allocate a leaf's `(x, y)` coordinates. Extracted as a seam so tests can inject an off-curve leaf
/// (x kept in the membership set, y off the curve) to check the leaf's on-curve enforcement.
#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
fn allocate_leaf_coords<
    F1: PrimeField,
    C: SWCurveConfig<BaseField = F1>,
    Cs: ConstraintSystem<F1>,
>(
    cs: &mut Cs,
    leaf_plus_delta: Affine<C>,
) -> (Variable<F1>, Variable<F1>) {
    let x_var = cs.allocate(Some(leaf_plus_delta.x)).unwrap();
    let y_var = cs.allocate(Some(leaf_plus_delta.y)).unwrap();
    (x_var, y_var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve_tree::{CurveTree, Root};
    use crate::parameters::{SelRerandParameters, SelRerandProofParametersNew};
    use crate::utils::{prove, verify};
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_pallas::PallasConfig;
    use ark_std::UniformRand;
    use ark_vesta::VestaConfig;
    use bulletproofs::r1cs::{R1CSError, Verifier};
    use rand::thread_rng;
    use rand_core::CryptoRngCore;

    const DEPTH: usize = 4;

    type Params = SelRerandProofParametersNew<PallasConfig, VestaConfig, PallasParams, VestaParams>;
    type Witness = CurveTreeWitnessMultiPath<32, 2, PallasConfig, VestaConfig>;

    fn build() -> (
        SelRerandParameters<PallasConfig, VestaConfig>,
        Params,
        CurveTree<32, 2, PallasConfig, VestaConfig>,
    ) {
        let mut rng = thread_rng();
        let gen_len = 1 << 12;
        let sr_params =
            SelRerandParameters::<PallasConfig, VestaConfig>::new(gen_len, gen_len).unwrap();
        let sr_proof_params = Params::from_sr_params(sr_params.clone());
        let set = (0..2)
            .map(|_| Affine::<PallasConfig>::rand(&mut rng))
            .collect::<Vec<_>>();
        let curve_tree = CurveTree::<32, 2, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &sr_proof_params,
            Some(DEPTH),
        );
        assert_eq!(curve_tree.height(), DEPTH);
        (sr_params, sr_proof_params, curve_tree)
    }

    /// Run the full batched-divisor prove verify logic
    fn run<R: CryptoRngCore>(
        paths: &Witness,
        root: &Root<32, 2, PallasConfig, VestaConfig>,
        sr_params: &SelRerandParameters<PallasConfig, VestaConfig>,
        sr_proof_params: &Params,
        rng: &mut R,
    ) -> core::result::Result<(), R1CSError> {
        let mut pallas_prover: Prover<_, Affine<PallasConfig>> = Prover::new(
            &sr_params.even_parameters.pc_gens,
            MerlinTranscript::new(b"batched-negative"),
        );
        let mut vesta_prover: Prover<_, Affine<VestaConfig>> = Prover::new(
            &sr_params.odd_parameters.pc_gens,
            MerlinTranscript::new(b"batched-negative"),
        );
        let (path_commitments, _) = paths
            .batched_select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                &mut pallas_prover,
                &mut vesta_prover,
                sr_proof_params,
                rng,
            )
            .unwrap();
        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            rng,
        )
        .unwrap();

        let mut pallas_verifier = Verifier::new(MerlinTranscript::new(b"batched-negative"));
        let mut vesta_verifier = Verifier::new(MerlinTranscript::new(b"batched-negative"));
        path_commitments
            .batched_select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
                root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                sr_proof_params,
            )
            .unwrap();
        verify(
            pallas_verifier,
            vesta_verifier,
            &pallas_proof,
            &vesta_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            rng,
        )
    }

    #[test]
    fn honest_batched_path_verifies() {
        // Ensures the above run function is correct
        let mut rng = thread_rng();
        let (sr_params, sr_proof_params, curve_tree) = build();
        let root = curve_tree.root_node();
        let paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();
        assert!(run(&paths, &root, &sr_params, &sr_proof_params, &mut rng).is_ok());
    }

    #[test]
    fn non_member_root_child_is_rejected() {
        // Replace one root-selected child with a fresh on-curve point that is not a child of the root
        let mut rng = thread_rng();
        let (sr_params, sr_proof_params, curve_tree) = build();
        let root = curve_tree.root_node();
        let mut paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();

        assert!(paths.root_is_even());
        paths.even_internal_nodes[0][0].child_node_to_randomize =
            Affine::<VestaConfig>::rand(&mut rng);

        let res = run(&paths, &root, &sr_params, &sr_proof_params, &mut rng);
        assert!(
            res.is_err(),
            "a non-member root child must be rejected by the membership check"
        );
    }

    // The on-curve and divisor faults need a prover-side fault (an off-curve coordinate / a
    // mismatched blinding scalar) that cannot be expressed through public inputs, so they mock a
    // prover seam. Run with:
    //   cargo +nightly nextest run -p relations --features nightly_mocking_tests mocking
    #[cfg(feature = "nightly_mocking_tests")]
    mod mocking_tests {
        use super::*;
        use crate::prover::create_and_commit_divisor;
        use ark_ff::One;
        use ark_pallas::{Fq as PallasBase, Fr as PallasFr};
        use mocktopus::mocking::{MockResult, Mockable};
        use rand_chacha::ChaChaRng;
        use rand_core::SeedableRng;
        use std::boxed::Box;

        struct MockGuard;
        impl Drop for MockGuard {
            fn drop(&mut self) {
                super::super::batched_select_and_accumulate_root::<
                    PallasFr,
                    VestaConfig,
                    Prover<MerlinTranscript, Affine<PallasConfig>>,
                >
                    .clear_mock();
                create_and_commit_divisor::<
                    ChaChaRng,
                    PallasFr,
                    PallasBase,
                    PallasConfig,
                    VestaConfig,
                    PallasParams,
                >
                    .clear_mock();
                super::super::allocate_leaf_coords::<
                    PallasBase,
                    PallasConfig,
                    Prover<MerlinTranscript, Affine<VestaConfig>>,
                >
                    .clear_mock();
            }
        }

        #[test]
        fn off_curve_root_child_is_rejected() {
            // Prover uses one off-curve root child (x kept in the set so membership still passes)
            let _guard = MockGuard;
            let mut rng = thread_rng();
            let (sr_params, sr_proof_params, curve_tree) = build();
            let root = curve_tree.root_node();
            let paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();

            super::super::batched_select_and_accumulate_root::<
                PallasFr,
                VestaConfig,
                Prover<MerlinTranscript, Affine<PallasConfig>>,
            >
                .mock_safe(|cs, num_indices, all_x_coords, selected| {
                    let selected = selected.expect("prover supplies the selected children");
                    let mut corrupted = selected.to_vec();
                    let (x, y) = corrupted[0]
                        .xy()
                        .expect("selected child is not at infinity");
                    corrupted[0] = Affine::<VestaConfig>::new_unchecked(x, y + PallasFr::one());
                    let leaked: &'static [Affine<VestaConfig>] =
                        Box::leak(corrupted.into_boxed_slice());
                    MockResult::Continue((cs, num_indices, all_x_coords, Some(leaked)))
                });

            let res = run(&paths, &root, &sr_params, &sr_proof_params, &mut rng);
            assert!(
                res.is_err(),
                "an off-curve root child must be rejected by curve_check"
            );
        }

        #[test]
        fn off_curve_leaf_is_rejected() {
            // Prover uses one off-curve leaf
            let _guard = MockGuard;
            let mut rng = thread_rng();
            let (sr_params, sr_proof_params, curve_tree) = build();
            let root = curve_tree.root_node();
            let paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();

            super::super::allocate_leaf_coords::<
                PallasBase,
                PallasConfig,
                Prover<MerlinTranscript, Affine<VestaConfig>>,
            >
                .mock_safe(|cs, leaf_plus_delta| {
                    let x = cs.allocate(Some(leaf_plus_delta.x)).unwrap();
                    let y = cs
                        .allocate(Some(leaf_plus_delta.y + PallasBase::one()))
                        .unwrap();
                    MockResult::Return((x, y))
                });

            let res = run(&paths, &root, &sr_params, &sr_proof_params, &mut rng);
            assert!(
                res.is_err(),
                "an off-curve leaf must be rejected by its on-curve check"
            );
        }

        #[test]
        fn mismatched_blinding_divisor_is_rejected() {
            // Prover uses different scalar for divisor proof than used in node rerandomization
            let _guard = MockGuard;
            // Seeded ChaChaRng so the root divisor monomorphizes as create_and_commit_divisor::<ChaChaRng, ..>.
            let mut rng = ChaChaRng::from_seed([7u8; 32]);
            let (sr_params, sr_proof_params, curve_tree) = build();
            let root = curve_tree.root_node();
            let paths = curve_tree.get_paths_to_leaves(&[0, 1]).unwrap();

            create_and_commit_divisor::<
                ChaChaRng,
                PallasFr,
                PallasBase,
                PallasConfig,
                VestaConfig,
                PallasParams,
            >
                .mock_safe(|rng, prover, randomization, table, bp_gens| {
                    MockResult::Continue((
                        rng,
                        prover,
                        randomization + PallasBase::one(),
                        table,
                        bp_gens,
                    ))
                });

            let res = run(&paths, &root, &sr_params, &sr_proof_params, &mut rng);
            assert!(
                res.is_err(),
                "a node whose divisor proves the wrong blinding must be rejected"
            );
        }
    }
}
