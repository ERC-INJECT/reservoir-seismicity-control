import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ProjectedDerivative
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9BoundedFlux
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9IntegrationByParts
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ZeroBoundary
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9PhysicalInitial
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ObservationRate
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9Causal
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothKernel
import ReservoirSeismicityControl.Paper2026.PhysicalA14NormalizedRate
import ReservoirSeismicityControl.Paper2026.PhysicalA14InverseTransport
import ReservoirSeismicityControl.Paper2026.PhysicalA14GainRate
import ReservoirSeismicityControl.Paper2026.PhysicalA12FullInverse
import ReservoirSeismicityControl.Paper2026.PhysicalA12FullGainBound
import ReservoirSeismicityControl.Paper2026.PhysicalA11RegionalMean
import ReservoirSeismicityControl.Paper2026.PhysicalA12FullPhysical
import ReservoirSeismicityControl.Paper2026.PhysicalA12FullNominal
import ReservoirSeismicityControl.Paper2026.PhysicalA12Geometry
import ReservoirSeismicityControl.Paper2026.PhysicalA12Inverse
import ReservoirSeismicityControl.Paper2026.PhysicalA12Normalization
import ReservoirSeismicityControl.Paper2026.PositiveSRNearFiniteWeakRate
import ReservoirSeismicityControl.Paper2026.PositivePressureNearFiniteDerivative
import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import ReservoirSeismicityControl.Paper2026.PositiveSRNearWeakIncrement
import ReservoirSeismicityControl.Paper2026.PositiveSRNearWeakBound
import ReservoirSeismicityControl.Paper2026.PositiveSRNearFarSplit
import ReservoirSeismicityControl.Paper2026.PositiveSRDiffusionWeight
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3FixedReference
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3CanonicalB19
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionCoordinates
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3A3Reaction
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionA3L2
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionA3Coefficients
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3PhysicalReaction
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionValue
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionFiniteRegions
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionFromEvolution
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionL2Envelope
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionRegional
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionRate
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3References
import ReservoirSeismicityControl.SeismicityUniformBounds
import ReservoirSeismicityControl.SeismicityPhysicalL2RateBridge
import ReservoirSeismicityControl.PaperRegionalPerturbationComponents
import ReservoirSeismicityControl.PaperFarCausalConvolutionBridge
import ReservoirSeismicityControl.PaperFarNoncompactConvolutionLimit
import ReservoirSeismicityControl.PaperPhysicalSRMovingFarKernel
import ReservoirSeismicityControl.PaperConstructiveNominalGain
import ReservoirSeismicityControl.PaperPhysicalSRMultiwellInverse
import ReservoirSeismicityControl.PaperPhysicalDemandWellNormFromSR
import ReservoirSeismicityControl.PaperPhysicalSRAveragesFinalCertificates
import ReservoirSeismicityControl.PaperGainContraction
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8Geometry
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8L1
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8ZeroLimit

/-!
# Narrow, paper-only verification entry point (23 Oct 2026)

Only imported, already-written proof components are checked here. A Lean build
checks each proof against its EXPLICIT hypotheses. It is NOT equivalent to
establishing all hypotheses of Theorems 1 and 2 from Assumptions 1--6.

External results are restricted to what the paper CITES: standard Neumann PDE
semigroup / elliptic / Sobolev results and Moreno--García-Mathey MIMO STA.
They are not reproved, imported from an unverified source, or silently axiomatized.

COMPATIBILITY: existing legacy physical SR ODE interfaces can be s=-1 specific;
the current signed physical well input is now verified for BOTH signs,
with a separate new P2 pointwise logistic bridge. Legacy B demand matrix uses the old sign; the new P5 bridge proves
that its algebraic evaluation at -β equals the corrected physical (+) row.
The physical β remains positive; all unmodified legacy certificates
are invalid for the new manuscript unless transported through this bridge.
The n_d=1,2 cases await connection to the cited dimension-dependent estimates.
-/

-- Paper eqs. (3), (12), (15): check of sign cancellation only.
#check ReservoirSeismicityControl.Paper2026.signed_sr_input_coefficient
#print axioms ReservoirSeismicityControl.Paper2026.signed_sr_input_coefficient

-- P0: eqs. (3), (12)--(15), exact actual regional SR well integrals.
#check ReservoirSeismicityControl.Paper2026.sr_signed_physical_matrix_eq
#print axioms ReservoirSeismicityControl.Paper2026.sr_signed_physical_matrix_eq
#check ReservoirSeismicityControl.Paper2026.sr_signed_physical_action_eq
#print axioms ReservoirSeismicityControl.Paper2026.sr_signed_physical_action_eq
#check ReservoirSeismicityControl.Paper2026.signed_sr_error_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.signed_sr_error_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.sr_physical_eq_normalized_nominal
#print axioms ReservoirSeismicityControl.Paper2026.sr_physical_eq_normalized_nominal
#check ReservoirSeismicityControl.Paper2026.sr_physical_supported_entry_positive
#print axioms ReservoirSeismicityControl.Paper2026.sr_physical_supported_entry_positive
#check ReservoirSeismicityControl.Paper2026.sr_legacy_matrix_is_negative
#print axioms ReservoirSeismicityControl.Paper2026.sr_legacy_matrix_is_negative

-- P2: signed SR equation gives the transformed logistic derivative and bounds.
#check ReservoirSeismicityControl.Paper2026.signed_physical_sr_logistic_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.signed_physical_sr_logistic_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.signed_physical_sr_uniform_bounds
#print axioms ReservoirSeismicityControl.Paper2026.signed_physical_sr_uniform_bounds

-- A.1 / A.2: scalar pressure mean and logistic SR ingredients.
#check ReservoirSeismicityControl.mean_pressure_bound
#print axioms ReservoirSeismicityControl.mean_pressure_bound
#check ReservoirSeismicityControl.physical_sr_uniform_bounds_from_original_ode
#print axioms ReservoirSeismicityControl.physical_sr_uniform_bounds_from_original_ode
#check ReservoirSeismicityControl.sr_rate_L2_from_pressure_ae
#print axioms ReservoirSeismicityControl.sr_rate_L2_from_pressure_ae

-- A.3: near/far component reduction; estimates from the PDE are premises.
#check ReservoirSeismicityControl.paper_far_actual_derivative_bound_from_causal_kernel_ae
#print axioms ReservoirSeismicityControl.paper_far_actual_derivative_bound_from_causal_kernel_ae
#check ReservoirSeismicityControl.paper_regional_psi_actual_derivative_from_components_ae
#print axioms ReservoirSeismicityControl.paper_regional_psi_actual_derivative_from_components_ae
#check ReservoirSeismicityControl.paper_physical_sr_far_kernel_observation_deriv_bound_ae
#print axioms ReservoirSeismicityControl.paper_physical_sr_far_kernel_observation_deriv_bound_ae

-- A.4, theorem 1: constructive diagonal gain and normalized disturbance.
#check ReservoirSeismicityControl.paper_sr_midpoint_normalization_uniform
#print axioms ReservoirSeismicityControl.paper_sr_midpoint_normalization_uniform
#check ReservoirSeismicityControl.paper_physical_sr_multiwell_integral_inverse_certificate
#print axioms ReservoirSeismicityControl.paper_physical_sr_multiwell_integral_inverse_certificate
#check ReservoirSeismicityControl.paper_theorem1_actual_derivative_from_contraction_ae
#print axioms ReservoirSeismicityControl.paper_theorem1_actual_derivative_from_contraction_ae

-- B, theorem 2: actual SR well averages, allocation, vertices, derivative.
#check ReservoirSeismicityControl.paper_physical_theorem2_certificates_from_sr_L2_ae
#print axioms ReservoirSeismicityControl.paper_physical_theorem2_certificates_from_sr_L2_ae
#check ReservoirSeismicityControl.paper_physical_demand_certificate_without_well_operator_bound
#print axioms ReservoirSeismicityControl.paper_physical_demand_certificate_without_well_operator_bound

-- P5: correct positive SR matrix and reuse of demand vertex-contraction
-- certificate without suppressing the pressure-to-SR cross terms.
#check ReservoirSeismicityControl.Paper2026.positive_sr_matrix_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_matrix_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.physical_sr_matrix_eq_scaled_positive
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_matrix_eq_scaled_positive
#check ReservoirSeismicityControl.Paper2026.positive_demand_matrix_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_matrix_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_sr_pressure_block_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_pressure_block_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_sr_sr_block_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_sr_block_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_sr_combined_action_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_combined_action_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_demand_gain_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_gain_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_vertices
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_vertices

-- P5 (B19): correct positive-physical demand gain, well-operator and
-- rate-geometry representations, transporting the established a.e. bound.
#check ReservoirSeismicityControl.Paper2026.positive_demand_wellCLM_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_wellCLM_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_demand_rate_geometry_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_rate_geometry_eq_legacy_rebased
#check ReservoirSeismicityControl.Paper2026.positive_demand_normalized_rate_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_normalized_rate_ae

-- P5 (B15): correct mean/deviation decomposition of the physical
-- positive SR input, and non-diagonal allocated gain from B0 C_W = I.
#check ReservoirSeismicityControl.Paper2026.positive_sr_mean_deviation_entry
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_mean_deviation_entry
#check ReservoirSeismicityControl.Paper2026.positive_sr_allocated_mean_deviation
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_allocated_mean_deviation
#check ReservoirSeismicityControl.Paper2026.positive_demand_B15_gain
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B15_gain

-- P5 (B16): manuscript's symmetric mean/deviation vertex test + explicit T(h)
-- imply the already built corrected-positive B18 contraction certificate.
#check ReservoirSeismicityControl.Paper2026.positive_B16_sr_block_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_sr_block_eq_physical
#check ReservoirSeismicityControl.Paper2026.positive_B16_cross_block_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_cross_block_eq_physical
#check ReservoirSeismicityControl.Paper2026.positive_B16_action_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_action_eq_physical
#check ReservoirSeismicityControl.Paper2026.positive_B16_symmetric_quadratic
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_symmetric_quadratic
#check ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_B16_vertices
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_B16_vertices

-- P5 / Assumption 6: null-space and Gram inverse certificates construct
-- C_W and F_D; discharge B₀ C_W = I in the already proved B16/B18 bridge.
#check ReservoirSeismicityControl.Paper2026.positive_allocation_nominal_right_inverse
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_nominal_right_inverse
#check ReservoirSeismicityControl.Paper2026.positive_allocation_nullspace
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_nullspace
#check ReservoirSeismicityControl.Paper2026.positive_allocation_demand_right_inverse
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_demand_right_inverse
#check ReservoirSeismicityControl.Paper2026.positive_allocation_exact_demand
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_exact_demand
#check ReservoirSeismicityControl.Paper2026.positive_demand_B16_from_allocation
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B16_from_allocation

-- P5: remove standalone sensitivity-box and well-operator-bound premises by
-- inserting the actual gamma_1 R spatial integrals and existing A.2 bounds.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B18_from_actual_sr_integrals
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B18_from_actual_sr_integrals
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_well_operator_from_actual_sr_integrals
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_well_operator_from_actual_sr_integrals

-- P5 (B19): actual SR Lebesgue well averages give the a.e. sensitivity
-- derivatives and well-operator bound; the strong L2 evolution supplies
-- the rate without an independent Rdot-rate hypothesis.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_actual_sr_L2_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_actual_sr_L2_ae
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_ae

-- P3 -> P5 (B19): regional Psi/Psi-dot bounds and derivative now follow
-- from the four physical Appendix A.3 component estimates, not three
-- independent aggregate Psi assumptions.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_ae

-- P3 (A.3) / A2: reference contribution and reference-rate hypotheses
-- discharged by the fixed output scaling of the reference velocity.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_A2_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_A2_ae

-- P3 / A.3: pointwise SR reaction differentiated and bounded from A3/A7.
#check ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_rate_envelope
#print axioms ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_rate_envelope

-- P3 A.3 signed physical SR reaction regional Lebesgue integral.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_pointwise_derivative
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_pointwise_derivative

-- P3 / A.3: the independent L² reaction-rate bound is replaced by the
-- paper's coefficient-rate forcing, multiplier, and SR L²-rate bounds.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_L2_rate_from_components_ae
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_L2_rate_from_components_ae
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_L2_components
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_L2_components

-- P3 / A.3: actual signed regional SR reaction integral, with Rdot L²
-- controlled from the already verified strong pressure-to-SR evolution.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_sr_evolution
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_sr_evolution

-- P3 / A.3: finite SR output-region aggregation of the actual signed reaction.
-- Per-region strong L2 reaction/product hypotheses remain explicit.
#check ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_regions
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_regions
#check ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_evolution
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_evolution

-- P3 / A.3: bound the VALUE of the signed regional SR reaction from its
-- actual L2 representative and its finite-region output embedding.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_value_from_L2
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_value_from_L2
#check ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_from_L2
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_from_L2
#check ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_uniform
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_uniform

-- P3 -> B19: replace three abstract reaction-component hypotheses with the
-- actual signed regional reaction integrals, physical rate and L2 envelopes.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_physical_sr_reaction_P3_A2_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_physical_sr_reaction_P3_A2_ae

-- P3 / A.3: physical A3/A7 coefficient bounds, retaining |Rt| for Holder.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_three_coefficients
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_three_coefficients
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_rate_envelope
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_rate_envelope

-- P3 / A.3: bounded physical coefficient fields -> finite-volume L2 bounds.
#check ReservoirSeismicityControl.Paper2026.physical_sr_indicator_L2_of_ae_bound
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_indicator_L2_of_ae_bound
#check ReservoirSeismicityControl.Paper2026.physical_sr_A3_multiplier_opNorm
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_A3_multiplier_opNorm
#check ReservoirSeismicityControl.Paper2026.physical_sr_A3_actual_reaction_L2_bounds
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_A3_actual_reaction_L2_bounds

-- P3 -> P5/B19: A3/A7 pointwise coefficient envelopes imply the actual
-- regional L2 reaction/forcing/multiplier bounds a.e. in time, removing three
-- independent norm-bound assumptions from the signed reaction-to-B19 bridge.
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_reaction_P3_A2_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_reaction_P3_A2_ae

-- P3 / Eq. (14): canonical signed SR output slots (pressure slots zero).
#check ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_embed_apply
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_embed_apply
#check ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_pressure_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_pressure_zero
#check ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_sr_entry
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_sr_entry
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_canonical_eq
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_canonical_eq

-- P3 -> P5/B19, Eq. (14): physical signed SR coordinates, no arbitrary
-- injection map; all strong L² / near-far / A6 premises remain explicit.
#check ReservoirSeismicityControl.Paper2026.physical_sr_reaction_rate_canonical_eq
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_rate_canonical_eq
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_canonical_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_canonical_SR_ae

-- P3/A2: literal fixed pressure/SR reference scale from (12)/(14).
#check ReservoirSeismicityControl.Paper2026.paper_reference_scale_pressure
#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_pressure
#check ReservoirSeismicityControl.Paper2026.paper_reference_scale_SR
#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_SR
#check ReservoirSeismicityControl.Paper2026.paper_reference_scale_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_fixed_reference_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_fixed_reference_ae

-- P3 / A.3: actual normalized SR diffusion observation weight,
-- including its physical regional representative and strong L² derivative.
-- Near-field generator-domain and far off-diagonal hypotheses remain open.
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_representative
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_representative
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_estimates
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_estimates

-- P3 / A.3 physical near/far split: exact normalized weight,
-- its two strong time derivatives, value/rate bounds and diffusion pairing.
-- The near D(A) and far Davies–Gaffney applicability remain explicit.
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_split
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_split
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_norm_bounds
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_norm_bounds
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_rate_bounds
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_rate_bounds
#check ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_observation_split
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_observation_split

-- P3 / A.3: physical near-field symmetry on the unbounded Neumann domain,
-- and uniform norm bound on the two-term weak derivative expression.
-- Published elliptic H² -> D(A), generator bound, and weak differentiation
-- are still explicit applicability obligations; no Qdot hypothesis.
#check ReservoirSeismicityControl.Paper2026.paper_sr_near_weight_symmetric_pairing
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_weight_symmetric_pairing
#check ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_value_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_value_bound
#check ReservoirSeismicityControl.Paper2026.paper_sr_near_weak_rate_rhs_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_weak_rate_rhs_bound

-- P3: normalized physical near-field observation, two-time increment
-- and its Cauchy--Schwarz bound, with no derivative of A p or Q.
#check ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment
#check ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment_bound

-- P3 / A.3: actual pressure and SR near-field diffusion VALUE,
-- with normalized finite-volume weights and canonical output coordinates.
-- The weak derivative and local H2 -> D(A) remain open.
#check ReservoirSeismicityControl.Paper2026.paper_pressure_near_weight_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_weight_bound
#check ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_bound
#check ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_value_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_value_bound

-- P3 / Appendix A.3: genuine weak time derivative for the fixed PRESSURE
-- near-field observation via Neumann-domain symmetry and strong L2 pressure rate.
-- The SR near-field derivative and elliptic-domain applicability remain open.
#check ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.paper_pressure_near_derivative_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_derivative_bound

-- P3 / Appendix A.3: full finite-dimensional PRESSURE near weak derivative
-- from fixed weights and the passed symmetric-domain pressure identity.
-- The moving SR weak derivative and local H2 generator applicability remain open.
#check ReservoirSeismicityControl.Paper2026.paper_physical_pressure_near_finite_derivative_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_pressure_near_finite_derivative_ae
#check ReservoirSeismicityControl.Paper2026.paper_physical_near_pressure_component_eq
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_near_pressure_component_eq


-- P3 / A.3: finite-dimensional SR weak-RHS and complete near-RHS bound.
-- These are NOT a proof of the moving SR weak derivative identity.
#check ReservoirSeismicityControl.Paper2026.paper_physical_sr_near_weak_rate_finite_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_sr_near_weak_rate_finite_bound
#check ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_weak_rate_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_weak_rate_bound

-- P4: exact A12 pressure-ratio scaling for the physical signed SR matrix.
#check ReservoirSeismicityControl.Paper2026.paper_A12_pressure_weighted_midpoint
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_pressure_weighted_midpoint
#check ReservoirSeismicityControl.Paper2026.paper_A12_sr_matrix_ratio_cancel
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_sr_matrix_ratio_cancel
#check ReservoirSeismicityControl.Paper2026.paper_A12_actual_SR_equals_midpoint_matrix
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_actual_SR_equals_midpoint_matrix

-- P4 / A12: inverse and sharp norm bound for the actual SR well matrix.
-- Domain: nonnegative physical times; geometry/rank and SR box hypotheses visible.
#check ReservoirSeismicityControl.Paper2026.paper_A12_SR_interval_margin_eq
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_SR_interval_margin_eq
#check ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_certificate
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_certificate

-- P4 / A4 -> A12: nonempty well support implies strict nominal SR Gram
-- positivity; the actual physical inverse no longer assumes hgram.
#check ReservoirSeismicityControl.Paper2026.paper_A12_nominal_SR_gram_pos
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_nominal_SR_gram_pos
#check ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_from_A4
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_from_A4

-- P4 / Assumption 4: exact FULL nominal (pressure + SR) Gram,
-- including cross-channel orthogonality and B0 C0 = I, not merely SR.
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_gram_pos
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_gram_pos
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_cross_gram_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_cross_gram_zero
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_right_inverse_from_A4
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_right_inverse_from_A4

-- P4 / A.4: actual B(t) shares the nominal well support; full gain has
-- zero pressure/SR cross entries, and pressure gain is exactly beta0/beta.
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_row
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_row
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_off_diagonal_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_off_diagonal_zero
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_gain
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_gain

-- P4 / A11: for the actual physical SR Lebesgue well inputs, A4's constant
-- supported nominal row turns the Gram ratio into the paper's ARITHMETIC
-- mean over all wells assigned to each SR output region.
#check ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_row
#print axioms ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_row
#check ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_gain_arithmetic_mean
#print axioms ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_gain_arithmetic_mean

-- P4/A12: complete physical operator-norm contraction, derived from actual
-- well-integral sensitivity intervals and the verified A4/A11 geometry.
#check ReservoirSeismicityControl.Paper2026.paper_A12_regional_mean_interval
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_regional_mean_interval
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_diagonal_to_opNorm
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_diagonal_to_opNorm
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_well_interval
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_well_interval
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_A3
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_A3

-- P4: full physical (A12) inverse (new candidate, pending local Lean check).
#check ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_inverse_from_A3
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_inverse_from_A3

-- P4: exact a.e. full physical gain derivative from L² SR and Euclidean rate norm.
#check ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_deriv_from_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_deriv_from_SR_ae
#check ReservoirSeismicityControl.Paper2026.paper_A14_full_rate_geometry_factor
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_rate_geometry_factor
#check ReservoirSeismicityControl.Paper2026.paper_A14_full_physical_rate_opNorm_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_physical_rate_opNorm_bound

#check ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_rate_from_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_rate_from_SR_ae

-- P4/A14: the actual physical full inverse and normalized Psi derivative.
-- This is conditional only on A3/A7 applicability and P3's a.e. Psi derivative,
-- which are not silently discharged by the final statement.
#check ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_wells
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_wells
#check ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_SR_ae
#check ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_derivative_from_A3_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_derivative_from_A3_ae

#check ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_rate_bound_from_A3_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_rate_bound_from_A3_ae


-- P3/A.3: actual smooth-complement far SR kernel from the *same*
-- normalized weight as the passed near/far decomposition. Frozen-lag
-- (A8) and moving-observation-time (A9) derivatives are distinct.
#check ReservoirSeismicityControl.Paper2026.paperSRFarSmoothKernel
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_lag_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_lag_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_hasDerivAt
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_ae

-- P3/A.3: the physical smooth-complement SR weight is fixed by the sharp
-- far projection, and its kernel/rate bounds follow from projected orbit
-- estimates (Davies--Gaffney is a named external applicability condition).
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_fixed
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_fixed
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projected_kernel_bounds
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projected_kernel_bounds
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_nonunit_set
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_nonunit_set
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_nonunit_cutoff_separation
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_nonunit_cutoff_separation

-- P3/A8: one physical cutoff for the entire finite well family.
-- The actual projected Neumann orbit inequalities remain the external
-- Davies–Gaffney applicability inputs, not Lean-derived PDE estimates.
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_cutoff_all_wells_separated
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_cutoff_all_wells_separated
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_from_all_well_cutoff
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_from_all_well_cutoff

-- P3/A8: L¹ integrability of actual smooth SR kernel lag derivative,
-- conditional only on the published Neumann-semigroup envelope/regularity.
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_lag_rate_integrable
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_lag_rate_integrable

-- P3 / A8: positive-lag physical kernel limit and uniform magnitude.
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_zero_lag
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_zero_lag
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_value_uniform
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_value_uniform

-- P3/A9: the physical smooth SR kernel's causal value term is now bounded
-- from the verified A8 amplitude, without a separate K(t) hypothesis.
-- Time-reversed L1 mass and the actual observation derivative remain open.
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_value
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_value

-- P3/A9: Mathlib interval change-of-variables removes time-reversed kernel
-- hypotheses using the established physical positive-lag A8 L1 certificate.
#check ReservoirSeismicityControl.Paper2026.paper_A9_lag_reflection
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_lag_reflection
#check ReservoirSeismicityControl.Paper2026.paper_A9_lag_mass_le_positive
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_lag_mass_le_positive
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_L1
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_L1

-- P3/A9: actual far-observation a.e. rate bound uses the verified A8
-- smooth kernel and reflection. The PDE identity remains an open input.
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_A8_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_A8_ae

-- P3/A9: the first two terms of the physical far derivative are the
-- moving SR weight plus the semigroup initial-data term. Their a.e.
-- bound follows from the compiled L² weight/rate estimates and A3/A5.
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_physical_initial_bound_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_physical_initial_bound_ae
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_physical_initial_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_physical_initial_ae

-- P3/A8 -> A9: zero-lag continuation and endpoint cancellation.
#check ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_positive
#check ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_tendsto
#check ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_finite_well_boundary
#check ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_causal_interior
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_zero_boundary
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_zero_boundary


-- P3/A9: smooth-input integration by parts uses the physical zero-lag
-- extension from A8 and removes Q' from the causal finite-well formula.
-- Bounded-input extension and mild PDE observation identity remain OPEN.
#check ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_integration_by_parts
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_integration_by_parts
#check ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_zero_extension
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_zero_extension
#check ReservoirSeismicityControl.Paper2026.paper_A9_smooth_multiwell_causal_identity
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_multiwell_causal_identity


-- P3/A9: measurable L∞ well fluxes give genuine integrable causal
-- convolutions from the physical smooth-kernel A8 L¹ estimate.
-- This is NOT the still-open PDE far-observation derivative identity.
#check ReservoirSeismicityControl.Paper2026.paper_A9_L1_kernel_times_bounded_flux
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_L1_kernel_times_bounded_flux
#check ReservoirSeismicityControl.Paper2026.paper_A9_bounded_causal_flux_from_positive_L1
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_bounded_causal_flux_from_positive_L1
#check ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_bounded_flux_integrable_from_A8
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_bounded_flux_integrable_from_A8

-- P3/A9: true moving-weight derivative from the far-projected L² pressure rate.
#check ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_moving_weight_from_projected_pressure_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_moving_weight_from_projected_pressure_ae
