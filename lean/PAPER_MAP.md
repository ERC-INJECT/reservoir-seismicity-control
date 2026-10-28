# Manuscript-to-Lean verification map

The following four source modules are the final verification entrypoints.
Successful compilation checks their results under their explicit
hypotheses; it does not automatically discharge physical assumptions.

## Physical A7/A10 assembly

`ReservoirSeismicityControl.Paper2026.PhysicalA7A10FullPhysicalFromGreen20261027`

Principal theorem: `paper_A10_full_from_actual_A7_and_green_cutoff`.
It assembles A7 local SR estimates with A10 pressure, reaction, near/far
and cutoff results under the theorem's specified analytic inputs.

## Spatial dimension and restricted measure

`ReservoirSeismicityControl.Paper2026.VerificationSpatialNDRestrictedSmooth20261027`

A verification checkpoint for `n_d = 1, 2, 3`, restricted physical
measures, smooth test density and related weak-generator results.

## Physical positive Neumann realization

`ReservoirSeismicityControl.Paper2026.PhysicalPressureNDA10PositiveRealization20261027`

Principal theorem: `pressure_nd_physical_volume_canonical_A3_positive_generator`.
It identifies a symmetric, nonnegative physical generator under the
module's smooth approximation and Green-identity hypotheses.

## Finite-dimensional control certificates

`ReservoirSeismicityControl.PaperFinalCertificatesAudit`

The module checks previously established declarations, including:

- `paper_theorem1_actual_derivative_from_contraction_ae`
- `paper_theorem2_exact_demand_bridge`
- `paper_physical_demand_contraction_from_vertices`
- `paper_physical_wellCLM_hasDerivAt_ae`
- `paper_physical_gainCLM_hasDerivAt_ae`
- `paper_physical_theorem2_certificates_from_vertices_ae`

This map is an entrypoint guide rather than a claim that the Lean
source independently proves every analytical or physical assumption.
