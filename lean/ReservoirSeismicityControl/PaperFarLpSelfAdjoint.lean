import ReservoirSeismicityControl.PaperFarLpProjection
import ReservoirSeismicityControl.PaperFarProjectedNeumannBounds
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stage 69 — Self-adjoint spatial projection on the real L² space

Stage 68 constructed the concrete indicator cutoff as a bounded linear map
on almost-everywhere equivalence classes in `Lp ℝ 2 μ`. Here we prove
self-adjointness for its actual L² inner product and connect it with
Stage 66's localization identity and bound.

No PDE semigroup, off-diagonal estimate, or derivative of the well rates
is assumed or established in this module.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- Multiplication by a measurable indicator is self-adjoint for the
actual Hilbert-space inner product on real L². -/
theorem paper_far_lp_projection_selfAdjoint
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f g : Lp ℝ (2 : ENNReal) μ) :
    ⟪paperFarLpProjection μ far hfar f, g⟫_ℝ =
      ⟪f, paperFarLpProjection μ far hfar g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ far hfar f,
       paper_far_lp_cutoff_coeFn μ far hfar g]
    with x hf hg
  simp only [paper_far_lp_projection_apply] at *
  rw [hf, hg]
  by_cases hx : x ∈ far
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, inner_zero_left, inner_zero_right]

/-- An L² function supported almost everywhere in the far region is fixed
by the concrete indicator projection. -/
theorem paper_far_lp_projection_eq_of_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (w : Lp ℝ (2 : ENNReal) μ)
    (hw : ∀ᵐ x ∂μ, x ∉ far → (w : Ω → ℝ) x = 0) :
    paperFarLpProjection μ far hfar w = w := by
  rw [paper_far_lp_projection_apply]
  apply Lp.ext
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ far hfar w, hw]
    with x hcut hsupp
  rw [hcut]
  by_cases hx : x ∈ far
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx]
    exact (hsupp hx).symm

/-- Stage 66's exact localization identity for the concrete L² projection.
The observation weight need only be supported in the far region a.e. -/
theorem paper_far_lp_localized_inner
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (w v : Lp ℝ (2 : ENNReal) μ)
    (hw : ∀ᵐ x ∂μ, x ∉ far → (w : Ω → ℝ) x = 0) :
    ⟪w, v⟫_ℝ =
      ⟪w, paperFarLpProjection μ far hfar v⟫_ℝ := by
  exact paper_far_projected_inner
    (paperFarLpProjection μ far hfar)
    (paper_far_lp_projection_selfAdjoint μ far hfar)
    w v (paper_far_lp_projection_eq_of_support μ far hfar w hw)

/-- The physical far-region cutoff discharges the self-adjointness
assumption of Stage 66's projected Cauchy–Schwarz estimate. -/
theorem paper_far_lp_localized_inner_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (w v : Lp ℝ (2 : ENNReal) μ)
    (hw : ∀ᵐ x ∂μ, x ∉ far → (w : Ω → ℝ) x = 0) :
    |⟪w, v⟫_ℝ| ≤ ‖w‖ * ‖paperFarLpProjection μ far hfar v‖ := by
  exact paper_far_projected_inner_bound
    (paperFarLpProjection μ far hfar)
    (paper_far_lp_projection_selfAdjoint μ far hfar)
    w v (paper_far_lp_projection_eq_of_support μ far hfar w hw)

end ReservoirSeismicityControl
