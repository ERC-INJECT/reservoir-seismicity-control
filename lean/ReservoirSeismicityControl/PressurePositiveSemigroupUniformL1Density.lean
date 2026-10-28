import ReservoirSeismicityControl.PressurePositiveSemigroupLipschitzAverages
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# ReservoirSeismicityControl (A5): L¹-density of uniformly continuous rates

Mathlib's `Integrable.exists_hasCompactSupport_integral_sub_le` proves
that compactly supported continuous functions approximate arbitrary
integrable real-valued rates in L¹ for regular measures on ℝ.
A continuous, compactly supported function on ℝ is uniformly continuous.

This is the density input for the cell-average approximation. It does not
assert L¹ convergence of the cell averages by itself. In the physical
application the finite measure is Lebesgue measure restricted to [0,T].
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology

/-- Every integrable signed well rate on a regular measure space over ℝ
can be approximated in L¹ by uniformly continuous compactly supported
functions. There is no differentiability or derivative bound assumption. -/
theorem pressure_integrable_uniform_l1_density
    (μ : Measure ℝ) [μ.Regular]
    (q : ℝ → ℝ) (hq : Integrable q μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ,
      UniformContinuous g ∧ HasCompactSupport g ∧ Integrable g μ ∧
        (∫ t, |q t - g t| ∂μ) ≤ ε := by
  obtain ⟨g, hgSupport, hgApprox, hgCont, hgInt⟩ :=
    hq.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨g,
    hgCont.uniformContinuous_of_tendsto_cocompact hgSupport.is_zero_at_infty,
    hgSupport, hgInt, ?_⟩
  simpa only [Real.norm_eq_abs] using hgApprox

/-- In particular, essentially bounded measurable well rates on a finite
regular time measure admit uniformly continuous L¹ approximations.
The approximating function need not obey the same L∞ bound: bound
preservation is ensured by the separate interval-average theorem. -/
theorem pressure_bounded_uniform_l1_density
    (μ : Measure ℝ) [μ.Regular] [IsFiniteMeasure μ]
    (q : ℝ → ℝ) (hq : AEStronglyMeasurable q μ)
    (M : ℝ) (hM : ∀ᵐ t ∂μ, |q t| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ,
      UniformContinuous g ∧ HasCompactSupport g ∧ Integrable g μ ∧
        (∫ t, |q t - g t| ∂μ) ≤ ε := by
  have hInt : Integrable q μ :=
    Integrable.of_bound hq M (by
      simpa only [Real.norm_eq_abs] using hM)
  exact pressure_integrable_uniform_l1_density μ q hInt hε

end ReservoirSeismicityControl
