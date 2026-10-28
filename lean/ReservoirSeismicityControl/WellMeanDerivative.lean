import ReservoirSeismicityControl.WellIntegralL2
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Differentiation of well averages of L²-valued trajectories

The averaging functional from `WellIntegralL2` is continuous and linear.
Hence a strongly differentiable trajectory `F : ℝ → Lp ℝ 2 μ` has a
well average whose derivative is the well average of the L² derivative.

This formalizes the interchange of a time derivative and the *spatial*
well integral under strong L² differentiability. It does NOT establish
strong L² differentiability of the ReservoirSeismicityControl seismicity state from the
PDE--ODE equations. It also does not yet prove the off-diagonal heat
semigroup or pressure-observation estimates used elsewhere in Appendix A.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A strongly differentiable L²-valued trajectory can be differentiated
through the spatial integral over any measurable set of finite measure. -/
theorem well_integral_L2_hasDerivAt
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (F : ℝ → Lp ℝ 2 μ) (F' : Lp ℝ 2 μ) (t : ℝ)
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun τ => wellIntegralL2 μ s hs hfinite (F τ))
      (wellIntegralL2 μ s hs hfinite F') t := by
  let χ : Lp ℝ 2 μ := indicatorConstLp 2 hs hfinite (1 : ℝ)
  have hinner :
      HasDerivAt ((innerSL ℝ χ) ∘ F) ((innerSL ℝ χ) F') t :=
    ((innerSL ℝ χ).hasFDerivAt.comp_hasDerivAt t hF)
  simpa only [Function.comp_def, innerSL_apply_apply, wellIntegralL2, χ]
    using hinner

/-- The same differentiation identity for the normalized spatial well mean. -/
theorem well_mean_L2_hasDerivAt
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (F : ℝ → Lp ℝ 2 μ) (F' : Lp ℝ 2 μ) (t : ℝ)
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun τ => wellMeanL2 μ s hs hfinite (F τ))
      (wellMeanL2 μ s hs hfinite F') t := by
  simpa only [wellMeanL2] using
    (well_integral_L2_hasDerivAt μ s hs hfinite F F' t hF).div_const
      (μ.real s)

/-- The derivative of the normalized mean is the normalized mean of the
strong L² derivative. No pointwise-in-space derivative is required. -/
theorem well_mean_L2_deriv
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (F : ℝ → Lp ℝ 2 μ) (F' : Lp ℝ 2 μ) (t : ℝ)
    (hF : HasDerivAt F F' t) :
    deriv (fun τ => wellMeanL2 μ s hs hfinite (F τ)) t =
      wellMeanL2 μ s hs hfinite F' := by
  exact (well_mean_L2_hasDerivAt μ s hs hfinite F F' t hF).deriv

/-- A uniform L² bound on the strong derivative of the seismicity field
implies a time-uniform bound on the actual derivative of its well mean. -/
theorem well_mean_L2_deriv_uniform
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (F Fdot : ℝ → Lp ℝ 2 μ) (C : ℝ)
    (hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (Fdot t) t)
    (hL2 : ∀ t : ℝ, 0 ≤ t → ‖Fdot t‖ ≤ C) :
    ∀ t : ℝ, 0 ≤ t →
      |deriv (fun τ => wellMeanL2 μ s hs hfinite (F τ)) t| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * C) / μ.real s := by
  intro t ht
  rw [well_mean_L2_deriv μ s hs hfinite F (Fdot t) t (hF t ht)]
  exact well_mean_L2_time_uniform μ s hs hfinite hpositive Fdot C hL2 t ht

end ReservoirSeismicityControl
