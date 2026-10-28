import ReservoirSeismicityControl.WellSensitivity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Continuous well integrals controlled by spatial L² bounds

This module replaces the finite quadrature of `WellSensitivity` by an actual
Lebesgue integral over a measurable well support `s` of finite measure.

For `f : Lp ℝ 2 μ`, the integral on `s` is represented by its L² inner product
with the indicator of `s`.  Cauchy--Schwarz bounds the integral and its mean
using only the spatial L² norm, not a pointwise bound on `f`.

Theorems hold for an arbitrary measure space, hence also for a measurable
well region in a three-dimensional reservoir equipped with volume measure.
They do not derive the time-dependent L² bounds from the reservoir PDE--ODE,
or establish differentiation under the spatial integral.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The integral of an L² real field over a finite-measure well support.
The inner-product representation is insensitive to the chosen a.e. representative. -/
noncomputable def wellIntegralL2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (f : Lp ℝ 2 μ) : ℝ :=
  inner ℝ (indicatorConstLp 2 hs hfinite (1 : ℝ)) f

/-- The L² definition is the actual set integral, rather than a finite sum. -/
theorem well_integral_L2_eq_set_integral
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (f : Lp ℝ 2 μ) :
    wellIntegralL2 μ s hs hfinite f =
      ∫ x in s, inner ℝ (1 : ℝ) (f x) ∂μ := by
  exact MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner
    ℝ f hs (1 : ℝ) hfinite

/-- The continuous well integral is bounded by the L² norm and the square
root of the support volume. This is Cauchy--Schwarz on the indicator of `s`. -/
theorem well_integral_L2_bound
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (f : Lp ℝ 2 μ) :
    |wellIntegralL2 μ s hs hfinite f| ≤
      (μ.real s) ^ (1 / (2 : ℝ)) * ‖f‖ := by
  have hcs :
      ‖inner ℝ (indicatorConstLp (2 : ENNReal) hs hfinite (1 : ℝ)) f‖ ≤
        ‖indicatorConstLp (2 : ENNReal) hs hfinite (1 : ℝ)‖ * ‖f‖ :=
    norm_inner_le_norm _ _
  have hind :
      ‖indicatorConstLp (2 : ENNReal) hs hfinite (1 : ℝ)‖ =
        (μ.real s) ^ (1 / (2 : ℝ)) := by
    simpa using (MeasureTheory.norm_indicatorConstLp
      (μ := μ) (p := (2 : ENNReal)) (hs := hs) (hμs := hfinite)
      (c := (1 : ℝ)) (by norm_num) (by norm_num))
  simpa [wellIntegralL2, Real.norm_eq_abs, hind] using hcs

/-- The normalized well average is the spatial integral divided by the
positive support measure. -/
noncomputable def wellMeanL2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (f : Lp ℝ 2 μ) : ℝ :=
  wellIntegralL2 μ s hs hfinite f / μ.real s

/-- The normalized well average inherits an L² bound without assuming any
pointwise control of the field. Here `μ.real s` is the positive well volume. -/
theorem well_mean_L2_bound
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (f : Lp ℝ 2 μ) :
    |wellMeanL2 μ s hs hfinite f| ≤
      ((μ.real s) ^ (1 / (2 : ℝ)) * ‖f‖) / μ.real s := by
  dsimp [wellMeanL2]
  rw [abs_div, abs_of_pos hpositive]
  exact div_le_div_of_nonneg_right
    (well_integral_L2_bound μ s hs hfinite f) hpositive.le

/-- If an L²-valued rate field is uniformly bounded in time, its spatially
averaged rate is bounded uniformly in time as well. This is a bound on the
average of the rate field, not yet identification with the derivative of the
mean of the underlying state. -/
theorem well_mean_L2_time_uniform
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (f : ℝ → Lp ℝ 2 μ) (C : ℝ)
    (hL2 : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C) :
    ∀ t : ℝ, 0 ≤ t →
      |wellMeanL2 μ s hs hfinite (f t)| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * C) / μ.real s := by
  intro t ht
  have hfactor : 0 ≤ (μ.real s) ^ (1 / (2 : ℝ)) := by
    positivity
  calc
    |wellMeanL2 μ s hs hfinite (f t)| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * ‖f t‖) / μ.real s :=
      well_mean_L2_bound μ s hs hfinite hpositive (f t)
    _ ≤ ((μ.real s) ^ (1 / (2 : ℝ)) * C) / μ.real s := by
      apply div_le_div_of_nonneg_right _ hpositive.le
      exact mul_le_mul_of_nonneg_left (hL2 t ht) hfactor

end ReservoirSeismicityControl
