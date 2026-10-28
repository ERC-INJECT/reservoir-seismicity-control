import ReservoirSeismicityControl.PressurePositiveSemigroupAverageBound

/-!
# ReservoirSeismicityControl A5: L1 stability of signed cell averages

This module gives the key contraction estimate for scalar cell averages:

  |average(q) - average(r)| <= average(|q-r|).

The measure can be any finite measure, in particular Lebesgue measure
restricted to an interval. Neither positivity of q and r nor a time
derivative is required.

The resulting error estimate against a constant is useful for proving
convergence of interval averages for continuous comparison functions.
Density of such functions in L1, and therefore convergence for all
bounded measurable well rates, is NOT established in this module.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

section AverageL1

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsFiniteMeasure μ]

/-- Cell averaging is contractive from the average L1 discrepancy
of two integrable signed inputs to the absolute difference of the
averages. -/
theorem pressure_average_l1_contraction
    (q r : α → ℝ) (hq : Integrable q μ) (hr : Integrable r μ) :
    |(⨍ x, q x ∂μ) - (⨍ x, r x ∂μ)| ≤
      ⨍ x, |q x - r x| ∂μ := by
  have hdiff : Integrable (fun x => q x - r x) μ := hq.sub hr
  have habs : Integrable (fun x => |q x - r x|) μ := hdiff.abs
  have hUpper :
      0 ≤ ⨍ x, |q x - r x| - (q x - r x) ∂μ := by
    apply average_nonneg
    intro x
    exact sub_nonneg.mpr (le_abs_self (q x - r x))
  have hLower :
      0 ≤ ⨍ x, |q x - r x| + (q x - r x) ∂μ := by
    apply average_nonneg
    intro x
    change 0 ≤ |q x - r x| + (q x - r x)
    simpa only [sub_eq_add_neg, neg_neg] using
      (sub_nonneg.mpr (neg_le_abs (q x - r x)))
  rw [average_fun_sub habs hdiff, average_fun_sub hq hr] at hUpper
  rw [average_fun_add habs hdiff, average_fun_sub hq hr] at hLower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Comparing the average of an integrable well rate with a constant
is controlled by its average absolute discrepancy from that constant.
For a time cell, this is the local L1 error estimate. -/
theorem pressure_average_error_against_constant
    [NeZero μ] (q : α → ℝ) (c : ℝ) (hq : Integrable q μ) :
    |(⨍ x, q x ∂μ) - c| ≤ ⨍ x, |q x - c| ∂μ := by
  have h := pressure_average_l1_contraction μ q (fun _ => c)
    hq (integrable_const c)
  simpa only [average_const μ c] using h

end AverageL1

end ReservoirSeismicityControl
