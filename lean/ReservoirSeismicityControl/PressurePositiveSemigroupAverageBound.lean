import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl A5: boundedness of averaging a signed well rate

The approximation of a bounded measurable well rate by interval-step
functions should use cell averages rather than point samples. Pointwise
samples need not satisfy an essential-supremum bound (a representative
may be arbitrarily large on a null set).

This module proves the key bound for the average over ANY finite,
nonzero measure. In the time-cell application the measure is the
restriction of Lebesgue measure to the cell.

The L1 convergence of the resulting interval-step sequence and its
identification with the Bochner forcing remain separate steps.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Averaging an essentially bounded signed real function against a
nonzero finite measure preserves its absolute bound. The input can
have either sign. -/
theorem pressure_average_preserves_signed_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (q : α → ℝ) (M : ℝ)
    (hq : Integrable q μ)
    (hBound : ∀ᵐ x ∂μ, |q x| ≤ M) :
    |⨍ x, q x ∂μ| ≤ M := by
  have hUpperAE : ∀ᵐ x ∂μ, 0 ≤ M - q x := by
    filter_upwards [hBound] with x hx
    exact sub_nonneg.mpr (abs_le.mp hx).2
  have hLowerAE : ∀ᵐ x ∂μ, 0 ≤ M + q x := by
    filter_upwards [hBound] with x hx
    have h := (abs_le.mp hx).1
    linarith
  have hUpper : 0 ≤ ⨍ x, M - q x ∂μ :=
    average_nonneg_of_ae hUpperAE
  have hLower : 0 ≤ ⨍ x, M + q x ∂μ :=
    average_nonneg_of_ae hLowerAE
  rw [average_fun_sub (integrable_const M) hq, average_const μ M] at hUpper
  rw [average_fun_add (integrable_const M) hq, average_const μ M] at hLower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ReservoirSeismicityControl
