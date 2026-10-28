import ReservoirSeismicityControl.PressurePositiveSemigroupAverageL1

/-!
# ReservoirSeismicityControl A5: L1 oscillation of a signed cell average

For an integrable signed rate q on a cell with nonzero finite measure,

  average |q - average q| <= 2 * average |q - c|

for every constant c. Thus the cell-average projection has an explicit
local approximation estimate with no derivatives of q. In particular,
for continuous comparison functions, uniform continuity makes the
right-hand side small on sufficiently short time cells.

This module does NOT yet establish convergence of uniform-mesh averages
for all bounded measurable rates; a finite-partition summation and the
continuous-function density argument remain to be formalized.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

section AverageOscillation

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]

/-- A cell average approximates any signed integrable input in average
absolute error within factor two of the best constant comparator.
This applies to any nonzero finite measure, hence to Lebesgue measure
restricted to a nondegenerate time interval. -/
theorem pressure_average_oscillation_le_two_comparator
    (q : α → ℝ) (c : ℝ) (hq : Integrable q μ) :
    (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
      2 * (⨍ x, |q x - c| ∂μ) := by
  have hDiff : Integrable (fun x => |q x - c|) μ :=
    (hq.sub (integrable_const c)).abs
  have hOsc : Integrable (fun x => |q x - (⨍ y, q y ∂μ)|) μ :=
    (hq.sub (integrable_const (⨍ y, q y ∂μ))).abs
  have hPoint : ∀ x : α,
      |q x - (⨍ y, q y ∂μ)| ≤
      |q x - c| + |(⨍ y, q y ∂μ) - c| := by
    intro x
    calc
      |q x - (⨍ y, q y ∂μ)| ≤
          |q x - c| + |c - (⨍ y, q y ∂μ)| := abs_sub_le _ _ _
      _ = |q x - c| + |(⨍ y, q y ∂μ) - c| := by
        rw [abs_sub_comm c]
  -- Keep the pointwise subtraction as an explicit subtraction of functions.
  -- This allows `average_fun_sub` and `average_fun_add` to match directly.
  have hUpper :
      0 ≤ ⨍ x, (((fun z : α => |q z - c|) +
        (fun _ : α => |(⨍ y, q y ∂μ) - c|)) -
        (fun z : α => |q z - (⨍ y, q y ∂μ)|)) x ∂μ := by
    apply average_nonneg
    intro x
    change 0 ≤ (|q x - c| + |(⨍ y, q y ∂μ) - c|) -
      |q x - (⨍ y, q y ∂μ)|
    exact sub_nonneg.mpr (hPoint x)
  rw [average_sub (hDiff.add (integrable_const _)) hOsc,
    average_add hDiff (integrable_const _), average_const μ] at hUpper
  have hComparator := pressure_average_error_against_constant μ q c hq
  linarith


/-- If an integrable signed rate differs from one constant by at most
`δ` almost everywhere on a cell, then replacing it with its cell average
incurs average absolute error at most `2 * δ`. This is the form needed
when a continuous comparison function oscillates little on a short cell. -/
theorem pressure_average_oscillation_of_ae_close
    (q : α → ℝ) (c δ : ℝ) (hq : Integrable q μ)
    (hClose : ∀ᵐ x ∂μ, |q x - c| ≤ δ) :
    (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤ 2 * δ := by
  have hDiff : Integrable (fun x => |q x - c|) μ :=
    (hq.sub (integrable_const c)).abs
  have hUpper : 0 ≤ ⨍ x, δ - |q x - c| ∂μ := by
    apply average_nonneg_of_ae
    filter_upwards [hClose] with x hx
    exact sub_nonneg.mpr hx
  rw [average_fun_sub (integrable_const δ) hDiff,
    average_const μ] at hUpper
  have hOsc := pressure_average_oscillation_le_two_comparator μ q c hq
  linarith

end AverageOscillation

end ReservoirSeismicityControl
