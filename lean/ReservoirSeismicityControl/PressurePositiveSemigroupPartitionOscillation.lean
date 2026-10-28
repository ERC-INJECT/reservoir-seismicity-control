import ReservoirSeismicityControl.PressurePositiveSemigroupAverageOscillation

/-!
# ReservoirSeismicityControl A5: integrated oscillation bounds for a finite partition

A cell average has at most twice the L1 error of any constant competitor.
This file first converts the previously verified average bound into an
unnormalized Bochner/Lebesgue integral estimate and then sums it over a
finite family of cells, represented by their finite nonzero restriction
measures. Thus the result applies to Lebesgue measures restricted to
nondegenerate intervals, without needing a time derivative of the input.

This module does not prove that mesh averages converge in L1. That will
require showing that the cells form a genuine time partition, controlling
oscillation for continuous comparators, and density of such comparators.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators

section CellOscillation

variable {α : Type*} [MeasurableSpace α]

/-- The factor-two oscillation estimate in unnormalized L1 form.
    The cell is represented by its (finite, nonzero) restricted measure. -/
theorem pressure_cell_integral_oscillation_le_two_comparator
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (q : α → ℝ) (c : ℝ) (hq : Integrable q μ) :
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
      2 * (∫ x, |q x - c| ∂μ) := by
  have h := pressure_average_oscillation_le_two_comparator μ q c hq
  have hMassNonneg : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hScale :
      μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
        μ.real Set.univ * (2 * (⨍ x, |q x - c| ∂μ)) :=
    mul_le_mul_of_nonneg_left h hMassNonneg
  have hLeft :
      μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) =
        ∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ := by
    simpa only [smul_eq_mul] using
      (measure_smul_average μ (fun x : α => |q x - (⨍ y, q y ∂μ)|))
  have hRight :
      μ.real Set.univ * (⨍ x, |q x - c| ∂μ) =
        ∫ x, |q x - c| ∂μ := by
    simpa only [smul_eq_mul] using
      (measure_smul_average μ (fun x : α => |q x - c|))
  calc
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) =
        μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) := hLeft.symm
    _ ≤ μ.real Set.univ * (2 * (⨍ x, |q x - c| ∂μ)) := hScale
    _ = 2 * (μ.real Set.univ * (⨍ x, |q x - c| ∂μ)) := by ring
    _ = 2 * (∫ x, |q x - c| ∂μ) := by rw [hRight]

/-- The integrated approximation error if q differs by at most δ almost
    everywhere from a constant on a finite nonzero cell. -/
theorem pressure_cell_integral_oscillation_of_ae_close
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (q : α → ℝ) (c δ : ℝ) (hq : Integrable q μ)
    (hClose : ∀ᵐ x ∂μ, |q x - c| ≤ δ) :
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
      2 * δ * μ.real Set.univ := by
  have h := pressure_average_oscillation_of_ae_close μ q c δ hq hClose
  have hMassNonneg : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hScale :
      μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
        μ.real Set.univ * (2 * δ) :=
    mul_le_mul_of_nonneg_left h hMassNonneg
  have hLeft :
      μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) =
        ∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ := by
    simpa only [smul_eq_mul] using
      (measure_smul_average μ (fun x : α => |q x - (⨍ y, q y ∂μ)|))
  calc
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) =
        μ.real Set.univ * (⨍ x, |q x - (⨍ y, q y ∂μ)| ∂μ) := hLeft.symm
    _ ≤ μ.real Set.univ * (2 * δ) := hScale
    _ = 2 * δ * μ.real Set.univ := by ring

end CellOscillation

section FinitePartition

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- Sum of the unnormalized L1 errors of the cell averages, controlled
    by errors against arbitrary cellwise constants. Distinct cells are
    represented by restricted measures μ i; disjointness is not needed
    for this finite-sum inequality. -/
theorem pressure_partition_integral_oscillation_le_two_comparator
    (μ : ι → Measure α)
    (hFinite : ∀ i, IsFiniteMeasure (μ i))
    (hNonzero : ∀ i, NeZero (μ i))
    (q : α → ℝ) (c : ι → ℝ)
    (hq : ∀ i, Integrable q (μ i)) :
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
      2 * (∑ i : ι, ∫ x, |q x - c i| ∂(μ i)) := by
  calc
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
        ∑ i : ι, 2 * (∫ x, |q x - c i| ∂(μ i)) := by
          apply Finset.sum_le_sum
          intro i hi
          letI : IsFiniteMeasure (μ i) := hFinite i
          letI : NeZero (μ i) := hNonzero i
          exact pressure_cell_integral_oscillation_le_two_comparator
            (μ i) q (c i) (hq i)
    _ = 2 * (∑ i : ι, ∫ x, |q x - c i| ∂(μ i)) := by
      simp only [Finset.mul_sum]

/-- If each cell is δ-close to its chosen constant, the total
    approximation error is controlled by δ times the total measure. -/
theorem pressure_partition_integral_oscillation_of_ae_close
    (μ : ι → Measure α)
    (hFinite : ∀ i, IsFiniteMeasure (μ i))
    (hNonzero : ∀ i, NeZero (μ i))
    (q : α → ℝ) (c : ι → ℝ) (δ : ℝ)
    (hq : ∀ i, Integrable q (μ i))
    (hClose : ∀ i, ∀ᵐ x ∂(μ i), |q x - c i| ≤ δ) :
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
      2 * δ * (∑ i : ι, (μ i).real Set.univ) := by
  calc
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
        ∑ i : ι, 2 * δ * (μ i).real Set.univ := by
          apply Finset.sum_le_sum
          intro i hi
          letI : IsFiniteMeasure (μ i) := hFinite i
          letI : NeZero (μ i) := hNonzero i
          exact pressure_cell_integral_oscillation_of_ae_close
            (μ i) q (c i) δ (hq i) (hClose i)
    _ = 2 * δ * (∑ i : ι, (μ i).real Set.univ) := by
      simp only [Finset.mul_sum]

end FinitePartition

end ReservoirSeismicityControl
