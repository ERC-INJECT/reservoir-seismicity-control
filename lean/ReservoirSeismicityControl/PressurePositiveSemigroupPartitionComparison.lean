import ReservoirSeismicityControl.PressurePositiveSemigroupPartitionOscillation

/-!
# ReservoirSeismicityControl A5: finite-partition comparison and L1 convergence criterion

The average of an integrable signed rate on a cell is within twice the
L1 distance to any cellwise constant. We refine that estimate by allowing
an integrable *comparison function* g:

  int |q - avg(q)| <= 2 * (int |q-g| + int |g-c|).

The finite-partition estimate then shows that the averaged rates converge
in L1 if (i) a fixed comparison function approximates the rate in the
partitioned L1 norm, and (ii) the comparison function has vanishing
cellwise oscillation against constants as the partitions refine.

This is a convergence CRITERION, not yet the construction of a refining
partition or the density theorem for continuous comparison functions.
Neither positivity nor differentiability of q is required.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

section CellComparison

variable {α : Type*} [MeasurableSpace α]

/-- L1 error of an averaged signed rate, compared with an arbitrary
integrable function g and an arbitrary scalar c. -/
theorem pressure_cell_integral_oscillation_of_l1_comparator
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (q g : α → ℝ) (c : ℝ)
    (hq : Integrable q μ) (hg : Integrable g μ) :
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
      2 * ((∫ x, |q x - g x| ∂μ) +
        (∫ x, |g x - c| ∂μ)) := by
  have hqc : Integrable (fun x => |q x - c|) μ :=
    (hq.sub (integrable_const c)).abs
  have hqg : Integrable (fun x => |q x - g x|) μ :=
    (hq.sub hg).abs
  have hgc : Integrable (fun x => |g x - c|) μ :=
    (hg.sub (integrable_const c)).abs
  have hTriangle :
      (∫ x, |q x - c| ∂μ) ≤
      (∫ x, |q x - g x| ∂μ) +
        (∫ x, |g x - c| ∂μ) := by
    rw [← integral_add hqg hgc]
    apply integral_mono hqc (hqg.add hgc)
    intro x
    exact abs_sub_le (q x) (g x) c
  calc
    (∫ x, |q x - (⨍ y, q y ∂μ)| ∂μ) ≤
        2 * (∫ x, |q x - c| ∂μ) :=
      pressure_cell_integral_oscillation_le_two_comparator μ q c hq
    _ ≤ 2 * ((∫ x, |q x - g x| ∂μ) +
        (∫ x, |g x - c| ∂μ)) :=
      mul_le_mul_of_nonneg_left hTriangle (by norm_num)

end CellComparison

section PartitionComparison

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- The comparison inequality summed over a finite collection of cells.
The measures can be interval restrictions with possibly different lengths. -/
theorem pressure_partition_integral_oscillation_of_l1_comparator
    (μ : ι → Measure α)
    (hFinite : ∀ i, IsFiniteMeasure (μ i))
    (hNonzero : ∀ i, NeZero (μ i))
    (q g : α → ℝ) (c : ι → ℝ)
    (hq : ∀ i, Integrable q (μ i))
    (hg : ∀ i, Integrable g (μ i)) :
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
      2 * ((∑ i : ι, ∫ x, |q x - g x| ∂(μ i)) +
        (∑ i : ι, ∫ x, |g x - c i| ∂(μ i))) := by
  calc
    (∑ i : ι, ∫ x, |q x - (⨍ y, q y ∂(μ i))| ∂(μ i)) ≤
        ∑ i : ι, 2 * ((∫ x, |q x - g x| ∂(μ i)) +
          (∫ x, |g x - c i| ∂(μ i))) := by
      apply Finset.sum_le_sum
      intro i hi
      letI : IsFiniteMeasure (μ i) := hFinite i
      letI : NeZero (μ i) := hNonzero i
      exact pressure_cell_integral_oscillation_of_l1_comparator
        (μ i) q g (c i) (hq i) (hg i)
    _ = 2 * ((∑ i : ι, ∫ x, |q x - g x| ∂(μ i)) +
        (∑ i : ι, ∫ x, |g x - c i| ∂(μ i))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

end PartitionComparison

section RefiningCriterion

variable {α : Type*} [MeasurableSpace α]

/-- A varying finite partition, whose cells may be represented by
restricted time measures. Under convergence of the comparator errors,
its signed cell averages converge in the summed L1 error. The comparison
functions g k are allowed to vary with the partition index, making
diagonal continuous-function approximations possible.

The theorem does NOT assert that these comparator hypotheses always hold.
Establishing them for the actual shrinking interval partitions uses
density of continuous functions in L1 and their uniform continuity. -/
theorem pressure_partition_average_l1_vanishes_of_comparator_errors
    (n : ℕ → ℕ)
    (μ : ∀ k, Fin (n k) → Measure α)
    (hFinite : ∀ k i, IsFiniteMeasure (μ k i))
    (hNonzero : ∀ k i, NeZero (μ k i))
    (q : α → ℝ) (g : ℕ → α → ℝ)
    (c : ∀ k, Fin (n k) → ℝ)
    (hq : ∀ k i, Integrable q (μ k i))
    (hg : ∀ k i, Integrable (g k) (μ k i))
    (hCompare : Tendsto
      (fun k => ∑ i : Fin (n k), ∫ x, |q x - g k x| ∂(μ k i))
      atTop (𝓝 0))
    (hSmallOscillation : Tendsto
      (fun k => ∑ i : Fin (n k), ∫ x, |g k x - c k i| ∂(μ k i))
      atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) := by
  have hMajor : Tendsto
      (fun k => 2 *
        ((∑ i : Fin (n k), ∫ x, |q x - g k x| ∂(μ k i)) +
          (∑ i : Fin (n k), ∫ x, |g k x - c k i| ∂(μ k i))))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (hCompare.add hSmallOscillation)) using 1 <;> simp
  have hLower (k : ℕ) :
      0 ≤ ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i) := by
    apply Finset.sum_nonneg
    intro i hi
    apply integral_nonneg
    intro x
    exact abs_nonneg _
  have hUpper (k : ℕ) :
      (∑ i : Fin (n k), ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i)) ≤
      2 * ((∑ i : Fin (n k), ∫ x, |q x - g k x| ∂(μ k i)) +
        (∑ i : Fin (n k), ∫ x, |g k x - c k i| ∂(μ k i))) :=
    pressure_partition_integral_oscillation_of_l1_comparator
      (μ k) (hFinite k) (hNonzero k) q (g k) (c k) (hq k) (hg k)
  exact squeeze_zero hLower hUpper hMajor

end RefiningCriterion

end ReservoirSeismicityControl
