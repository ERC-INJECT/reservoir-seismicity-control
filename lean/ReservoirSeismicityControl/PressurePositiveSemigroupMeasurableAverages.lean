import ReservoirSeismicityControl.PressurePositiveSemigroupUniformAverages
import ReservoirSeismicityControl.PressurePositiveSemigroupPartitionComparison

/-!
# ReservoirSeismicityControl A5: L1 convergence of averages for measurable well rates

The previous modules provide the two substantive ingredients:
* uniform L1 density of uniformly continuous functions on a regular measure;
* shrinking-cell convergence of averages of a uniformly continuous function.

The partition-comparison theorem now gives convergence for **every integrable**
real-valued rate, hence for essentially bounded measurable rates on a
finite regular time measure.

The hypotheses `hCover` and `hDom` make the relation between the cell
measures and the original measure explicit. They hold for a genuine finite
partition of a time interval; proving this for the chosen actual intervals
is a separate, geometric formalization task.

No temporal derivative, spectral basis, compact resolvent, or weak subsequence
is required.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- For any integrable signed rate, finite cell-average approximations
converge in the summed L1 error as the cell radius tends to zero.

The cells have fixed total mass, cover the original finite measure, and are
dominated by it; the last two conditions are automatic for genuine disjoint
measurable partition cells. -/
theorem pressure_partition_integrable_average_l1_tendsto
    (μ₀ : Measure ℝ) [μ₀.Regular] [IsFiniteMeasure μ₀]
    (n : ℕ → ℕ)
    (μ : ∀ k, Fin (n k) → Measure ℝ)
    (hFinite : ∀ k i, IsFiniteMeasure (μ k i))
    (hNonzero : ∀ k i, NeZero (μ k i))
    (hCover : ∀ k, (∑ i : Fin (n k), μ k i) = μ₀)
    (hDom : ∀ k i, μ k i ≤ μ₀)
    (q : ℝ → ℝ) (hq : Integrable q μ₀)
    (centers : ∀ k, Fin (n k) → ℝ)
    (mesh : ℕ → ℝ)
    (hRadius : ∀ k i, ∀ᵐ x ∂(μ k i), dist x (centers k i) ≤ mesh k)
    (T : ℝ)
    (hMass : ∀ k, (∑ i : Fin (n k), (μ k i).real Set.univ) = T)
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) := by
  have hqCells (k : ℕ) (i : Fin (n k)) : Integrable q (μ k i) :=
    hq.mono_measure (hDom k i)
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨g, hgUC, _hgSupport, hgInt, hgApprox⟩ :=
    pressure_integrable_uniform_l1_density μ₀ q hq hε8
  have hgCells (k : ℕ) (i : Fin (n k)) : Integrable g (μ k i) :=
    hgInt.mono_measure (hDom k i)
  have hAvgG : Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) :=
    pressure_partition_uniform_average_l1_tendsto
      n μ hFinite hNonzero g hgUC centers mesh hRadius T hMass hgCells hMesh
  have hEv : ∀ᶠ k in atTop,
      (∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i)) < ε / 8 :=
    hAvgG.eventually (Iio_mem_nhds hε8)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEv
  refine ⟨N, ?_⟩
  intro k hk
  have hIntCell (i : Fin (n k)) :
      Integrable (fun x => |q x - g x|) (μ k i) :=
    ((hqCells k i).sub (hgCells k i)).abs
  have hErrCover :
      (∑ i : Fin (n k), ∫ x, |q x - g x| ∂(μ k i)) =
        ∫ x, |q x - g x| ∂μ₀ := by
    calc
      (∑ i : Fin (n k), ∫ x, |q x - g x| ∂(μ k i)) =
          ∫ x, |q x - g x| ∂(∑ i : Fin (n k), μ k i) := by
            exact (integral_finsetSum_measure (fun i _ => hIntCell i)).symm
      _ = ∫ x, |q x - g x| ∂μ₀ := by rw [hCover k]
  have hEstimate :
      (∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i)) ≤
      2 * ((∫ x, |q x - g x| ∂μ₀) +
        (∑ i : Fin (n k),
          ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i))) := by
    have h := pressure_partition_integral_oscillation_of_l1_comparator
      (μ k) (hFinite k) (hNonzero k) q g
      (fun i => ⨍ x, g x ∂(μ k i))
      (hqCells k) (hgCells k)
    rw [hErrCover] at h
    exact h
  have hSmallG := hN k hk
  have hNonneg : (0 : ℝ) ≤
      (∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i)) := by
    apply Finset.sum_nonneg
    intro i hi
    apply integral_nonneg
    intro x
    exact abs_nonneg _
  have hSmall :
      (∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i)) < ε := by
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using hSmall

/-- The preceding theorem applies to all essentially bounded measurable
signed rates on a finite regular measure. No bound on their derivative is used. -/
theorem pressure_partition_bounded_measurable_average_l1_tendsto
    (μ₀ : Measure ℝ) [μ₀.Regular] [IsFiniteMeasure μ₀]
    (n : ℕ → ℕ)
    (μ : ∀ k, Fin (n k) → Measure ℝ)
    (hFinite : ∀ k i, IsFiniteMeasure (μ k i))
    (hNonzero : ∀ k i, NeZero (μ k i))
    (hCover : ∀ k, (∑ i : Fin (n k), μ k i) = μ₀)
    (hDom : ∀ k i, μ k i ≤ μ₀)
    (q : ℝ → ℝ) (hq : AEStronglyMeasurable q μ₀)
    (M : ℝ) (hBound : ∀ᵐ x ∂μ₀, |q x| ≤ M)
    (centers : ∀ k, Fin (n k) → ℝ)
    (mesh : ℕ → ℝ)
    (hRadius : ∀ k i, ∀ᵐ x ∂(μ k i), dist x (centers k i) ≤ mesh k)
    (T : ℝ)
    (hMass : ∀ k, (∑ i : Fin (n k), (μ k i).real Set.univ) = T)
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) := by
  have hInt : Integrable q μ₀ :=
    Integrable.of_bound hq M (by
      simpa only [Real.norm_eq_abs] using hBound)
  exact pressure_partition_integrable_average_l1_tendsto
    μ₀ n μ hFinite hNonzero hCover hDom q hInt
    centers mesh hRadius T hMass hMesh

end ReservoirSeismicityControl
