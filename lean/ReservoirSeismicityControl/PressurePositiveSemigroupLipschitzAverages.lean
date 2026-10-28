import ReservoirSeismicityControl.PressurePositiveSemigroupPartitionOscillation
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# ReservoirSeismicityControl (A5): convergence of cell averages for Lipschitz rates

This result establishes an actual L1 convergence theorem, not merely a
conditional comparator criterion. The cells are represented by finite,
nonzero measures; an essential bound on their radius and a fixed total
measure are hypotheses. Interval-restriction measures from a genuine
partition of a bounded time interval satisfy these properties.

A Lipschitz signed rate need not be differentiable. Arbitrary L1 rates
will be handled later by density of Lipschitz comparison functions.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- The L1 error of averaging a Lipschitz rate on shrinking cells tends to
zero. In a time partition, `centers k i` can be any point of the ith cell,
`mesh k` its maximal radius, and `T` the total interval length.

This theorem assumes the cell measures have fixed total mass and are
concentrated (a.e.) in balls of radius `mesh k` about the chosen centers.
It does not yet construct those measures from intervals. -/
theorem pressure_partition_lipschitz_average_l1_tendsto
    (n : ℕ → ℕ)
    (μ : ∀ k, Fin (n k) → Measure ℝ)
    (hFinite : ∀ k i, IsFiniteMeasure (μ k i))
    (hNonzero : ∀ k i, NeZero (μ k i))
    (q : ℝ → ℝ) (K : NNReal) (hLip : LipschitzWith K q)
    (centers : ∀ k, Fin (n k) → ℝ)
    (mesh : ℕ → ℝ)
    (hRadius : ∀ k i, ∀ᵐ x ∂(μ k i), dist x (centers k i) ≤ mesh k)
    (T : ℝ)
    (hMass : ∀ k, (∑ i : Fin (n k), (μ k i).real Set.univ) = T)
    (hq : ∀ k i, Integrable q (μ k i))
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) := by
  have hClose (k : ℕ) (i : Fin (n k)) :
      ∀ᵐ x ∂(μ k i),
        |q x - q (centers k i)| ≤ (K : ℝ) * mesh k := by
    filter_upwards [hRadius k i] with x hx
    have hL := hLip.dist_le_mul x (centers k i)
    have hR := mul_le_mul_of_nonneg_left hx K.coe_nonneg
    have hLE : |q x - q (centers k i)| ≤
        (K : ℝ) * dist x (centers k i) := by
      simpa only [Real.dist_eq] using hL
    exact hLE.trans hR
  have hUpper (k : ℕ) :
      (∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i)) ≤
      2 * ((K : ℝ) * mesh k) * T := by
    have h := pressure_partition_integral_oscillation_of_ae_close
      (μ k) (hFinite k) (hNonzero k)
      q (fun i => q (centers k i)) ((K : ℝ) * mesh k)
      (hq k) (hClose k)
    rw [hMass k] at h
    exact h
  have hLower (k : ℕ) :
      0 ≤ ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ k i))| ∂(μ k i) := by
    apply Finset.sum_nonneg
    intro i hi
    apply integral_nonneg
    intro x
    exact abs_nonneg _
  have hMajor :
      Tendsto (fun k : ℕ => 2 * ((K : ℝ) * mesh k) * T)
        atTop (𝓝 0) := by
    have hAux :
        Tendsto (fun k : ℕ => (2 * (K : ℝ)) * mesh k * T)
          atTop (𝓝 ((2 * (K : ℝ)) * 0 * T)) :=
      (tendsto_const_nhds.mul hMesh).mul tendsto_const_nhds
    simpa only [mul_zero, zero_mul, mul_assoc] using hAux
  exact squeeze_zero hLower hUpper hMajor

end ReservoirSeismicityControl
