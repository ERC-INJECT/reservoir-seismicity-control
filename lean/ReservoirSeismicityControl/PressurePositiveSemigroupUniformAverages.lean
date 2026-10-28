import ReservoirSeismicityControl.PressurePositiveSemigroupUniformL1Density
import ReservoirSeismicityControl.PressurePositiveSemigroupPartitionComparison
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# ReservoirSeismicityControl (A5): convergence of averages for uniformly continuous rates

For a uniformly continuous real-valued rate, the total L1 error of
cellwise averaging tends to zero when the radius of each cell tends
to zero and the total measure of the cells remains fixed.

This generalizes the already verified Lipschitz-average theorem.
The cells are still abstract finite measures concentrated in shrinking
balls; the connection to actual interval restrictions is separate.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- Uniformly continuous signed rates have vanishing integrated error
under cellwise averaging on shrinking cells of fixed total measure.

No derivative of the rate is used. -/
theorem pressure_partition_uniform_average_l1_tendsto
    (n : ℕ → ℕ)
    (μ : ∀ k, Fin (n k) → Measure ℝ)
    (hFinite : ∀ k i, IsFiniteMeasure (μ k i))
    (hNonzero : ∀ k i, NeZero (μ k i))
    (g : ℝ → ℝ) (hUC : UniformContinuous g)
    (centers : ∀ k, Fin (n k) → ℝ)
    (mesh : ℕ → ℝ)
    (hRadius : ∀ k i, ∀ᵐ x ∂(μ k i), dist x (centers k i) ≤ mesh k)
    (T : ℝ)
    (hMass : ∀ k, (∑ i : Fin (n k), (μ k i).real Set.univ) = T)
    (hg : ∀ k i, Integrable g (μ k i))
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i))
      atTop (𝓝 0) := by
  have hT : 0 ≤ T := by
    calc
      (0 : ℝ) ≤ ∑ i : Fin (n 0), (μ 0 i).real Set.univ := by
        apply Finset.sum_nonneg
        intro i hi
        exact ENNReal.toReal_nonneg
      _ = T := hMass 0
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hTp : 0 < T + 1 := by linarith
  let η : ℝ := ε / (4 * (T + 1))
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 4) hTp)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hUC η hη
  have hEventually : ∀ᶠ k in atTop, mesh k < δ :=
    hMesh.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨N, ?_⟩
  intro k hkN
  have hk : mesh k < δ := hN k hkN
  have hClose (i : Fin (n k)) :
      ∀ᵐ x ∂(μ k i), |g x - g (centers k i)| ≤ η := by
    filter_upwards [hRadius k i] with x hx
    have hDist : dist x (centers k i) < δ := hx.trans_lt hk
    have hResult : dist (g x) (g (centers k i)) < η := hmod hDist
    simpa only [Real.dist_eq] using hResult.le
  have hUpper :
      (∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i)) ≤
        2 * η * T := by
    have h := pressure_partition_integral_oscillation_of_ae_close
      (μ k) (hFinite k) (hNonzero k)
      g (fun i => g (centers k i)) η (hg k) hClose
    rw [hMass k] at h
    exact h
  have hNonneg :
      (0 : ℝ) ≤ (∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i)) := by
    apply Finset.sum_nonneg
    intro i hi
    apply integral_nonneg
    intro x
    exact abs_nonneg _
  have hDen : T + 1 ≠ 0 := ne_of_gt hTp
  have hScale : 2 * η * T ≤ ε / 2 := by
    have hBound : T ≤ T + 1 := by linarith
    have hMon : 2 * η * T ≤ 2 * η * (T + 1) :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    have hId : 2 * η * (T + 1) = ε / 2 := by
      dsimp [η]
      field_simp [hDen]
      <;> ring
    linarith
  have hSmall :
      (∑ i : Fin (n k),
        ∫ x, |g x - (⨍ y, g y ∂(μ k i))| ∂(μ k i)) < ε := by
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using hSmall

end ReservoirSeismicityControl
