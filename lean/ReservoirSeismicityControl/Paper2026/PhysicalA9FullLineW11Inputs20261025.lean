import ReservoirSeismicityControl.Paper2026.PhysicalA9ProjectedVectorPositiveL1_20261025
import Mathlib.Tactic

/-!
# A9 physical full-line kernel and bounded-flux Bochner applicability

The previously PASSED physical positive-lag result proves the projected
Neumann kernel and its derivative lie in L1 on (0, infinity), vanish on
nonpositive times, and have the correct positive-lag derivative and trace.

This module removes the separate full-line convolution-integrability
premises for the ACTUAL projected kernels: first convert positive-lag L1
to whole-line L1 using the proved zero extension, then reflect about any
observation time using Lebesgue measure preservation, and multiply by
measurable bounded physical well fluxes. No Q derivative is used.

Smooth W1,1 density, causal generator compatibility, and the final physical
four-term A9 identification remain separate obligations. These results do
NOT silently assert the weak W1,1 derivative or smooth approximation.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 2000000

/-- A causal zero extension integrable on positive lags is integrable on
all of real time. This allows the physical positive-lag DG envelope to be
used with the already proved *full-line* vector-convolution theorem. -/
theorem paper_A9_causal_positive_L1_to_full_line
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (k : ℝ → Lp ℝ 2 μ)
    (hPos : Integrable k
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
    (hZero : ∀ s : ℝ, s ≤ 0 → k s = 0) :
    Integrable k (volume : Measure ℝ) := by
  have hIndicator : Integrable
      ((Set.Ioi (0 : ℝ)).indicator k) (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hPos
  have hEq : (Set.Ioi (0 : ℝ)).indicator k = k := by
    funext s
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs)]
    · have hnot : s ∉ Set.Ioi (0 : ℝ) := hs
      rw [Set.indicator_of_notMem hnot]
      exact (hZero s (le_of_not_gt hs)).symm
  simpa only [hEq] using hIndicator

/-- Reflection about observation time preserves whole-line Bochner L1,
even for an L2-valued, noncompact causal Neumann kernel. -/
theorem paper_A9_full_line_L1_reflected
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (k : ℝ → Lp ℝ 2 μ)
    (hk : Integrable k (volume : Measure ℝ)) (t : ℝ) :
    Integrable (fun s : ℝ => k (t - s)) (volume : Measure ℝ) := by
  exact ((volume : Measure ℝ).measurePreserving_sub_left t).integrable_comp_of_integrable hk

/-- Physical A1 (bounded measurable flux) times a globally integrable
vector kernel gives a legitimate Bochner convolution at every observation
time. This is the L2-vector version, not merely a scalar A8 statement. -/
theorem paper_A9_bounded_flux_times_full_line_L1
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : ℝ → ℝ) (k : ℝ → Lp ℝ 2 μ)
    (hqMeas : AEStronglyMeasurable q (volume : Measure ℝ))
    (hk : Integrable k (volume : Measure ℝ))
    (M : ℝ) (hqBound : ∀ s : ℝ, |q s| ≤ M)
    (t : ℝ) :
    Integrable (fun s : ℝ => q s • k (t - s))
      (volume : Measure ℝ) := by
  have hReflect : Integrable (fun s : ℝ => k (t - s))
      (volume : Measure ℝ) :=
    paper_A9_full_line_L1_reflected μ k hk t
  have hMeas : AEStronglyMeasurable
      (fun s : ℝ => q s • k (t - s)) (volume : Measure ℝ) :=
    hqMeas.smul hReflect.aestronglyMeasurable
  have hM : 0 ≤ M :=
    (abs_nonneg (q 0)).trans (hqBound 0)
  have hDom : ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
      ‖q s • k (t - s)‖ ≤ M * ‖k (t - s)‖ := by
    filter_upwards [] with s
    have hs : |q s| * ‖k (t - s)‖ ≤ M * ‖k (t - s)‖ :=
      mul_le_mul_of_nonneg_right (hqBound s) (norm_nonneg _)
    simpa only [norm_smul, Real.norm_eq_abs] using hs
  exact (hReflect.norm.const_mul M).mono' hMeas hDom

/-- A complete *physical* full-line L1/Bochner certificate for the two
projected Neumann kernels, obtained from the same physical positive-lag
orbits, second-order terms, DG envelopes, and measurable A1 well fluxes.

Unlike the earlier W11 manifold-level interface, this statement does not
assume the integrability of either convolution. Its output supplies those
premises to the PASSED four-term A9 theorem. The generic Banach W11 density
application is still to be instantiated. -/
theorem paper_A9_physical_projected_vector_full_line_certificate
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ}
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (B₀ B₁ : Fin m → ℝ → ℝ)
    (hB₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₀ j lag)
    (hB₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₁ j lag)
    (hDG₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))‖
        ≤ B₀ j lag)
    (hDG₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag)‖
        ≤ B₁ j lag)
    (hB₀Int : ∀ j : Fin m,
      Integrable (B₀ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₁Int : ∀ j : Fin m,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₀Zero : ∀ j : Fin m,
      Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hOrbitMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSecondMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (qext : Fin m → ℝ → ℝ)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (qext j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |qext j s| ≤ M j) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      else 0
    let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    (∀ j : Fin m, Integrable (kernel j) (volume : Measure ℝ)) ∧
    (∀ j : Fin m, Integrable (rate j) (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => qext j s • kernel j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => qext j s • rate j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt (kernel j) (rate j lag) lag) ∧
    (∀ j : Fin m, Tendsto (kernel j)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Lp ℝ 2 μ))) ∧
    (∀ (j : Fin m) (lag : ℝ), lag ≤ 0 →
      kernel j lag = 0 ∧ rate j lag = 0) := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  change
    (∀ j : Fin m, Integrable (kernel j) (volume : Measure ℝ)) ∧
    (∀ j : Fin m, Integrable (rate j) (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => qext j s • kernel j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => qext j s • rate j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt (kernel j) (rate j lag) lag) ∧
    (∀ j : Fin m, Tendsto (kernel j)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Lp ℝ 2 μ))) ∧
    (∀ (j : Fin m) (lag : ℝ), lag ≤ 0 →
      kernel j lag = 0 ∧ rate j lag = 0)
  obtain ⟨hDeriv, hPosKernel, hPosRate, hTrace, hZero⟩ :=
    paper_A9_physical_vector_kernel_positive_L1_from_DG
      μ far hfar V E hsep orbit second hOrbit
      B₀ B₁ hB₀ hB₁ hDG₀ hDG₁
      hB₀Int hB₁Int hB₀Zero hOrbitMeas hSecondMeas
  have hGlobalKernel (j : Fin m) :
      Integrable (kernel j) (volume : Measure ℝ) :=
    paper_A9_causal_positive_L1_to_full_line μ (kernel j)
      (hPosKernel j) (fun lag hlag => (hZero j lag hlag).1)
  have hGlobalRate (j : Fin m) :
      Integrable (rate j) (volume : Measure ℝ) :=
    paper_A9_causal_positive_L1_to_full_line μ (rate j)
      (hPosRate j) (fun lag hlag => (hZero j lag hlag).2)
  refine ⟨hGlobalKernel, hGlobalRate, ?_, ?_, hDeriv, hTrace, hZero⟩
  · intro j t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (qext j)
      (kernel j) (hqMeas j) (hGlobalKernel j) (M j) (hqBound j) t
  · intro j t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (qext j)
      (rate j) (hqMeas j) (hGlobalRate j) (M j) (hqBound j) t

#print axioms paper_A9_causal_positive_L1_to_full_line
#print axioms paper_A9_full_line_L1_reflected
#print axioms paper_A9_bounded_flux_times_full_line_L1
#print axioms paper_A9_physical_projected_vector_full_line_certificate

end ReservoirSeismicityControl.Paper2026
