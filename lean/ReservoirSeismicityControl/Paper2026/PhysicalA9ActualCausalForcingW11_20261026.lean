import ReservoirSeismicityControl.Paper2026.PhysicalA9CausalSemigroupFromDensity20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9ApproximationTranslation20261025
import Mathlib.Tactic

/-!
# Appendix A.3: actual causal pressure-forcing derivative and UNIFORM rate bound

This closes the forcing-specific input used by the global A9 / A10 theorems:
`hForcingDerivative` is proved rather than assumed, and the corresponding
`hFBound` is derived from the physical projected second-order kernel's L1 mass.
The physical finite-interval integral is identified with the full-line
zero-extended W1,1 convolution on every positive-time neighborhood.
No bounded time derivative of Q and no differentiability of the desired
causal forcing appear among the hypotheses.

Inputs B0/B1, positive-lag DG estimates, local flux measurability, and the
cited universal Banach W1,1 density theorem are exactly those of the
PREVIOUSLY PASSED projected-vector convolution theorem.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology
set_option maxHeartbeats 2000000

/-- The finite A5 causal forcing inherits the global W1,1 derivative and a
uniform norm bound from the physical far-projected positive-lag Neumann
kernel. The rate is the actual zero-extended second-generator convolution.
The constant is the bounded well flux times the whole-line L1 kernel mass. -/
theorem paper_A9_actual_causal_forcing_derivative_and_uniform_rate
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
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
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag)‖ ≤ B₁ j lag)
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
    (Q qext : Fin m → ℝ → ℝ)
    (hQext : ∀ j s, qext j s = if 0 ≤ s then Q j s else 0)
    (hqLoc : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (qext j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |qext j s| ≤ M j)
    (hDensity : PaperA9BanachW11Density μ) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    let forcing : ℝ → Lp ℝ 2 μ := fun t =>
      ∑ j : Fin m, ∫ s in (0 : ℝ)..t, Q j s •
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
    let forcingRate : ℝ → Lp ℝ 2 μ := fun t =>
      ∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)
    let Cf : ℝ :=
      ∑ j : Fin m, M j * (∫ lag : ℝ, ‖rate j lag‖)
    (∀ t : ℝ, 0 < t → HasDerivAt forcing (forcingRate t) t) ∧
    (∀ t : ℝ, ‖forcingRate t‖ ≤ Cf) := by
  classical
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  let forcing : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s in (0 : ℝ)..t, Q j s •
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
  let fullConvolution : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s : ℝ, qext j s • kernel j (t - s)
  let forcingRate : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)
  let Cf : ℝ := ∑ j : Fin m, M j * (∫ lag : ℝ, ‖rate j lag‖)
  change (∀ t : ℝ, 0 < t → HasDerivAt forcing (forcingRate t) t) ∧
    (∀ t : ℝ, ‖forcingRate t‖ ≤ Cf)
  have hFullDerivative : ∀ t : ℝ,
      HasDerivAt fullConvolution (forcingRate t) t := by
    exact paper_A9_physical_projected_convolution_rate_from_DG_and_density
      μ far hfar V E hsep orbit second hOrbit B₀ B₁
      hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas qext hqLoc hqMeas M hqBound hDensity
  have hKernelPos (j : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      kernel j lag = P
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)) := by
    simp only [kernel, if_pos hlag]
  have hKernelZero (j : Fin m) (lag : ℝ) (hlag : lag ≤ 0) :
      kernel j lag = 0 := by
    simp only [kernel, if_neg (not_lt.mpr hlag)]
  have hCausal (t : ℝ) (ht : 0 ≤ t) :
      fullConvolution t = forcing t := by
    exact paper_A9_vector_full_line_equals_physical_causal μ Q qext kernel
      (fun j lag => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
        (orbit j lag))) hQext hKernelPos hKernelZero t ht
  obtain ⟨_hKernelInt, hRateInt, _hValConvInt, hRateConvInt,
    _hKernelDeriv, _hKernelTrace, _hZero⟩ :=
      paper_A9_physical_projected_vector_full_line_certificate
        μ far hfar V E hsep orbit second hOrbit B₀ B₁
        hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
        hOrbitMeas hSecondMeas qext hqMeas M hqBound
  constructor
  · intro t ht
    have hLocal : forcing =ᶠ[𝓝 t] fullConvolution := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
      exact (hCausal τ hτ.le).symm
    exact (hFullDerivative t).congr_of_eventuallyEq hLocal
  · intro t
    have hEach (j : Fin m) :
        ‖∫ s : ℝ, qext j s • rate j (t - s)‖ ≤
          M j * (∫ lag : ℝ, ‖rate j lag‖) := by
      have hRef := paper_A9_full_line_L1_reflected μ (rate j) (hRateInt j) t
      have hDom : ∀ᵐ s : ℝ ∂volume,
          ‖qext j s • rate j (t - s)‖ ≤
            M j * ‖rate j (t - s)‖ := by
        filter_upwards [] with s
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hqBound j s) (norm_nonneg _)
      have hBound :
          ‖∫ s : ℝ, qext j s • rate j (t - s)‖ ≤
            M j * (∫ s : ℝ, ‖rate j (t - s)‖) := by
        simpa only [integral_const_mul] using
          (norm_integral_le_of_norm_le
            (hRef.norm.const_mul (M j)) hDom)
      calc
        ‖∫ s : ℝ, qext j s • rate j (t - s)‖ ≤
            M j * (∫ s : ℝ, ‖rate j (t - s)‖) := hBound
        _ = M j * (∫ lag : ℝ, ‖rate j lag‖) := by
          rw [paper_A9_whole_line_reflected_integral
            (fun lag : ℝ => ‖rate j lag‖) t]
    calc
      ‖forcingRate t‖ ≤
          ∑ j : Fin m, ‖∫ s : ℝ, qext j s • rate j (t - s)‖ := by
            exact norm_sum_le _ _
      _ ≤ Cf := by
        dsimp only [Cf]
        apply Finset.sum_le_sum
        intro j _
        exact hEach j

#print axioms paper_A9_actual_causal_forcing_derivative_and_uniform_rate
end ReservoirSeismicityControl.Paper2026
