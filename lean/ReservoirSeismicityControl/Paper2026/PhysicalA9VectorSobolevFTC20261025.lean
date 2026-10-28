import ReservoirSeismicityControl.Paper2026.PhysicalA9FullLineW11Inputs20261025
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical A9: the projected Neumann kernel satisfies the Banach-valued FTC

This is an ACTUAL consequence of the previously verified separated
Neumann-orbit derivative, the DG rate envelope, and the zero-lag trace.
In particular the zero-lag behavior is not silently replaced by a
strong-domain assumption on the physical well profile.

The Bochner FTC on (0,b) identifies the integral of the physical rate
with the actual causal vector kernel. This is the missing endpoint
absolute-continuity fact needed to apply the standard external
Banach-valued W^{1,1} smooth-density result. This file does NOT assume
W^{1,1} regularity or assert that the density theorem is already applied.
No assumption on the time derivative of the well flux is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 2000000

/-- Banach-valued FTC starting precisely at the zero-lag trace. Unlike an
interior FTC, this handles the physically singular Neumann generator at
lag zero by taking the established one-sided limit. -/
theorem paper_A9_positive_vector_FTC_from_zero_trace
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (k dk : ℝ → Lp ℝ 2 μ)
    (hDerivative : ∀ lag : ℝ, 0 < lag → HasDerivAt k (dk lag) lag)
    (hRateInt : Integrable dk (volume : Measure ℝ))
    (hTrace : Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 (0 : Lp ℝ 2 μ)))
    (b : ℝ) (hb : 0 < b) :
    (∫ lag in (0 : ℝ)..b, dk lag) = k b := by
  have hLeft : Tendsto k (𝓝[<] b) (𝓝 (k b)) :=
    (hDerivative b hb).continuousAt.continuousWithinAt
  have hFTC : (∫ lag in (0 : ℝ)..b, dk lag) =
      k b - (0 : Lp ℝ 2 μ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hb (fun x hx => hDerivative x hx.1)
      (hRateInt.intervalIntegrable) hTrace hLeft
  simpa using hFTC

/-- Standard Banach-valued FTC on any strictly positive lag interval. -/
theorem paper_A9_positive_vector_FTC_between_lags
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (k dk : ℝ → Lp ℝ 2 μ)
    (hDerivative : ∀ lag : ℝ, 0 < lag → HasDerivAt k (dk lag) lag)
    (hRateInt : Integrable dk (volume : Measure ℝ))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ lag in a..b, dk lag) = k b - k a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hDerivative x (lt_of_lt_of_le ha hx.1)
  · exact hRateInt.intervalIntegrable

/-- The ACTUAL projected Neumann vector kernel, rather than an arbitrary
Sobolev function, satisfies the zero-endpoint Bochner FTC. The hypotheses
are precisely the positive-lag Neumann orbit and off-diagonal estimates
already used in `paper_A9_physical_vector_kernel_positive_L1_from_DG`.
The full-line integrability of the derivative is constructed, not assumed. -/
theorem paper_A9_physical_projected_vector_FTC_from_DG
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
        (volume.restrict (Set.Ioi (0 : ℝ)))) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      else 0
    let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    ∀ j : Fin m, ∀ b : ℝ, 0 < b →
      (∫ lag in (0 : ℝ)..b, rate j lag) = kernel j b := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  change ∀ j : Fin m, ∀ b : ℝ, 0 < b →
    (∫ lag in (0 : ℝ)..b, rate j lag) = kernel j b
  obtain ⟨hDerivative, _hKernelPos, hRatePos, hTrace, hZero⟩ :=
    paper_A9_physical_vector_kernel_positive_L1_from_DG
      μ far hfar V E hsep orbit second hOrbit B₀ B₁
      hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas
  intro j b hb
  have hRateFull : Integrable (rate j) (volume : Measure ℝ) :=
    paper_A9_causal_positive_L1_to_full_line μ (rate j)
      (hRatePos j) (fun lag hlag => (hZero j lag hlag).2)
  exact paper_A9_positive_vector_FTC_from_zero_trace μ
    (kernel j) (rate j) (hDerivative j) hRateFull (hTrace j) b hb

#print axioms paper_A9_positive_vector_FTC_from_zero_trace
#print axioms paper_A9_positive_vector_FTC_between_lags
#print axioms paper_A9_physical_projected_vector_FTC_from_DG

end ReservoirSeismicityControl.Paper2026
