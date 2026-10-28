import ReservoirSeismicityControl.Paper2026.PhysicalA9ScalarKernelIdentification
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9BoundedFlux
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothKernel
import Mathlib.Tactic

/-!
# Appendix A.3 / (A8)--(A9): actual physical SR kernel's L¹ lag derivative

The previous physical causal result was scalarized for the *actual* signed SR
far observation. The published A8 estimate and the archived bounded-flux
convolution lemma use a separate rate kernel. This file identifies it with
`deriv` of the actual frozen-observation-time smooth SR kernel on positive lags.

This imports and APPLIES the existing A8 L¹ result and bounded-flux convolution
theorem; the abstract semigroup orbit differentiation remains an explicitly
cited positive-lag analytic-semigroup input. `hRateInt` below is precisely the
A8 L¹ result (already derived in PositiveSRFarA8L1 from the cited off-diagonal
estimate); it is NOT an assumption of the desired convolution identity.

Crucially, there is no claim of differentiability at lag zero or of the
actual moving observation (A9) yet. No time derivative of the well rate Q.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Identify `deriv K_{j,t}` with the physical second semigroup kernel on
strictly positive lags. This is the missing *actual kernel* interface between
the published semigroup orbit identity and A8's `K'` bound. -/
theorem paper_A9_actual_SR_far_kernel_lag_deriv
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ} (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (observation : ℝ) (j : Fin m) (lag : ℝ) (hlag : 0 < lag) :
    deriv (paperSRFarSmoothKernel μ region hregion Kγ R
      gamma10 R0star cutoff V E hsep orbit observation j) lag =
      ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second observation j lag := by
  exact (paper_sr_far_smooth_kernel_lag_hasDerivAt
    μ region hregion Kγ R gamma10 R0star cutoff V E hsep orbit second
    observation j lag (hOrbit j lag hlag)).deriv

/-- The SAME actual SR far kernel has an integrable lag derivative on
positive lags, and its convolution against a bounded measurable well rate
is well defined. The A8 rate-kernel integrability hypothesis can be
instantiated by the ALREADY PROVED `paper_sr_smooth_far_A8_lag_rate_integrable`.
The upper bound is the original positive-lag L¹ mass; no Qdot occurs. -/
theorem paper_A9_actual_SR_far_kernel_deriv_L1_and_flux
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ} (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (observation : ℝ)
    (hRateInt : ∀ j : Fin m,
      Integrable
        (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second observation j)
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (Q : Fin m → ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hQmeas : ∀ j : Fin m,
      AEStronglyMeasurable (Q j) (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hQ : ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), |Q j s| ≤ M j) :
    (∀ j : Fin m,
      Integrable
        (fun lag => deriv (paperSRFarSmoothKernel μ region hregion Kγ R
          gamma10 R0star cutoff V E hsep orbit observation j) lag)
        (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∀ j : Fin m,
      let k := ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second observation j
      Integrable (fun s => k (t - s) * Q j s)
        (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
      |∫ s in Set.Ioc (0 : ℝ) t, k (t - s) * Q j s| ≤
        M j * (∫ lag in Set.Ioi (0 : ℝ), |k lag|)) := by
  let k : Fin m → ℝ → ℝ := fun j =>
    ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff) second observation j
  have hDeriv (j : Fin m) :
      (fun lag : ℝ => deriv (paperSRFarSmoothKernel μ region hregion
        Kγ R gamma10 R0star cutoff V E hsep orbit observation j) lag)
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] (k j) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
    exact paper_A9_actual_SR_far_kernel_lag_deriv
      μ region hregion Kγ R gamma10 R0star cutoff V E hsep orbit second
      hOrbit observation j lag hlag
  have hInt (j : Fin m) :
      Integrable
        (fun lag : ℝ => deriv (paperSRFarSmoothKernel μ region hregion
          Kγ R gamma10 R0star cutoff V E hsep orbit observation j) lag)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (hRateInt j).congr (hDeriv j).symm
  have hConv := ReservoirSeismicityControl.Paper2026.paper_A9_bounded_causal_flux_from_positive_L1
    k Q t ht M hM (fun j => hRateInt j) hQmeas hQ
  exact ⟨hInt, hConv⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_SR_far_kernel_lag_deriv
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_SR_far_kernel_deriv_L1_and_flux
