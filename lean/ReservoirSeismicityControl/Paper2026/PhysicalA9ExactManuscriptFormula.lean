import ReservoirSeismicityControl.Paper2026.PhysicalA9FinalAssembly
import ReservoirSeismicityControl.Paper2026.PhysicalA9InitialFluxCancellation
import ReservoirSeismicityControl.Paper2026.PhysicalA9LagDerivativeIdentification
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.Tactic

/-!
# Appendix A.3, exact four terms of (A9): physical compatibility assembly

This does NOT reconstruct a kernel, an elliptic generator, or a convolution
estimate. It connects the already proved moving-observation rate, initial-flux
cancellation, and physical frozen-weight lag-derivative identification.

The remaining strong projected L² convolution differentiation hypothesis is
*explicit* (`hForcingRate`): its applicability for the actual separated Neumann
semigroup and bounded Q is an external analytic-semigroup / W¹,¹ convolution
step. A passing build of this application alone must not be called unconditional
closure of (A9) from Assumptions 1--5.

The final scalar formula is exactly the manuscript's: moving weight, positive-
time homogeneous rate A exp(-tA) p_t(0), -K(t) Q(0), and the K' convolution.
No derivative or absolute continuity of Q is assumed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- Physical A9, with its *literal four terms*. `L t` is the positive-lag
bounded Neumann operator `A exp(-tA)`; `orbit j lag` represents the
positive-lag Neumann semigroup applied to the j-th well source. The sign of
the convolution follows from differentiation in the lag, not in observation
time. The resulting kernel derivative is certified in the first conjunct.

IMPORTANT: `hForcingRate` is still an EXTERNAL vector-valued W¹,¹
applicability obligation; it is not implied merely by scalar `K'∈L¹`.
The `hBochner` premise concerns the matching vector integrand. -/
theorem paper_A9_exact_physical_four_terms_from_existing_assembly
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
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
    (f : Fin m → Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ)
    (Ap0 pt0 : Lp ℝ 2 μ)
    (hInitial : pt0 = -Ap0 + ∑ j : Fin m, (Q j 0) • f j)
    (L : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hOrbitCompatibility : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        L t (f j) = ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j t))
    (Ap homogeneous forcing : ℝ → Lp ℝ 2 μ)
    (hPhysicalDecomposition : ∀ τ : ℝ,
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap τ) =
        homogeneous τ + forcing τ)
    (hHomogeneousRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt homogeneous
        (-(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
          (L t Ap0))) t)
    (hForcingRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing
        (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          (Q j s) • (-(ReservoirSeismicityControl.paperFarLpProjection μ
            {x : X | ζ x ≠ 1} hfar (second j (t - s))))) t)
    (hBochner : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        Integrable (fun s : ℝ => (Q j s) • (-(ReservoirSeismicityControl.paperFarLpProjection μ
          {x : X | ζ x ≠ 1} hfar (second j (t - s)))))
          (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hR : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t) :
    (∀ observation : ℝ, ∀ j : Fin m, ∀ lag : ℝ, 0 < lag →
      deriv (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit observation j) lag =
        ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second observation j lag) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t -
           cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t), Ap t⟫_ℝ +
         ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
           gamma10 R0star cutoff t, L t pt0⟫_ℝ -
         ∑ j : Fin m,
           paperSRFarSmoothKernel μ region hregion Kγ R
             gamma10 R0star cutoff V E hsep orbit t j t * Q j 0 +
         ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
           ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
             (paperSRFarDiffusionWeight μ region hregion Kγ R
               gamma10 R0star cutoff) second t j (t - s) * Q j s) t) := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff τ
  let wd : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star τ -
      cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
        gamma10 R0star τ)
  let lag : ℝ → Fin m → ℝ → Lp ℝ 2 μ :=
    fun t j s => -(P (second j (t - s)))
  let frate : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s in (0 : ℝ)..t, (Q j s) • lag t j s
  have hRep : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      frate t = ∑ j : Fin m,
        ∫ s in (0 : ℝ)..t, (Q j s) • lag t j s :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt (fun τ => ⟪w τ, Ap τ⟫_ℝ)
        (⟪wd t, P (Ap t)⟫_ℝ +
         ⟪w t, -(P (L t Ap0))⟫_ℝ +
         ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
           Q j s * ⟪w t, lag t j s⟫_ℝ) t := by
    have h := paper_A9_final_physical_moving_SR_far_derivative_ae
      μ region hregion Kγ R Rdot gamma10 R0star cutoff ζ hfar hcutoff
      Q Ap homogeneous forcing (fun t => -(P (L t Ap0))) frate lag
      hPhysicalDecomposition hHomogeneousRate hForcingRate hRep hBochner hR
    exact h
  have hFixed : ∀ τ : ℝ, P (w τ) = w τ := by
    intro τ
    exact paper_sr_smooth_far_projection_nonunit_set
      μ region hregion Kγ R gamma10 R0star cutoff
      ζ hfar hcutoff τ
  have hWdFixed : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      P (wd t) = wd t := by
    filter_upwards [hR] with t hRt
    have hWDeriv : HasDerivAt w (wd t) t :=
      (paper_sr_diffusion_near_far_hasDerivAt
        μ region hregion Kγ R Rdot gamma10 R0star cutoff t hRt).2
    have hPDeriv : HasDerivAt (fun τ => P (w τ)) (P (wd t)) t :=
      P.hasFDerivAt.comp_hasDerivAt t hWDeriv
    have hFun : (fun τ => P (w τ)) = w := by
      funext τ
      exact hFixed τ
    rw [hFun] at hPDeriv
    exact hPDeriv.unique hWDeriv
  refine ⟨?_, ?_⟩
  · intro observation j lag0 hlag
    exact paper_A9_actual_SR_far_kernel_lag_deriv
      μ region hregion Kγ R gamma10 R0star cutoff V E hsep
      orbit second hOrbit observation j lag0 hlag
  · filter_upwards [hRate, hOrbitCompatibility, hWdFixed]
      with t hMain hCompat hWdot
    have hFirst : ⟪wd t, P (Ap t)⟫_ℝ = ⟪wd t, Ap t⟫_ℝ := by
      exact (ReservoirSeismicityControl.paper_far_projected_inner P
        (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
          μ {x : X | ζ x ≠ 1} hfar) (wd t) (Ap t) hWdot).symm
    have hKernel (j : Fin m) :
        ⟪w t, L t (f j)⟫_ℝ =
          paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t j t := by
      rw [hCompat j]
      rfl
    have hSumKernel :
        (∑ j : Fin m, ⟪w t, L t (f j)⟫_ℝ * Q j 0) =
        ∑ j : Fin m,
          paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t j t * Q j 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hKernel j]
    have hCancel := paper_A9_physical_SR_initial_flux_cancellation
      μ region hregion Kγ R gamma10 R0star cutoff
      m f (fun j => Q j 0) Ap0 pt0 hInitial (L t) t
    change -⟪w t, L t Ap0⟫_ℝ =
      ⟪w t, L t pt0⟫_ℝ -
        ∑ j : Fin m, ⟪w t, L t (f j)⟫_ℝ * Q j 0 at hCancel
    rw [hSumKernel] at hCancel
    have hSumRate :
        (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          Q j s * ⟪w t, lag t j s⟫_ℝ) =
        ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          ReservoirSeismicityControl.paperFarWeakNeumannKernelRate w second t j (t - s) * Q j s := by
      apply Finset.sum_congr rfl
      intro j _
      apply intervalIntegral.integral_congr
      intro s _
      change Q j s * ⟪w t, -(P (second j (t - s)))⟫_ℝ =
        (-⟪w t, second j (t - s)⟫_ℝ) * Q j s
      rw [inner_neg_right]
      have hSec := ReservoirSeismicityControl.paper_far_projected_inner P
        (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
          μ {x : X | ζ x ≠ 1} hfar)
        (w t) (second j (t - s)) (hFixed t)
      rw [←hSec]
      ring
    change HasDerivAt (fun τ => ⟪w τ, Ap τ⟫_ℝ)
      (⟪wd t, P (Ap t)⟫_ℝ +
       ⟪w t, -(P (L t Ap0))⟫_ℝ +
       ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
         Q j s * ⟪w t, lag t j s⟫_ℝ) t at hMain
    have hHomo := ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
        μ {x : X | ζ x ≠ 1} hfar)
      (w t) (L t Ap0) (hFixed t)
    rw [hFirst, inner_neg_right, ←hHomo, hCancel, hSumRate] at hMain
    -- The last rewrite uses `paperFarWeakNeumannKernelRate` as an alias
    -- for K'. The first conjunct certifies the identity for every lag>0.
    convert hMain using 1 <;> ring

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_exact_physical_four_terms_from_existing_assembly
