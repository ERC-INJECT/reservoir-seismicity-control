import ReservoirSeismicityControl.Paper2026.PositiveSRNearFarSplit
import ReservoirSeismicityControl.PaperFarWeakNeumannKernel
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 — the actual smooth-complement far SR kernel

The manuscript uses the *same normalized SR observation weight* for near
and far diffusion. Its far weight is `(1-ζ)w`, not the characteristic-function
projection in the older far-kernel module. This file connects the already
verified `paperSRFarDiffusionWeight` to the existing weak Neumann kernel.

The two different derivatives are kept distinct:
* in semigroup lag, with the observation weight frozen (A8);
* in observation time, at fixed lag, including the moving SR weight (A9).

The semigroup-orbit derivative is an external analytic-semigroup dependency.
The Davies--Gaffney estimates, positive separation of supports, the causal
integration-by-parts step, and the moving near-field weak derivative remain
open applicability obligations. No derivative of the well flux is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The *actual* normalized smooth far-field SR kernel, with the same
`(1 - ζ)w` as in the verified P3 near/far decomposition. -/
noncomputable def paperSRFarSmoothKernel
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (t : ℝ) (j : Fin n) (lag : ℝ) : ℝ :=
  ReservoirSeismicityControl.paperFarWeakNeumannKernel V E hsep
    (paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff) orbit t j lag

/-- The lag derivative of the manuscript's frozen-observation SR far kernel.
Only the semigroup-orbit differentiation supplied by cited semigroup theory
is used; the actual smooth far weight has already been identified in P3. -/
theorem paper_sr_far_smooth_kernel_lag_hasDerivAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (t : ℝ) (j : Fin n) (lag : ℝ)
    (hOrbit : HasDerivAt
      (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
      (-(second j lag)) lag) :
    HasDerivAt
      (paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
        cutoff V E hsep orbit t j)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t j lag) lag := by
  exact ReservoirSeismicityControl.paper_far_weak_neumann_kernel_hasDerivAt
    V E hsep (paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff) orbit second t j lag hOrbit

/-- At fixed semigroup lag, the kernel also varies with the *observation
weight*. This term is essential for (A9) when the signed SR field moves. -/
theorem paper_sr_far_smooth_kernel_observation_hasDerivAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (t : ℝ) (j : Fin n) (lag : ℝ)
    (hR : HasDerivAt R (Rdot t) t) :
    HasDerivAt
      (fun τ => paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit τ j lag)
      (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
          gamma10 R0star t -
         cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
           gamma10 R0star t),
         ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)⟫_ℝ) t := by
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff τ
  let wdot : Lp ℝ 2 μ :=
    paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
    cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)
  let v : Lp ℝ 2 μ :=
    ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)
  have hw : HasDerivAt w wdot t :=
    (paper_sr_diffusion_near_far_hasDerivAt μ region hregion
      Kγ R Rdot gamma10 R0star cutoff t hR).2
  have hinner : HasDerivAt (fun τ => (innerSL ℝ v) (w τ))
      ((innerSL ℝ v) wdot) t :=
    (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hw
  have hfun :
      (fun τ => ReservoirSeismicityControl.paperFarWeakNeumannKernel V E hsep w orbit τ j lag) =
      (fun τ => (innerSL ℝ v) (w τ)) := by
    funext τ
    change ⟪w τ, v⟫_ℝ = ⟪v, w τ⟫_ℝ
    exact (real_inner_comm (w τ) v).symm
  change HasDerivAt
    (fun τ => ReservoirSeismicityControl.paperFarWeakNeumannKernel V E hsep w orbit τ j lag)
    (⟪wdot, v⟫_ℝ) t
  rw [hfun]
  convert hinner using 1
  simp only [innerSL_apply_apply]
  exact (real_inner_comm wdot v).symm

/-- The observation-time identity holds a.e. at positive physical times
whenever the signed physical SR trajectory has the verified strong rate. -/
theorem paper_sr_far_smooth_kernel_observation_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hR : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), HasDerivAt R (Rdot t) t) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ∀ (j : Fin n) (lag : ℝ),
      HasDerivAt
        (fun τ => paperSRFarSmoothKernel μ region hregion Kγ R
          gamma10 R0star cutoff V E hsep orbit τ j lag)
        (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
            gamma10 R0star t -
           cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t),
           ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)⟫_ℝ) t := by
  filter_upwards [hR] with t ht j lag
  exact paper_sr_far_smooth_kernel_observation_hasDerivAt
    μ region hregion Kγ R Rdot gamma10 R0star cutoff
    V E hsep orbit t j lag ht

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_lag_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_smooth_kernel_observation_ae
