import Mathlib
import ReservoirSeismicityControl.Theorems
import ReservoirSeismicityControl.Demand
import ReservoirSeismicityControl.PressurePhysicalTensorEntries

/-!
# Theorems 1 and 2: quantitative bridge to the manuscript proofs

Source: `NLD_2026(9).tex`, Appendix A.3--A.4 and Appendix B.

This module does not assume the desired bound on the NORMALIZED perturbation.
It derives it from bounded pieces of the regional perturbation derivative,
bounded inverse-gain action and bounded gain derivative, using the exact
inverse-gain differentiation identity from Appendix A.4 / Appendix B.

The substantial PDE assertions are explicit inputs: the near/far kernel,
SR reaction and reference-term estimates, and bounded unnormalized Psi.
The inverse-gain action bound and the inverse differentiation identity are
also explicit hypotheses. In particular, this is not a proof that A1--A6
imply those hypotheses. The external MIMO super-twisting stability theorem
is NOT formalized or asserted by this module.

No regularity condition on the time derivative of the applied well rates Q
appears in any declaration below. The constrained controller requires the
bounded derivative of demand D, exactly as in Assumption A6.
-/

namespace ReservoirSeismicityControl

/-- Appendix A.3, equation `eq:PsiDerivativeNew`: the four independently
estimated classes of terms give the bound on the regional perturbation rate.
The *existence* of the decomposition and each bound is a PDE proof obligation,
not hidden inside this result. -/
theorem paper_regional_perturbation_rate_bound
    {E : Type*} [NormedAddCommGroup E]
    (near far reaction reference rate : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hnear : ∀ t, 0 ≤ t → ‖near t‖ ≤ Lnear)
    (hfar : ∀ t, 0 ≤ t → ‖far t‖ ≤ Lfar)
    (hreaction : ∀ t, 0 ≤ t → ‖reaction t‖ ≤ Lreaction)
    (href : ∀ t, 0 ≤ t → ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ t, 0 ≤ t →
      rate t = near t + far t + reaction t + reference t) :
    ∀ t, 0 ≤ t →
      ‖rate t‖ ≤ Lnear + Lfar + Lreaction + Lreference := by
  intro t ht
  rw [hdecomp t ht]
  have h1 := norm_add_le (near t) (far t)
  have h2 := norm_add_le (near t + far t) (reaction t)
  have h3 := norm_add_le (near t + far t + reaction t) (reference t)
  have hn := hnear t ht
  have hf := hfar t ht
  have hr := hreaction t ht
  have href' := href t ht
  linarith

/-- Appendix A.4, `eq:PsiBarBoundNew`: a quantified version of the exact
matrix inverse derivative estimate. `inverseGain` and `gainRate` are bounded
linear operators, not just numbers. `htransport` is the inverse product-rule
identity and remains an explicitly visible analytic hypothesis. -/
theorem paper_normalized_perturbation_rate_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate normalizedRate : ℝ → E)
    (inverseGain gainRate : ℝ → E →L[ℝ] E)
    (δB Lpsi LpsiRate LgainRate : ℝ)
    (hδ : δB < 1)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLgain : 0 ≤ LgainRate)
    (hpsi : ∀ t, 0 ≤ t → ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ t, 0 ≤ t → ‖psiRate t‖ ≤ LpsiRate)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ t, 0 ≤ t →
      normalizedRate t = inverseGain t (psiRate t) -
        inverseGain t (gainRate t (inverseGain t (psi t)))) :
    ∀ t, 0 ≤ t →
      ‖normalizedRate t‖ ≤
        (1 / (1 - δB)) * LpsiRate +
        (1 / (1 - δB)) *
          (LgainRate * ((1 / (1 - δB)) * Lpsi)) := by
  intro t ht
  have hq : 0 ≤ (1 / (1 - δB)) := by
    apply div_nonneg
    · norm_num
    · linarith
  have hfirst : ‖inverseGain t (psiRate t)‖ ≤
      (1 / (1 - δB)) * LpsiRate := by
    calc
      _ ≤ (1 / (1 - δB)) * ‖psiRate t‖ := hinv t (psiRate t)
      _ ≤ (1 / (1 - δB)) * LpsiRate :=
        mul_le_mul_of_nonneg_left (hpsiRate t ht) hq
  have hsecond :
      ‖inverseGain t (gainRate t (inverseGain t (psi t)))‖ ≤
        (1 / (1 - δB)) *
          (LgainRate * ((1 / (1 - δB)) * Lpsi)) := by
    calc
      _ ≤ (1 / (1 - δB)) * ‖gainRate t (inverseGain t (psi t))‖ :=
        hinv t _
      _ ≤ (1 / (1 - δB)) * (LgainRate * ‖inverseGain t (psi t)‖) :=
        mul_le_mul_of_nonneg_left (hgainRate t _) hq
      _ ≤ (1 / (1 - δB)) *
          (LgainRate * ((1 / (1 - δB)) * ‖psi t‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hinv t (psi t)) hLgain) hq
      _ ≤ (1 / (1 - δB)) *
          (LgainRate * ((1 / (1 - δB)) * Lpsi)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hpsi t ht) hq) hLgain) hq
  rw [htransport t ht]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

/-- Theorem 1 quantitative conclusion, obtained from the four Appendix A.3
regional estimates and Appendix A.4 inverse-gain identity. This verifies
exactly the inequalities, not the externally cited STA stability theorem.
`hgainError` and `hinv` represent the matrix results of Appendix A.4. -/
theorem paper_theorem1_quantitative_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate normalizedRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (inverseGain gainRate : ℝ → E →L[ℝ] E)
    (gainErrorNorm : ℝ → ℝ)
    (δB Lpsi Lnear Lfar Lreaction Lreference LgainRate : ℝ)
    (hδ0 : 0 ≤ δB) (hδ1 : δB < 1)
    (hpsi0 : 0 ≤ Lpsi) (hgain0 : 0 ≤ LgainRate)
    (hnear0 : 0 ≤ Lnear) (hfar0 : 0 ≤ Lfar)
    (hreaction0 : 0 ≤ Lreaction) (href0 : 0 ≤ Lreference)
    (hpsi : ∀ t, 0 ≤ t → ‖psi t‖ ≤ Lpsi)
    (hnear : ∀ t, 0 ≤ t → ‖near t‖ ≤ Lnear)
    (hfar : ∀ t, 0 ≤ t → ‖far t‖ ≤ Lfar)
    (hreaction : ∀ t, 0 ≤ t → ‖reaction t‖ ≤ Lreaction)
    (href : ∀ t, 0 ≤ t → ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ t, 0 ≤ t →
      psiRate t = near t + far t + reaction t + reference t)
    (hgainError : ∀ t, 0 ≤ t → gainErrorNorm t ≤ δB)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ t, 0 ≤ t →
      normalizedRate t = inverseGain t (psiRate t) -
        inverseGain t (gainRate t (inverseGain t (psi t)))) :
    RequiredScalarMargins gainErrorNorm (fun t => ‖normalizedRate t‖) := by
  let Lrate := Lnear + Lfar + Lreaction + Lreference
  have hrate0 : 0 ≤ Lrate := by
    dsimp [Lrate]
    linarith
  have hrate : ∀ t, 0 ≤ t → ‖psiRate t‖ ≤ Lrate :=
    paper_regional_perturbation_rate_bound
      near far reaction reference psiRate Lnear Lfar Lreaction Lreference
      hnear hfar hreaction href hdecomp
  have hnormalized := paper_normalized_perturbation_rate_bound
    psi psiRate normalizedRate inverseGain gainRate
    δB Lpsi Lrate LgainRate hδ1 hpsi0 hrate0 hgain0
    hpsi hrate hinv hgainRate htransport
  have hq : 0 ≤ (1 / (1 - δB)) := by
    apply div_nonneg
    · norm_num
    · linarith
  refine ⟨δB,
    (1 / (1 - δB)) * Lrate +
      (1 / (1 - δB)) * (LgainRate * ((1 / (1 - δB)) * Lpsi)),
    hδ0, hδ1, ?_, hgainError, ?_⟩
  · exact add_nonneg (mul_nonneg hq hrate0)
      (mul_nonneg hq (mul_nonneg hgain0 (mul_nonneg hq hpsi0)))
  · exact hnormalized

/-- The additional perturbation in Appendix B (equation `eq:GW`). -/
def paperDemandPsi
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi : ℝ → E) (B : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D : ℝ → R) (t : ℝ) : E :=
  psi t + B t (FD (D t))

/-- The derivative formula in Appendix B, equation `eq:PsiWDotBoundNew`.
This is a CANDIDATE derivative: identifying it with the time derivative of
`paperDemandPsi` requires the product rule and regularity hypotheses. -/
def paperDemandPsiRate
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psiRate : ℝ → E) (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R) (t : ℝ) : E :=
  psiRate t + BRate t (FD (D t)) + B t (FD (DRate t))

/-- Uniform bound for Appendix B's demand-modified perturbation. -/
theorem paper_demand_psi_bound
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi : ℝ → E) (B : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D : ℝ → R)
    (Lpsi LB LF LD : ℝ)
    (hLB : 0 ≤ LB) (hLF : 0 ≤ LF)
    (hpsi : ∀ t, 0 ≤ t → ‖psi t‖ ≤ Lpsi)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ t, 0 ≤ t → ‖D t‖ ≤ LD) :
    ∀ t, 0 ≤ t →
      ‖paperDemandPsi psi B FD D t‖ ≤ Lpsi + LB * (LF * LD) := by
  intro t ht
  have hFval : ‖FD (D t)‖ ≤ LF * LD :=
    (hF (D t)).trans (mul_le_mul_of_nonneg_left (hD t ht) hLF)
  have hBval : ‖B t (FD (D t))‖ ≤ LB * (LF * LD) :=
    (hB t _).trans (mul_le_mul_of_nonneg_left hFval hLB)
  exact (norm_add_le (psi t) (B t (FD (D t)))).trans
    (add_le_add (hpsi t ht) hBval)

/-- Uniform bound for the demand-modified perturbation derivative from the
product-rule decomposition and bounded D and DRate (A6). -/
theorem paper_demand_psi_rate_bound
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psiRate : ℝ → E) (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (Lrate LB LBRate LF LD LDRate : ℝ)
    (hLB : 0 ≤ LB) (hLBRate : 0 ≤ LBRate) (hLF : 0 ≤ LF)
    (hpsiRate : ∀ t, 0 ≤ t → ‖psiRate t‖ ≤ Lrate)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hBRate : ∀ t x, ‖BRate t x‖ ≤ LBRate * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ t, 0 ≤ t → ‖D t‖ ≤ LD)
    (hDRate : ∀ t, 0 ≤ t → ‖DRate t‖ ≤ LDRate) :
    ∀ t, 0 ≤ t →
      ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ ≤
        Lrate + LBRate * (LF * LD) + LB * (LF * LDRate) := by
  intro t ht
  have hFval : ‖FD (D t)‖ ≤ LF * LD :=
    (hF (D t)).trans (mul_le_mul_of_nonneg_left (hD t ht) hLF)
  have hFRval : ‖FD (DRate t)‖ ≤ LF * LDRate :=
    (hF (DRate t)).trans (mul_le_mul_of_nonneg_left (hDRate t ht) hLF)
  have hBRval : ‖BRate t (FD (D t))‖ ≤ LBRate * (LF * LD) :=
    (hBRate t _).trans (mul_le_mul_of_nonneg_left hFval hLBRate)
  have hBval : ‖B t (FD (DRate t))‖ ≤ LB * (LF * LDRate) :=
    (hB t _).trans (mul_le_mul_of_nonneg_left hFRval hLB)
  change ‖psiRate t + BRate t (FD (D t)) + B t (FD (DRate t))‖ ≤ _
  have ha := norm_add_le (psiRate t) (BRate t (FD (D t)))
  have hb := norm_add_le (psiRate t + BRate t (FD (D t))) (B t (FD (DRate t)))
  have hc := hpsiRate t ht
  linarith

/-- Theorem 2 quantitative conclusion: Appendix A bound shared by both
controllers, plus Appendix B's extra demand terms and inverse-gain identity.
The MIMO super-twisting stability conclusion remains an external theorem. -/
theorem paper_theorem2_quantitative_bridge
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate normalizedRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E) (FD : R →L[ℝ] U)
    (D DRate : ℝ → R)
    (inverseGain gainRate : ℝ → E →L[ℝ] E)
    (gainErrorNorm : ℝ → ℝ)
    (δBW Lpsi Lnear Lfar Lreaction Lreference : ℝ)
    (LB LBRate LF LD LDRate LgainRate : ℝ)
    (hδ0 : 0 ≤ δBW) (hδ1 : δBW < 1)
    (hpsi0 : 0 ≤ Lpsi) (hgain0 : 0 ≤ LgainRate)
    (hnear0 : 0 ≤ Lnear) (hfar0 : 0 ≤ Lfar)
    (hreaction0 : 0 ≤ Lreaction) (href0 : 0 ≤ Lreference)
    (hLB : 0 ≤ LB) (hLBRate : 0 ≤ LBRate) (hLF : 0 ≤ LF)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate)
    (hpsi : ∀ t, 0 ≤ t → ‖psi t‖ ≤ Lpsi)
    (hnear : ∀ t, 0 ≤ t → ‖near t‖ ≤ Lnear)
    (hfar : ∀ t, 0 ≤ t → ‖far t‖ ≤ Lfar)
    (hreaction : ∀ t, 0 ≤ t → ‖reaction t‖ ≤ Lreaction)
    (href : ∀ t, 0 ≤ t → ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ t, 0 ≤ t →
      psiRate t = near t + far t + reaction t + reference t)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hBRate : ∀ t x, ‖BRate t x‖ ≤ LBRate * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ t, 0 ≤ t → ‖D t‖ ≤ LD)
    (hDRate : ∀ t, 0 ≤ t → ‖DRate t‖ ≤ LDRate)
    (hgainError : ∀ t, 0 ≤ t → gainErrorNorm t ≤ δBW)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δBW)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ t, 0 ≤ t →
      normalizedRate t =
        inverseGain t (paperDemandPsiRate psiRate B BRate FD D DRate t) -
        inverseGain t (gainRate t
          (inverseGain t (paperDemandPsi psi B FD D t)))) :
    RequiredScalarMargins gainErrorNorm (fun t => ‖normalizedRate t‖) := by
  let Lrate := Lnear + Lfar + Lreaction + Lreference
  let LWpsi := Lpsi + LB * (LF * LD)
  let LWrate := Lrate + LBRate * (LF * LD) + LB * (LF * LDRate)
  have hrate0 : 0 ≤ Lrate := by
    dsimp [Lrate]
    linarith
  have hLWpsi0 : 0 ≤ LWpsi := by
    dsimp [LWpsi]
    exact add_nonneg hpsi0 (mul_nonneg hLB (mul_nonneg hLF hLD))
  have hLWrate0 : 0 ≤ LWrate := by
    dsimp [LWrate]
    exact add_nonneg
      (add_nonneg hrate0 (mul_nonneg hLBRate (mul_nonneg hLF hLD)))
      (mul_nonneg hLB (mul_nonneg hLF hLDRate))
  have hrate : ∀ t, 0 ≤ t → ‖psiRate t‖ ≤ Lrate :=
    paper_regional_perturbation_rate_bound
      near far reaction reference psiRate Lnear Lfar Lreaction Lreference
      hnear hfar hreaction href hdecomp
  have hWPsi : ∀ t, 0 ≤ t → ‖paperDemandPsi psi B FD D t‖ ≤ LWpsi :=
    paper_demand_psi_bound psi B FD D Lpsi LB LF LD hLB hLF hpsi hB hF hD
  have hWRate : ∀ t, 0 ≤ t →
      ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ ≤ LWrate :=
    paper_demand_psi_rate_bound psiRate B BRate FD D DRate
      Lrate LB LBRate LF LD LDRate hLB hLBRate hLF
      hrate hB hBRate hF hD hDRate
  have hnorm := paper_normalized_perturbation_rate_bound
    (paperDemandPsi psi B FD D)
    (paperDemandPsiRate psiRate B BRate FD D DRate)
    normalizedRate inverseGain gainRate δBW LWpsi LWrate LgainRate
    hδ1 hLWpsi0 hLWrate0 hgain0 hWPsi hWRate hinv hgainRate htransport
  have hq : 0 ≤ (1 / (1 - δBW)) := by
    apply div_nonneg
    · norm_num
    · linarith
  refine ⟨δBW,
    (1 / (1 - δBW)) * LWrate +
      (1 / (1 - δBW)) * (LgainRate * ((1 / (1 - δBW)) * LWpsi)),
    hδ0, hδ1, ?_, hgainError, ?_⟩
  · exact add_nonneg (mul_nonneg hq hLWrate0)
      (mul_nonneg hq (mul_nonneg hgain0 (mul_nonneg hq hLWpsi0)))
  · exact hnorm

/-- Appendix B's exact demand identity, using the *already verified*
`ReservoirSeismicityControl.demand_exact`, valid at every time (including t = 0). -/
theorem paper_theorem2_exact_demand_bridge
    {n m nr : ℕ}
    (W : (Fin n → ℝ) →ₗ[ℝ] (Fin nr → ℝ))
    (C : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (F : (Fin nr → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hWC : ∀ z : Fin m → ℝ, W (C z) = 0)
    (hWF : ∀ d : Fin nr → ℝ, W (F d) = d)
    (z : ℝ → Fin m → ℝ) (D : ℝ → Fin nr → ℝ) :
    ∀ t : ℝ, W (C (z t) + F (D t)) = D t := by
  intro t
  exact demand_exact W C F hWC hWF (z t) (D t)

end ReservoirSeismicityControl
