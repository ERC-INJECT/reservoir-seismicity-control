import ReservoirSeismicityControl.PaperProofBridge

/-!
# Stage 37: almost-everywhere versions of the manuscript's perturbation bounds

The manuscript obtains weak/essentially bounded time derivatives, not
classical pointwise derivatives at every switching instant.  Consequently
Stages 36's pointwise interface is stronger than the paper needs.

This file proves the same quantitative conclusions under almost-everywhere
regional bounds and derivative identities, with respect to Lebesgue measure
restricted to strictly positive time.  It makes no assertion at exceptional
switching times.  Operator action bounds remain uniform in time, as in the
paper.  The PDE regularity and product-rule identities are still hypotheses;
this file does not silently assume existence of derivatives of Q.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Lebesgue measure on the positive time axis used for a.e. derivatives. -/
noncomputable def paperPositiveTime : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioi 0)

/-- A.e. counterpart of the uniform scalar margins in Theorems 1 and 2.
The two inequalities are required only away from a null set of times. -/
def PaperRequiredAEMargins
    (gainErrorNorm normalizedRateNorm : ℝ → ℝ) : Prop :=
  ∃ δB δ : ℝ, 0 ≤ δB ∧ δB < 1 ∧ 0 ≤ δ ∧
    (∀ᵐ t ∂paperPositiveTime, gainErrorNorm t ≤ δB) ∧
    (∀ᵐ t ∂paperPositiveTime, normalizedRateNorm t ≤ δ)

/-- Appendix A.3: regional contributions yield an a.e. perturbation-rate
bound.  No pointwise derivative at switching times is assumed. -/
theorem paper_regional_perturbation_rate_bound_ae
    {E : Type*} [NormedAddCommGroup E]
    (near far reaction reference rate : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hnear : ∀ᵐ t ∂paperPositiveTime, ‖near t‖ ≤ Lnear)
    (hfar : ∀ᵐ t ∂paperPositiveTime, ‖far t‖ ≤ Lfar)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ᵐ t ∂paperPositiveTime,
      rate t = near t + far t + reaction t + reference t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖rate t‖ ≤ Lnear + Lfar + Lreaction + Lreference := by
  filter_upwards [hnear, hfar, hreaction, href, hdecomp] with t hn hf hr href' hd
  rw [hd]
  have h1 := norm_add_le (near t) (far t)
  have h2 := norm_add_le (near t + far t) (reaction t)
  have h3 := norm_add_le (near t + far t + reaction t) (reference t)
  linarith

/-- Appendix A.4: the normalized perturbation-rate estimate a.e. in time.
The inverse differentiation identity is hypothesized only a.e., matching
the Sobolev/absolute-continuity formulation in the manuscript. -/
theorem paper_normalized_perturbation_rate_bound_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate normalizedRate : ℝ → E)
    (inverseGain gainRate : ℝ → E →L[ℝ] E)
    (δB Lpsi LpsiRate LgainRate : ℝ)
    (hδ : δB < 1)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLgain : 0 ≤ LgainRate)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ᵐ t ∂paperPositiveTime,
      normalizedRate t = inverseGain t (psiRate t) -
        inverseGain t (gainRate t (inverseGain t (psi t)))) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖normalizedRate t‖ ≤
        (1 / (1 - δB)) * LpsiRate +
        (1 / (1 - δB)) *
          (LgainRate * ((1 / (1 - δB)) * Lpsi)) := by
  have hq : 0 ≤ (1 / (1 - δB)) := by
    apply div_nonneg
    · norm_num
    · linarith
  filter_upwards [hpsi, hpsiRate, htransport] with t hp hpr htr
  have hfirst : ‖inverseGain t (psiRate t)‖ ≤
      (1 / (1 - δB)) * LpsiRate := by
    calc
      _ ≤ (1 / (1 - δB)) * ‖psiRate t‖ := hinv t (psiRate t)
      _ ≤ (1 / (1 - δB)) * LpsiRate :=
        mul_le_mul_of_nonneg_left hpr hq
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
            (mul_le_mul_of_nonneg_left hp hq) hLgain) hq
  rw [htr]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

/-- Theorem 1's required quantitative margins with the a.e. quantifiers
actually supplied by the regularity proof in Appendix A. -/
theorem paper_theorem1_ae_bridge
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
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hnear : ∀ᵐ t ∂paperPositiveTime, ‖near t‖ ≤ Lnear)
    (hfar : ∀ᵐ t ∂paperPositiveTime, ‖far t‖ ≤ Lfar)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ᵐ t ∂paperPositiveTime,
      psiRate t = near t + far t + reaction t + reference t)
    (hgainError : ∀ᵐ t ∂paperPositiveTime, gainErrorNorm t ≤ δB)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ᵐ t ∂paperPositiveTime,
      normalizedRate t = inverseGain t (psiRate t) -
        inverseGain t (gainRate t (inverseGain t (psi t)))) :
    PaperRequiredAEMargins gainErrorNorm (fun t => ‖normalizedRate t‖) := by
  let Lrate := Lnear + Lfar + Lreaction + Lreference
  have hrate0 : 0 ≤ Lrate := by
    dsimp [Lrate]
    linarith
  have hrate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ Lrate :=
    paper_regional_perturbation_rate_bound_ae
      near far reaction reference psiRate Lnear Lfar Lreaction Lreference
      hnear hfar hreaction href hdecomp
  have hnormalized := paper_normalized_perturbation_rate_bound_ae
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

/-- Appendix B: a.e. boundedness of demand-modified perturbation. -/
theorem paper_demand_psi_bound_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi : ℝ → E) (B : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D : ℝ → R)
    (Lpsi LB LF LD : ℝ)
    (hLB : 0 ≤ LB) (hLF : 0 ≤ LF)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖paperDemandPsi psi B FD D t‖ ≤ Lpsi + LB * (LF * LD) := by
  filter_upwards [hpsi, hD] with t hp hdt
  have hFval : ‖FD (D t)‖ ≤ LF * LD :=
    (hF (D t)).trans (mul_le_mul_of_nonneg_left hdt hLF)
  have hBval : ‖B t (FD (D t))‖ ≤ LB * (LF * LD) :=
    (hB t _).trans (mul_le_mul_of_nonneg_left hFval hLB)
  exact (norm_add_le (psi t) (B t (FD (D t)))).trans
    (add_le_add hp hBval)

/-- Appendix B: the candidate demand perturbation rate is bounded a.e.
The assertion that this candidate is an actual weak derivative remains an
independent product-rule/regularity obligation. -/
theorem paper_demand_psi_rate_bound_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psiRate : ℝ → E) (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (Lrate LB LBRate LF LD LDRate : ℝ)
    (hLB : 0 ≤ LB) (hLBRate : 0 ≤ LBRate) (hLF : 0 ≤ LF)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ Lrate)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hBRate : ∀ t x, ‖BRate t x‖ ≤ LBRate * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ ≤
        Lrate + LBRate * (LF * LD) + LB * (LF * LDRate) := by
  filter_upwards [hpsiRate, hD, hDRate] with t hp hdt hrdt
  have hFval : ‖FD (D t)‖ ≤ LF * LD :=
    (hF (D t)).trans (mul_le_mul_of_nonneg_left hdt hLF)
  have hFRval : ‖FD (DRate t)‖ ≤ LF * LDRate :=
    (hF (DRate t)).trans (mul_le_mul_of_nonneg_left hrdt hLF)
  have hBRval : ‖BRate t (FD (D t))‖ ≤ LBRate * (LF * LD) :=
    (hBRate t _).trans (mul_le_mul_of_nonneg_left hFval hLBRate)
  have hBval : ‖B t (FD (DRate t))‖ ≤ LB * (LF * LDRate) :=
    (hB t _).trans (mul_le_mul_of_nonneg_left hFRval hLB)
  change ‖psiRate t + BRate t (FD (D t)) + B t (FD (DRate t))‖ ≤ _
  have ha := norm_add_le (psiRate t) (BRate t (FD (D t)))
  have hb := norm_add_le (psiRate t + BRate t (FD (D t))) (B t (FD (DRate t)))
  linarith

/-- Theorem 2's a.e. quantitative margins, with no Qdot condition.
Demand regularity is represented solely by the a.e. DRate bound (A6). -/
theorem paper_theorem2_ae_bridge
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
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hnear : ∀ᵐ t ∂paperPositiveTime, ‖near t‖ ≤ Lnear)
    (hfar : ∀ᵐ t ∂paperPositiveTime, ‖far t‖ ≤ Lfar)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ᵐ t ∂paperPositiveTime,
      psiRate t = near t + far t + reaction t + reference t)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hBRate : ∀ t x, ‖BRate t x‖ ≤ LBRate * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hgainError : ∀ᵐ t ∂paperPositiveTime, gainErrorNorm t ≤ δBW)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δBW)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (htransport : ∀ᵐ t ∂paperPositiveTime,
      normalizedRate t =
        inverseGain t (paperDemandPsiRate psiRate B BRate FD D DRate t) -
        inverseGain t (gainRate t
          (inverseGain t (paperDemandPsi psi B FD D t)))) :
    PaperRequiredAEMargins gainErrorNorm (fun t => ‖normalizedRate t‖) := by
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
  have hrate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ Lrate :=
    paper_regional_perturbation_rate_bound_ae
      near far reaction reference psiRate Lnear Lfar Lreaction Lreference
      hnear hfar hreaction href hdecomp
  have hWPsi : ∀ᵐ t ∂paperPositiveTime,
      ‖paperDemandPsi psi B FD D t‖ ≤ LWpsi :=
    paper_demand_psi_bound_ae psi B FD D Lpsi LB LF LD hLB hLF hpsi hB hF hD
  have hWRate : ∀ᵐ t ∂paperPositiveTime,
      ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ ≤ LWrate :=
    paper_demand_psi_rate_bound_ae psiRate B BRate FD D DRate
      Lrate LB LBRate LF LD LDRate hLB hLBRate hLF
      hrate hB hBRate hF hD hDRate
  have hnorm := paper_normalized_perturbation_rate_bound_ae
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

end ReservoirSeismicityControl
