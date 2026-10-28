import ReservoirSeismicityControl.PaperActualDerivatives

/-!
# Stage 39: quantitative margins for actual a.e. derivatives

Source: NLD_2026(9).tex, Appendix A.3--A.4 and Appendix B.

Stages 37 and 38 are joined here. Stage 37 bounds a candidate normalized
rate if an a.e. transport identity is assumed; Stage 38 derives that identity
for the actual derivative from differentiability of the perturbation and of
the inverse-gain operator, plus its stated inverse derivative formula.

No assumption about a time derivative of the well rates Q is introduced.
The actual PDE/SR estimates, existence of a.e. derivatives, gain action
bounds, and inverse differentiation identity remain separately visible
hypotheses. No MIMO super-twisting convergence theorem is claimed here.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Appendix A.3: the regional rate decomposition bounds the actual
classical derivative at almost every positive time. -/
theorem paper_actual_regional_rate_bound_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate near far reaction reference : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hnear : ∀ᵐ t ∂paperPositiveTime, ‖near t‖ ≤ Lnear)
    (hfar : ∀ᵐ t ∂paperPositiveTime, ‖far t‖ ≤ Lfar)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖reference t‖ ≤ Lreference)
    (hdecomp : ∀ᵐ t ∂paperPositiveTime,
      psiRate t = near t + far t + reaction t + reference t)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv psi t‖ ≤ Lnear + Lfar + Lreaction + Lreference := by
  have hbound := paper_regional_perturbation_rate_bound_ae
    near far reaction reference psiRate Lnear Lfar Lreaction Lreference
    hnear hfar hreaction href hdecomp
  filter_upwards [hbound, hpsiDeriv] with t hb hd
  rw [hd.deriv]
  exact hb

/-- Theorem 1: the normalized derivative appearing in the manuscript is
literally the derivative of t ↦ G(t)⁻¹ Psi(t), not an arbitrary candidate.
This discharges Stage 37's `htransport` through Stage 38's product rule. -/
theorem paper_theorem1_actual_derivative_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
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
    (hgainError : ∀ᵐ t ∂paperPositiveTime,
      gainErrorNorm t ≤ δB)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hInvDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (inverseGainRate t) t)
    (hInvRule : ∀ᵐ t ∂paperPositiveTime, ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x))) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ => inverseGain s (psi s)) t‖) := by
  have htransport := paper_normalized_psi_deriv_ae
    psi psiRate inverseGain inverseGainRate gainRate
    hpsiDeriv hInvDeriv hInvRule
  exact paper_theorem1_ae_bridge
    psi psiRate (fun t => deriv (fun s : ℝ => inverseGain s (psi s)) t)
    near far reaction reference inverseGain gainRate gainErrorNorm
    δB Lpsi Lnear Lfar Lreaction Lreference LgainRate
    hδ0 hδ1 hpsi0 hgain0 hnear0 hfar0 hreaction0 href0
    hpsi hnear hfar hreaction href hdecomp hgainError hinv hgainRate
    htransport

/-- Appendix B: a bound on the genuine a.e. derivative of the demand
perturbation. This combines Stage 37's estimate with the derivative
identification of Stage 38, using a bound on DRate (not Qdot). -/
theorem paper_actual_demand_psi_rate_bound_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (Lrate LB LBRate LF LD LDRate : ℝ)
    (hLB : 0 ≤ LB) (hLBRate : 0 ≤ LBRate) (hLF : 0 ≤ LF)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ Lrate)
    (hB : ∀ t x, ‖B t x‖ ≤ LB * ‖x‖)
    (hBRate : ∀ t x, ‖BRate t x‖ ≤ LBRate * ‖x‖)
    (hF : ∀ x, ‖FD x‖ ≤ LF * ‖x‖)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hBDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt B (BRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (paperDemandPsi psi B FD D) t‖ ≤
        Lrate + LBRate * (LF * LD) + LB * (LF * LDRate) := by
  have hbound := paper_demand_psi_rate_bound_ae
    psiRate B BRate FD D DRate
    Lrate LB LBRate LF LD LDRate
    hLB hLBRate hLF hpsiRate hB hBRate hF hD hDRate
  have hderiv := paper_demand_psi_deriv_ae
    psi psiRate B BRate FD D DRate hpsiDeriv hBDeriv hDDeriv
  filter_upwards [hbound, hderiv] with t hb hd
  rw [hd]
  exact hb

/-- Theorem 2: the margin controls the actual derivative of
G_W(t)⁻¹ Psi_W(t), with A6's DRate bound. The inverse derivative rule
and input a.e. differentiability are still stated explicitly. -/
theorem paper_theorem2_actual_derivative_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E) (FD : R →L[ℝ] U)
    (D DRate : ℝ → R)
    (inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
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
    (hgainError : ∀ᵐ t ∂paperPositiveTime,
      gainErrorNorm t ≤ δBW)
    (hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δBW)) * ‖x‖)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hBDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt B (BRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t)
    (hInvDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (inverseGainRate t) t)
    (hInvRule : ∀ᵐ t ∂paperPositiveTime, ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x))) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ =>
        inverseGain s (paperDemandPsi psi B FD D s)) t‖) := by
  have htransport := paper_demand_normalized_psi_deriv_ae
    psi psiRate B BRate FD D DRate
    inverseGain inverseGainRate gainRate
    hpsiDeriv hBDeriv hDDeriv hInvDeriv hInvRule
  exact paper_theorem2_ae_bridge
    psi psiRate
    (fun t => deriv (fun s : ℝ =>
      inverseGain s (paperDemandPsi psi B FD D s)) t)
    near far reaction reference
    B BRate FD D DRate inverseGain gainRate gainErrorNorm
    δBW Lpsi Lnear Lfar Lreaction Lreference
    LB LBRate LF LD LDRate LgainRate
    hδ0 hδ1 hpsi0 hgain0 hnear0 hfar0 hreaction0 href0
    hLB hLBRate hLF hLD hLDRate
    hpsi hnear hfar hreaction href hdecomp
    hB hBRate hF hD hDRate hgainError hinv hgainRate
    htransport

end ReservoirSeismicityControl
