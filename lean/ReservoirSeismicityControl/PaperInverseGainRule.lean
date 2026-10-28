import ReservoirSeismicityControl.PaperActualMargins

/-!
# Stage 40: inverse-gain differentiation from the inverse identities

Source: NLD_2026(9).tex, Appendix A.4 and Appendix B.

The new theorem differentiates G(t) J(t) x = x, where J(t) is the
inverse gain operator, then uses J(t) G(t) y = y. It derives
  J'(t) x = -J(t) (G'(t) (J(t) x)).

Thus the two a.e. actual-derivative bridges no longer assume this rule.
We DO still assume that G and J are differentiable at the indicated times
and that they are genuine two-sided inverses. No bound on Qdot appears.
This does not establish G^{-1} differentiability from G differentiability,
or prove the PDE estimates or external MIMO super-twisting theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Differentiating `G(s) (J(s) x) = x` and applying the inverse `J(t)`
    gives the derivative of the inverse operator at a regular time. -/
theorem paper_inverse_gain_rule_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gain inverseGain gainRate inverseGainRate : ℝ → E →L[ℝ] E)
    (t : ℝ)
    (hGainDeriv : HasDerivAt gain (gainRate t) t)
    (hInvDeriv : HasDerivAt inverseGain (inverseGainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ x, inverseGain t (gain t x) = x) :
    ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x)) := by
  intro x
  have hx : HasDerivAt (fun s : ℝ => inverseGain s x)
      (inverseGainRate t x) t := by
    simpa using hInvDeriv.clm_apply (hasDerivAt_const t x)
  have hprod : HasDerivAt (fun s : ℝ => gain s (inverseGain s x))
      (gainRate t (inverseGain t x) + gain t (inverseGainRate t x)) t :=
    hGainDeriv.clm_apply hx
  have hfun : (fun s : ℝ => gain s (inverseGain s x)) =
      (fun _ : ℝ => x) := by
    funext s
    exact hRightInverse s x
  rw [hfun] at hprod
  have hzero : gainRate t (inverseGain t x) +
      gain t (inverseGainRate t x) = 0 := by
    exact hprod.unique (hasDerivAt_const t x)
  have hzeroInv : inverseGain t (gainRate t (inverseGain t x)) +
      inverseGainRate t x = 0 := by
    have hh := congrArg (fun y : E => inverseGain t y) hzero
    simpa only [map_add, map_zero, hLeftInverse] using hh
  calc
    inverseGainRate t x =
        (inverseGain t (gainRate t (inverseGain t x)) +
          inverseGainRate t x) -
        inverseGain t (gainRate t (inverseGain t x)) := by abel
    _ = 0 - inverseGain t (gainRate t (inverseGain t x)) := by
      rw [hzeroInv]
    _ = -inverseGain t (gainRate t (inverseGain t x)) := by simp

/-- An almost-everywhere inverse-derivative formula with genuine gain/inverse
    identities, no separately postulated inverse transport rule. -/
theorem paper_inverse_gain_rule_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gain inverseGain gainRate inverseGainRate : ℝ → E →L[ℝ] E)
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hInvDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (inverseGainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    ∀ᵐ t ∂paperPositiveTime, ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x)) := by
  filter_upwards [hGainDeriv, hInvDeriv] with t hg hi
  exact paper_inverse_gain_rule_at
    gain inverseGain gainRate inverseGainRate t hg hi
    hRightInverse (hLeftInverse t)

/-- Theorem 1: a.e. quantitative margin for the actual derivative, with the
    inverse-derivative rule proved from two-sided inverse identities. -/
theorem paper_theorem1_actual_derivative_from_gain_id_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (gain inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
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
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ => inverseGain s (psi s)) t‖) := by
  have hInvRule := paper_inverse_gain_rule_ae
    gain inverseGain gainRate inverseGainRate
    hGainDeriv hInvDeriv hRightInverse hLeftInverse
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


/-- Theorem 2: same rule for the demand controller. Only DRate is needed;
    no time derivative of the well rates is assumed. -/
theorem paper_theorem2_actual_derivative_from_gain_id_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E) (FD : R →L[ℝ] U)
    (D DRate : ℝ → R)
    (gain inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
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
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ =>
        inverseGain s (paperDemandPsi psi B FD D s)) t‖) := by
  have hInvRule := paper_inverse_gain_rule_ae
    gain inverseGain gainRate inverseGainRate
    hGainDeriv hInvDeriv hRightInverse hLeftInverse
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
