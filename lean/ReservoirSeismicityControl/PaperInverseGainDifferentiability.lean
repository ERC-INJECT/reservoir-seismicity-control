import ReservoirSeismicityControl.PaperInverseGainRule
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Stage 41: inverse-gain differentiability from gain differentiability

Source: NLD_2026(9).tex, Appendix A.4 and Appendix B.

The inverse gain is NOT assumed differentiable. For a Banach state space,
two-sided operator inverse identities make each gain a unit of the Banach
algebra of continuous linear endomorphisms. Mathlib's differentiability
of `Ring.inverse` then establishes the a.e. differentiability of the
actual inverse gain. Stage 40 determines its derivative algebraically.

The main margins still assume the PDE/SR bounds and the needed a.e.
differentiability of the direct gain, but not that of its inverse.
No derivative of the well rates Q is required.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Two-sided gain identities imply that the gain is invertible as an
    element of the continuous-linear-operator algebra. -/
theorem paper_gain_isUnit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gain inverseGain : ℝ → E →L[ℝ] E) (t : ℝ)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    IsUnit (gain t) := by
  apply isUnit_iff_exists.mpr
  refine ⟨inverseGain t, ?_, ?_⟩
  · ext x
    change gain t (inverseGain t x) = x
    exact hRightInverse t x
  · ext x
    change inverseGain t (gain t x) = x
    exact hLeftInverse t x

/-- Uniqueness of the inverse identifies the specified inverse gain
    with Mathlib's inverse on the endomorphism Banach algebra. -/
theorem paper_inverse_gain_eq_ringInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gain inverseGain : ℝ → E →L[ℝ] E) (t : ℝ)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    inverseGain t = Ring.inverse (gain t) := by
  have hu := paper_gain_isUnit gain inverseGain t hRightInverse hLeftInverse
  have hr : gain t * inverseGain t = 1 := by
    ext x
    change gain t (inverseGain t x) = x
    exact hRightInverse t x
  calc
    inverseGain t = (Ring.inverse (gain t) * gain t) * inverseGain t := by
      rw [Ring.inverse_mul_cancel (gain t) hu, one_mul]
    _ = Ring.inverse (gain t) * (gain t * inverseGain t) := mul_assoc _ _ _
    _ = Ring.inverse (gain t) := by rw [hr, mul_one]

/-- Differentiability of `G⁻¹` follows from differentiability of `G` and
    pointwise invertibility. No differentiability assumption on the inverse. -/
theorem paper_inverse_gain_hasDerivAt_from_gain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain inverseGain gainRate : ℝ → E →L[ℝ] E) (t : ℝ)
    (hGainDeriv : HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    HasDerivAt inverseGain (deriv inverseGain t) t := by
  have hu := paper_gain_isUnit gain inverseGain t hRightInverse hLeftInverse
  have heq : inverseGain = (fun s => Ring.inverse (gain s)) := by
    funext s
    exact paper_inverse_gain_eq_ringInverse gain inverseGain s
      hRightInverse hLeftInverse
  rw [heq]
  exact (hGainDeriv.differentiableAt.inverse hu).hasDerivAt

/-- A.e. differentiability of the true inverse from that of the direct gain. -/
theorem paper_inverse_gain_hasDerivAt_from_gain_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain inverseGain gainRate : ℝ → E →L[ℝ] E)
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (deriv inverseGain t) t := by
  filter_upwards [hGainDeriv] with t hg
  exact paper_inverse_gain_hasDerivAt_from_gain
    gain inverseGain gainRate t hg hRightInverse hLeftInverse

/-- Theorem 1: quantitative margin on the actual normalized-perturbation
    derivative without an independent inverse-gain differentiability premise. -/
theorem paper_theorem1_actual_derivative_from_gain_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (gain inverseGain gainRate : ℝ → E →L[ℝ] E)
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
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ => inverseGain s (psi s)) t‖) := by
  have hInvDeriv := paper_inverse_gain_hasDerivAt_from_gain_ae
    gain inverseGain gainRate
    hGainDeriv hRightInverse hLeftInverse
  have hInvRule := paper_inverse_gain_rule_ae
    gain inverseGain gainRate (fun t => deriv inverseGain t)
    hGainDeriv hInvDeriv hRightInverse hLeftInverse
  have htransport := paper_normalized_psi_deriv_ae
    psi psiRate inverseGain (fun t => deriv inverseGain t) gainRate
    hpsiDeriv hInvDeriv hInvRule
  exact paper_theorem1_ae_bridge
    psi psiRate (fun t => deriv (fun s : ℝ => inverseGain s (psi s)) t)
    near far reaction reference inverseGain gainRate gainErrorNorm
    δB Lpsi Lnear Lfar Lreaction Lreference LgainRate
    hδ0 hδ1 hpsi0 hgain0 hnear0 hfar0 hreaction0 href0
    hpsi hnear hfar hreaction href hdecomp hgainError hinv hgainRate
    htransport


theorem paper_theorem2_actual_derivative_from_gain_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E) (FD : R →L[ℝ] U)
    (D DRate : ℝ → R)
    (gain inverseGain gainRate : ℝ → E →L[ℝ] E)
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
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t)
    (hRightInverse : ∀ s x, gain s (inverseGain s x) = x)
    (hLeftInverse : ∀ s x, inverseGain s (gain s x) = x) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ =>
        inverseGain s (paperDemandPsi psi B FD D s)) t‖) := by
  have hInvDeriv := paper_inverse_gain_hasDerivAt_from_gain_ae
    gain inverseGain gainRate
    hGainDeriv hRightInverse hLeftInverse
  have hInvRule := paper_inverse_gain_rule_ae
    gain inverseGain gainRate (fun t => deriv inverseGain t)
    hGainDeriv hInvDeriv hRightInverse hLeftInverse
  have htransport := paper_demand_normalized_psi_deriv_ae
    psi psiRate B BRate FD D DRate
    inverseGain (fun t => deriv inverseGain t) gainRate
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
