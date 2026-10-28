import ReservoirSeismicityControl.PaperInverseGainDifferentiability
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Stage 42 — Gain invertibility and inverse bound from a strict contraction

The manuscript's small-gain hypothesis has the operator form
  ‖I - G(t)‖ ≤ δ < 1.
In the complete continuous-linear-endomorphism algebra, the Neumann-series
lemma proves that `G(t)` is a unit. The estimate
  (1-δ) ‖G(t)⁻¹ x‖ ≤ ‖x‖
then gives the exact inverse action bound used in Stages 36–41.

This file does not *identify* the manuscript's concrete matrix gain with
an endomorphism satisfying the norm contraction. That remains an explicit
connection to the finite-dimensional matrix modules, especially for the
weighted demand controller.

No input rate derivative Qdot is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A contraction relative to identity implies operator invertibility.
    This uses Mathlib's geometric-series construction. -/
theorem paper_gain_isUnit_of_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain : ℝ → E →L[ℝ] E) (δ : ℝ)
    (hδ : δ < 1)
    (hclose : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δ)
    (t : ℝ) : IsUnit (gain t) := by
  have hsmall : ‖(1 : E →L[ℝ] E) - gain t‖ < 1 :=
    lt_of_le_of_lt (hclose t) hδ
  have hu : IsUnit (1 - ((1 : E →L[ℝ] E) - gain t)) :=
    isUnit_one_sub_of_norm_lt_one hsmall
  convert hu using 1 <;> abel

/-- The canonical inverse is a right inverse of the direct gain. -/
theorem paper_gain_ringInverse_right_of_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain : ℝ → E →L[ℝ] E) (δ : ℝ)
    (hδ : δ < 1)
    (hclose : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δ)
    (t : ℝ) (x : E) :
    gain t (Ring.inverse (gain t) x) = x := by
  have hu := paper_gain_isUnit_of_contraction gain δ hδ hclose t
  have h := congrArg (fun f : E →L[ℝ] E => f x)
    (Ring.mul_inverse_cancel (gain t) hu)
  change gain t (Ring.inverse (gain t) x) = x at h
  exact h

/-- The canonical inverse is a left inverse of the direct gain. -/
theorem paper_gain_ringInverse_left_of_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain : ℝ → E →L[ℝ] E) (δ : ℝ)
    (hδ : δ < 1)
    (hclose : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δ)
    (t : ℝ) (x : E) :
    Ring.inverse (gain t) (gain t x) = x := by
  have hu := paper_gain_isUnit_of_contraction gain δ hδ hclose t
  have h := congrArg (fun f : E →L[ℝ] E => f x)
    (Ring.inverse_mul_cancel (gain t) hu)
  change Ring.inverse (gain t) (gain t x) = x at h
  exact h

/-- The Neumann-series inverse bound with the *same* δ as in the paper. -/
theorem paper_gain_ringInverse_action_bound_of_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (gain : ℝ → E →L[ℝ] E) (δ : ℝ)
    (hδ : δ < 1)
    (hclose : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δ)
    (t : ℝ) (x : E) :
    ‖Ring.inverse (gain t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ := by
  let y : E := Ring.inverse (gain t) x
  have hx : gain t y = x :=
    paper_gain_ringInverse_right_of_contraction gain δ hδ hclose t x
  have hdiff : ‖((1 : E →L[ℝ] E) - gain t) y‖ ≤ δ * ‖y‖ := by
    calc
      ‖((1 : E →L[ℝ] E) - gain t) y‖ ≤
          ‖(1 : E →L[ℝ] E) - gain t‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖y‖ :=
        mul_le_mul_of_nonneg_right (hclose t) (norm_nonneg y)
  have hdecomp : y = gain t y + (((1 : E →L[ℝ] E) - gain t) y) := by
    change y = gain t y + (y - gain t y)
    abel
  have hnorm : ‖y‖ ≤ ‖x‖ + δ * ‖y‖ := by
    calc
      ‖y‖ = ‖gain t y + (((1 : E →L[ℝ] E) - gain t) y)‖ :=
        congrArg norm hdecomp
      _ ≤ ‖gain t y‖ + ‖((1 : E →L[ℝ] E) - gain t) y‖ :=
        norm_add_le _ _
      _ ≤ ‖x‖ + δ * ‖y‖ := by
        rw [hx]
        exact add_le_add_right hdiff _
  have hlinear : (1 - δ) * ‖y‖ ≤ ‖x‖ := by nlinarith
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ
  calc
    ‖Ring.inverse (gain t) x‖ = ‖y‖ := rfl
    _ ≤ ‖x‖ / (1 - δ) := by
      apply (le_div_iff₀ hpos).2
      nlinarith only [hlinear]
    _ = (1 / (1 - δ)) * ‖x‖ := by ring


/-- Theorem 1: operator contraction supplies inverse identities and bound. -/
theorem paper_theorem1_actual_derivative_from_contraction_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (gain gainRate : ℝ → E →L[ℝ] E)
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
    (hcontraction : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δB)
    (hgainError : ∀ᵐ t ∂paperPositiveTime,
      gainErrorNorm t ≤ δB)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ => Ring.inverse (gain s) (psi s)) t‖) := by
  let inverseGain : ℝ → E →L[ℝ] E := fun s => Ring.inverse (gain s)
  have hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δB)) * ‖x‖ := by
    intro t x
    exact paper_gain_ringInverse_action_bound_of_contraction
      gain δB hδ1 hcontraction t x
  have hRightInverse : ∀ s x, gain s (inverseGain s x) = x := by
    intro s x
    exact paper_gain_ringInverse_right_of_contraction
      gain δB hδ1 hcontraction s x
  have hLeftInverse : ∀ s x, inverseGain s (gain s x) = x := by
    intro s x
    exact paper_gain_ringInverse_left_of_contraction
      gain δB hδ1 hcontraction s x
  have hmain := paper_theorem1_actual_derivative_from_gain_ae
    psi psiRate near far reaction reference
    gain inverseGain gainRate gainErrorNorm
    δB Lpsi Lnear Lfar Lreaction Lreference LgainRate
    hδ0 hδ1 hpsi0 hgain0 hnear0 hfar0 hreaction0 href0
    hpsi hnear hfar hreaction href hdecomp hgainError hinv hgainRate
    hpsiDeriv hGainDeriv hRightInverse hLeftInverse
  simpa only [inverseGain] using hmain

/-- Theorem 2: operator contraction supplies inverse identities and bound. -/
theorem paper_theorem2_actual_derivative_from_contraction_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (near far reaction reference : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E) (FD : R →L[ℝ] U)
    (D DRate : ℝ → R)
    (gain gainRate : ℝ → E →L[ℝ] E)
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
    (hcontraction : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δBW)
    (hgainError : ∀ᵐ t ∂paperPositiveTime,
      gainErrorNorm t ≤ δBW)
    (hgainRate : ∀ t x, ‖gainRate t x‖ ≤ LgainRate * ‖x‖)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hBDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt B (BRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t)
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt gain (gainRate t) t) :
    PaperRequiredAEMargins gainErrorNorm
      (fun t => ‖deriv (fun s : ℝ =>
        Ring.inverse (gain s) (paperDemandPsi psi B FD D s)) t‖) := by
  let inverseGain : ℝ → E →L[ℝ] E := fun s => Ring.inverse (gain s)
  have hinv : ∀ t x,
      ‖inverseGain t x‖ ≤ (1 / (1 - δBW)) * ‖x‖ := by
    intro t x
    exact paper_gain_ringInverse_action_bound_of_contraction
      gain δBW hδ1 hcontraction t x
  have hRightInverse : ∀ s x, gain s (inverseGain s x) = x := by
    intro s x
    exact paper_gain_ringInverse_right_of_contraction
      gain δBW hδ1 hcontraction s x
  have hLeftInverse : ∀ s x, inverseGain s (gain s x) = x := by
    intro s x
    exact paper_gain_ringInverse_left_of_contraction
      gain δBW hδ1 hcontraction s x
  have hmain := paper_theorem2_actual_derivative_from_gain_ae
    psi psiRate near far reaction reference
    B BRate FD D DRate
    gain inverseGain gainRate gainErrorNorm
    δBW Lpsi Lnear Lfar Lreaction Lreference
    LB LBRate LF LD LDRate LgainRate
    hδ0 hδ1 hpsi0 hgain0 hnear0 hfar0 hreaction0 href0
    hLB hLBRate hLF hLD hLDRate
    hpsi hnear hfar hreaction href hdecomp
    hB hBRate hF hD hDRate hgainError hinv hgainRate
    hpsiDeriv hBDeriv hDDeriv hGainDeriv
    hRightInverse hLeftInverse
  simpa only [inverseGain] using hmain

end ReservoirSeismicityControl
