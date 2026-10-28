import ReservoirSeismicityControl.PaperAERateBridge
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Stage 38: identify the *actual* a.e. derivatives in Appendix B

Source: NLD_2026(9).tex, Appendix A.4 and Appendix B.

Stage 37 bounds the candidate demand rate and assumes the inverse-gain
transport identity. Here the demand candidate is proved to be the actual
derivative at every time where Psi, B and D are differentiable. We also
obtain the derivative of (inverseGain Psi) from the CLM product rule.

No time derivative of the well rates Q is assumed anywhere in this file.
The inverse-gain derivative formula remains an explicit, separately visible
hypothesis. This file does NOT prove its validity from matrix invertibility,
nor prove PDE regularity or MIMO super-twisting stability.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The demand-modified candidate rate from Stage 36 is exactly the classical
 derivative of the demand perturbation at every regular time. -/
theorem paper_demand_psi_hasDerivAt
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R) (t : ℝ)
    (hpsi : HasDerivAt psi (psiRate t) t)
    (hB : HasDerivAt B (BRate t) t)
    (hD : HasDerivAt D (DRate t) t) :
    HasDerivAt (paperDemandPsi psi B FD D)
      (paperDemandPsiRate psiRate B BRate FD D DRate t) t := by
  have hFD : HasDerivAt (fun s : ℝ => FD (D s)) (FD (DRate t)) t :=
    FD.hasFDerivAt.comp_hasDerivAt t hD
  have hprod := hB.clm_apply hFD
  have hsum := hpsi.add hprod
  have hfun : (psi + fun s : ℝ => B s (FD (D s))) =
      paperDemandPsi psi B FD D := by
    funext s
    rfl
  rw [hfun] at hsum
  simpa only [paperDemandPsiRate, add_assoc] using hsum

/-- The demand candidate is the actual derivative for Lebesgue-a.e.
 positive time, as is appropriate for W¹,∞ solutions. -/
theorem paper_demand_psi_deriv_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, HasDerivAt psi (psiRate t) t)
    (hB : ∀ᵐ t ∂paperPositiveTime, HasDerivAt B (BRate t) t)
    (hD : ∀ᵐ t ∂paperPositiveTime, HasDerivAt D (DRate t) t) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (paperDemandPsi psi B FD D) t =
        paperDemandPsiRate psiRate B BRate FD D DRate t := by
  filter_upwards [hpsi, hB, hD] with t hp hb hd
  exact (paper_demand_psi_hasDerivAt
    psi psiRate B BRate FD D DRate t hp hb hd).deriv

/-- Appendix A.4's normalized derivative is a consequence of the
 time-dependent continuous-linear-map application rule, provided the
 inverse operator satisfies its usual derivative identity at this time.
 The latter remains a separate analytic obligation. -/
theorem paper_normalized_psi_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate : ℝ → E)
    (inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
    (t : ℝ)
    (hpsi : HasDerivAt psi (psiRate t) t)
    (hInv : HasDerivAt inverseGain (inverseGainRate t) t)
    (hInvRule : inverseGainRate t (psi t) =
      -inverseGain t (gainRate t (inverseGain t (psi t)))) :
    HasDerivAt (fun s : ℝ => inverseGain s (psi s))
      (inverseGain t (psiRate t) -
        inverseGain t (gainRate t (inverseGain t (psi t)))) t := by
  have heq :
      inverseGainRate t (psi t) + inverseGain t (psiRate t) =
        inverseGain t (psiRate t) -
          inverseGain t (gainRate t (inverseGain t (psi t))) := by
    rw [hInvRule]
    abel
  rw [← heq]
  exact hInv.clm_apply hpsi

/-- The actual derivative, rather than a candidate rate, of the normalized
 perturbation equals the Appendix A.4 expression a.e. -/
theorem paper_normalized_psi_deriv_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (psi psiRate : ℝ → E)
    (inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, HasDerivAt psi (psiRate t) t)
    (hInv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (inverseGainRate t) t)
    (hInvRule : ∀ᵐ t ∂paperPositiveTime, ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x))) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (fun s : ℝ => inverseGain s (psi s)) t =
        inverseGain t (psiRate t) -
          inverseGain t (gainRate t (inverseGain t (psi t))) := by
  filter_upwards [hpsi, hInv, hInvRule] with t hp hi hr
  exact (paper_normalized_psi_hasDerivAt
    psi psiRate inverseGain inverseGainRate gainRate t hp hi
    (hr (psi t))).deriv

/-- Appendix B: an actual a.e. derivative formula for G_W⁻¹ Psi_W, using
 the already defined candidate rate from Stage 36. This replaces Stage 37's
 assumed htransport by the three input derivatives and the explicit inverse
 derivative rule. -/
theorem paper_demand_normalized_psi_deriv_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (psi psiRate : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (inverseGain inverseGainRate gainRate : ℝ → E →L[ℝ] E)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, HasDerivAt psi (psiRate t) t)
    (hB : ∀ᵐ t ∂paperPositiveTime, HasDerivAt B (BRate t) t)
    (hD : ∀ᵐ t ∂paperPositiveTime, HasDerivAt D (DRate t) t)
    (hInv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt inverseGain (inverseGainRate t) t)
    (hInvRule : ∀ᵐ t ∂paperPositiveTime, ∀ x : E,
      inverseGainRate t x =
        -inverseGain t (gainRate t (inverseGain t x))) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (fun s : ℝ => inverseGain s (paperDemandPsi psi B FD D s)) t =
        inverseGain t (paperDemandPsiRate psiRate B BRate FD D DRate t) -
          inverseGain t (gainRate t
            (inverseGain t (paperDemandPsi psi B FD D t))) := by
  filter_upwards [hpsi, hB, hD, hInv, hInvRule]
    with t hp hb hd hi hr
  have hw := paper_demand_psi_hasDerivAt
    psi psiRate B BRate FD D DRate t hp hb hd
  exact (paper_normalized_psi_hasDerivAt
    (paperDemandPsi psi B FD D)
    (paperDemandPsiRate psiRate B BRate FD D DRate)
    inverseGain inverseGainRate gainRate t hw hi
    (hr (paperDemandPsi psi B FD D t))).deriv

end ReservoirSeismicityControl
