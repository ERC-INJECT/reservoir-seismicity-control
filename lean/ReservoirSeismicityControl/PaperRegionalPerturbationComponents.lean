import ReservoirSeismicityControl.PaperPhysicalSRAveragesFinalCertificates

/-!
# Stage 60: assemble actual regional perturbation components (Appendix A.3)

The regional perturbation is split into a near-well diffusion term, a
far-well diffusion term, an SR reaction term, and a reference term.

This module shows that differentiation and the a.e. uniform norm estimates
pass from the four *actual component trajectories* to their sum. In
particular it eliminates the **independent derivative assumption on their
sum** once the four component derivatives are supplied.

IMPORTANT: This is NOT yet a PDE proof that the near and far diffusion
components admit the stated derivatives. The difficult Neumann semigroup,
separation, convolution, and approximation argument remains to be linked to
these hypotheses. No Qdot or Qddot bound is used here.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The regional perturbation built from the four classes of terms
in Appendix A.3. The individual components must subsequently be identified
with their spatial PDE--ODE expressions. -/
def paperRegionalPsiFromComponents
    {E : Type*} [Add E]
    (near far reaction reference : ℝ → E) (t : ℝ) : E :=
  near t + far t + reaction t + reference t

/-- Candidate derivative formed from the four physical regional rates. -/
def paperRegionalPsiRateFromComponents
    {E : Type*} [Add E]
    (nearRate farRate reactionRate referenceRate : ℝ → E) (t : ℝ) : E :=
  nearRate t + farRate t + reactionRate t + referenceRate t

/-- At a regular time, the derivative of the four-term perturbation is the
sum of the component derivatives. -/
theorem paper_regional_psi_hasDerivAt_from_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (near far reaction reference : ℝ → E)
    (nearRate farRate reactionRate referenceRate : ℝ → E)
    (t : ℝ)
    (hn : HasDerivAt near (nearRate t) t)
    (hf : HasDerivAt far (farRate t) t)
    (hr : HasDerivAt reaction (reactionRate t) t)
    (href : HasDerivAt reference (referenceRate t) t) :
    HasDerivAt (paperRegionalPsiFromComponents near far reaction reference)
      (paperRegionalPsiRateFromComponents
        nearRate farRate reactionRate referenceRate t) t := by
  -- Addition of functions is pointwise. Rewrite the named component sum
  -- as the function sum produced by `HasDerivAt.add`.
  have hfun :
      paperRegionalPsiFromComponents near far reaction reference =
        near + far + reaction + reference := by
    funext s
    simp only [paperRegionalPsiFromComponents, Pi.add_apply]
  change HasDerivAt (paperRegionalPsiFromComponents near far reaction reference)
    (nearRate t + farRate t + reactionRate t + referenceRate t) t
  rw [hfun]
  exact (((hn.add hf).add hr).add href)

/-- Almost-everywhere version on strictly positive time. It requires no
pointwise derivative at switching times. -/
theorem paper_regional_psi_hasDerivAt_from_components_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (near far reaction reference : ℝ → E)
    (nearRate farRate reactionRate referenceRate : ℝ → E)
    (hn : ∀ᵐ t ∂paperPositiveTime, HasDerivAt near (nearRate t) t)
    (hf : ∀ᵐ t ∂paperPositiveTime, HasDerivAt far (farRate t) t)
    (hr : ∀ᵐ t ∂paperPositiveTime, HasDerivAt reaction (reactionRate t) t)
    (href : ∀ᵐ t ∂paperPositiveTime, HasDerivAt reference (referenceRate t) t) :
    ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (paperRegionalPsiFromComponents near far reaction reference)
        (paperRegionalPsiRateFromComponents
          nearRate farRate reactionRate referenceRate t) t := by
  filter_upwards [hn, hf, hr, href] with t hnt hft hrt hreft
  exact paper_regional_psi_hasDerivAt_from_components
    near far reaction reference nearRate farRate reactionRate referenceRate
    t hnt hft hrt hreft

/-- The actual four-term perturbation has an a.e. norm bound when each
component is bounded. This does not presume boundedness of its derivative. -/
theorem paper_regional_psi_norm_from_components_ae
    {E : Type*} [NormedAddCommGroup E]
    (near far reaction reference : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hn : ∀ᵐ t ∂paperPositiveTime, ‖near t‖ ≤ Lnear)
    (hf : ∀ᵐ t ∂paperPositiveTime, ‖far t‖ ≤ Lfar)
    (hr : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖reference t‖ ≤ Lreference) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖paperRegionalPsiFromComponents near far reaction reference t‖ ≤
        Lnear + Lfar + Lreaction + Lreference := by
  have hdecomp : ∀ᵐ t ∂paperPositiveTime,
      paperRegionalPsiFromComponents near far reaction reference t =
        near t + far t + reaction t + reference t :=
    Filter.Eventually.of_forall (fun _ => rfl)
  exact paper_regional_perturbation_rate_bound_ae
    near far reaction reference
    (paperRegionalPsiFromComponents near far reaction reference)
    Lnear Lfar Lreaction Lreference hn hf hr href hdecomp

/-- Rate bound for the four terms in Appendix A.3. The rate here is
identified with the *derivative of the component sum* by the next theorem. -/
theorem paper_regional_psi_rate_from_components_ae
    {E : Type*} [NormedAddCommGroup E]
    (nearRate farRate reactionRate referenceRate : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hn : ∀ᵐ t ∂paperPositiveTime, ‖nearRate t‖ ≤ Lnear)
    (hf : ∀ᵐ t ∂paperPositiveTime, ‖farRate t‖ ≤ Lfar)
    (hr : ∀ᵐ t ∂paperPositiveTime, ‖reactionRate t‖ ≤ Lreaction)
    (href : ∀ᵐ t ∂paperPositiveTime, ‖referenceRate t‖ ≤ Lreference) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖paperRegionalPsiRateFromComponents
        nearRate farRate reactionRate referenceRate t‖ ≤
        Lnear + Lfar + Lreaction + Lreference := by
  have hdecomp : ∀ᵐ t ∂paperPositiveTime,
      paperRegionalPsiRateFromComponents
        nearRate farRate reactionRate referenceRate t =
          nearRate t + farRate t + reactionRate t + referenceRate t :=
    Filter.Eventually.of_forall (fun _ => rfl)
  exact paper_regional_perturbation_rate_bound_ae
    nearRate farRate reactionRate referenceRate
    (paperRegionalPsiRateFromComponents
      nearRate farRate reactionRate referenceRate)
    Lnear Lfar Lreaction Lreference hn hf hr href hdecomp

/-- Stage 60 conclusion: the *actual classical derivative* of the four-term
regional perturbation is bounded almost everywhere. The substantive PDE
work is to prove the component differentiability and bounds passed here.
No derivative bound on any well flux Q occurs. -/
theorem paper_regional_psi_actual_derivative_from_components_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (near far reaction reference : ℝ → E)
    (nearRate farRate reactionRate referenceRate : ℝ → E)
    (Lnear Lfar Lreaction Lreference : ℝ)
    (hn : ∀ᵐ t ∂paperPositiveTime, HasDerivAt near (nearRate t) t)
    (hf : ∀ᵐ t ∂paperPositiveTime, HasDerivAt far (farRate t) t)
    (hr : ∀ᵐ t ∂paperPositiveTime, HasDerivAt reaction (reactionRate t) t)
    (href : ∀ᵐ t ∂paperPositiveTime, HasDerivAt reference (referenceRate t) t)
    (hnBound : ∀ᵐ t ∂paperPositiveTime, ‖nearRate t‖ ≤ Lnear)
    (hfBound : ∀ᵐ t ∂paperPositiveTime, ‖farRate t‖ ≤ Lfar)
    (hrBound : ∀ᵐ t ∂paperPositiveTime, ‖reactionRate t‖ ≤ Lreaction)
    (hrefBound : ∀ᵐ t ∂paperPositiveTime, ‖referenceRate t‖ ≤ Lreference) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (paperRegionalPsiFromComponents near far reaction reference) t‖ ≤
        Lnear + Lfar + Lreaction + Lreference := by
  have hDeriv := paper_regional_psi_hasDerivAt_from_components_ae
    near far reaction reference
    nearRate farRate reactionRate referenceRate hn hf hr href
  have hBound := paper_regional_psi_rate_from_components_ae
    nearRate farRate reactionRate referenceRate
    Lnear Lfar Lreaction Lreference hnBound hfBound hrBound hrefBound
  filter_upwards [hDeriv, hBound] with t hd hb
  rw [hd.deriv]
  exact hb

end ReservoirSeismicityControl
