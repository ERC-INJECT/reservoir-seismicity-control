import ReservoirSeismicityControl.SeismicityPhysicalDemandBridge
import ReservoirSeismicityControl.SeismicityRateL2

/-!
# Stage 61: Strong L² SR rate from the actual pressure-to-SR evolution

At almost every time the physical SR rate is represented by
    Rdot(t) = - Kpressure(t) Udot(t) - reaction(t),
where Kpressure is intended to be multiplication by gamma₁(x) R(x,t)
and reaction is gamma₂ R (R - R*).

This file DERIVES the L² bound on Rdot from the norm bounds of
Kpressure, Udot and reaction instead of assuming a separate SR rate bound.
It then applies Stage 60 to the actual spatial well averages and obtains
its quantitative Theorem 2 certificate. The SR box is derived from the
original pointwise ODE by Stage 60.

Remaining physically unverified steps are EXPLICIT hypotheses:
  * representation Kpressure = gamma₁ R and reaction = gamma₂ R(R-R*),
    and strong L² identity Rdot = -Kpressure Udot - reaction;
  * multiplier and reaction operator/norm bounds; bounded L² pressure rate;
  * strong L² time differentiability and representative identification;
  * regional perturbation Psi and its a.e. derivative;
  * vertex coercivity/upper bounds and demand conditions.

No bounded derivative of well rates Q is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The L² seismicity derivative is bounded almost everywhere by the
actual strong L² evolution equation, without separately assuming a bound
on the derivative. This is the a.e. version of the rate estimate in
`SeismicityRateL2.lean`. -/
theorem sr_rate_L2_from_pressure_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (K : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cmult CU Creact : ℝ)
    (hK : ∀ᵐ t ∂paperPositiveTime, ‖K t‖ ≤ Cmult)
    (hU : ∀ᵐ t ∂paperPositiveTime, ‖Udot t‖ ≤ CU)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Creact)
    (hODE : ∀ᵐ t ∂paperPositiveTime,
      Rdot t = -(K t (Udot t)) - reaction t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖Rdot t‖ ≤ Cmult * CU + Creact := by
  filter_upwards [hK, hU, hreaction, hODE] with t hKt hUt hreactt hODEt
  have hCU : 0 ≤ CU := (norm_nonneg (Udot t)).trans hUt
  calc
    ‖Rdot t‖ = ‖-(K t (Udot t)) - reaction t‖ := by rw [hODEt]
    _ = ‖-(K t (Udot t)) + -reaction t‖ := by rw [sub_eq_add_neg]
    _ ≤ ‖-(K t (Udot t))‖ + ‖-reaction t‖ := norm_add_le _ _
    _ = ‖K t (Udot t)‖ + ‖reaction t‖ := by rw [norm_neg, norm_neg]
    _ ≤ ‖K t‖ * ‖Udot t‖ + ‖reaction t‖ :=
      add_le_add ((K t).le_opNorm (Udot t)) (le_refl _)
    _ ≤ ‖K t‖ * CU + ‖reaction t‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hUt (norm_nonneg (K t))) (le_refl _)
    _ ≤ Cmult * CU + ‖reaction t‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hKt hCU) (le_refl _)
    _ ≤ Cmult * CU + Creact := add_le_add (le_refl _) hreactt

/-- The Stage 60 certificate with the a.e. SR-rate bound supplied by
its strong L² evolution instead of a new independent hypothesis.
Positive SR well-sensitivity boxes still follow from the ORIGINAL
physical SR ODE in Stage 60. -/
theorem paper_physical_theorem2_certificates_from_physical_sr_rate_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (measure : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (uPhysical utPhysical RPhysical RtPhysical : X → ℝ → ℝ)
    (γ₁ Rstar : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (γmin γmax : ℝ)
    (smin smax amin amax bmin bmax Pbound : ℝ)
    (hγmin : 0 < γmin)
    (hsmin : 0 < smin) (hamin : 0 < amin) (hbmin : 0 < bmin)
    (hbmax : 0 ≤ bmax)
    (hinit : ∀ x, smin ≤ RPhysical x 0 * Real.exp (γ₁ x * uPhysical x 0) ∧
      RPhysical x 0 * Real.exp (γ₁ x * uPhysical x 0) ≤ smax)
    (ha : ∀ x t, 0 ≤ t →
      amin ≤ γ₂ x t * Rstar x ∧ γ₂ x t * Rstar x ≤ amax)
    (hb : ∀ x t, 0 ≤ t →
      bmin ≤ γ₂ x t * Real.exp (-(γ₁ x * uPhysical x t)) ∧
        γ₂ x t * Real.exp (-(γ₁ x * uPhysical x t)) ≤ bmax)
    (hz : ∀ x t, 0 ≤ t → |γ₁ x * uPhysical x t| ≤ Pbound)
    (huPhysical : ∀ x t, 0 ≤ t →
      HasDerivAt (uPhysical x) (utPhysical x t) t)
    (hRPhysical : ∀ x t, 0 ≤ t →
      HasDerivAt (RPhysical x) (RtPhysical x t) t)
    (hPhysicalODE : ∀ x t, 0 ≤ t →
      RtPhysical x t = -γ₁ x * RPhysical x t * utPhysical x t -
        γ₂ x t * RPhysical x t * (RPhysical x t - Rstar x))
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * RPhysical x t) (well j) measure)
    (R_L2 Rdot Udot reaction : ℝ → Lp ℝ 2 measure)
    (Kpressure : ℝ → (Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure))
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ Cmult CU Creact Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * RPhysical x (max τ 0))
    (hSRDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt R_L2 (Rdot t) t)
    (hKpressure : ∀ᵐ t ∂paperPositiveTime, ‖Kpressure t‖ ≤ Cmult)
    (hU : ∀ᵐ t ∂paperPositiveTime, ‖Udot t‖ ≤ CU)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Creact)
    (hL2ODE : ∀ᵐ t ∂paperPositiveTime,
      Rdot t = -(Kpressure t (Udot t)) - reaction t)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * (Cmult * CU + Creact))) /
        measure.real (well j) ≤ Mh)
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (α μcoer M : ℝ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (LB Lpsi LpsiRate LD LDRate : ℝ)
    (hBC : B₀ * C = 1)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μcoer) (hM : 0 < M) (hμM : μcoer ≤ M)
    (hvertexCoercive : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * ((smin⁻¹ + bmax / amin)⁻¹ / Real.exp Pbound) ∨ hV j = γmax * ((min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-Pbound))) →
      ∀ v : Fin r → ℝ,
        μcoer * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * ((smin⁻¹ + bmax / amin)⁻¹ / Real.exp Pbound) ∨ hV j = γmax * ((min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-Pbound))) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)))
    (hLB : 0 ≤ LB)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hB : ∀ᵐ t ∂paperPositiveTime,
      ‖paperPhysicalWellCLM
        (fun i j => B₀ (Sum.inl i) j) wellRegion β volume
        (paperNonnegativeTimeWellSensitivities measure well γ₁ (fun τ x => RPhysical x τ))
        α (paperPhysicalDemandScale α μcoer M) t‖ ≤ LB)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t) :
    let h := paperNonnegativeTimeWellSensitivities measure well γ₁ (fun τ x => RPhysical x τ)
    let κ := paperPhysicalDemandScale α μcoer M
    let δ := paperPhysicalDemandMargin α μcoer M
    δ < 1 ∧
      (∀ t, ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
             EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h α κ C t‖ ≤ δ) ∧
      (∀ᵐ t ∂paperPositiveTime,
        ‖deriv (fun s : ℝ =>
          Ring.inverse (paperPhysicalGainCLM
              (fun i j => B₀ (Sum.inl i) j)
              wellRegion β volume h α κ C s)
            (paperDemandPsi psi
              (paperPhysicalWellCLM
                (fun i j => B₀ (Sum.inl i) j)
                wellRegion β volume h α κ)
              FD D s)) t‖ ≤
          (1 / (1 - δ)) *
            (LpsiRate +
              (paperMatrixEuclideanOpNorm
                (paperPhysicalDemandRateGeometry
                  (fun i j => B₀ (Sum.inl i) j)
                  wellRegion β volume κ) * Mh) *
                  (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
          (1 / (1 - δ)) *
            ((paperMatrixEuclideanOpNorm
                (paperPhysicalDemandRateGeometry
                  (fun i j => B₀ (Sum.inl i) j)
                  wellRegion β volume κ) * Mh *
                paperMatrixEuclideanOpNorm C) *
              ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD))))) := by
  have hSRRate : ∀ᵐ t ∂paperPositiveTime,
      ‖Rdot t‖ ≤ Cmult * CU + Creact :=
    sr_rate_L2_from_pressure_ae measure Udot Rdot reaction Kpressure
      Cmult CU Creact hKpressure hU hreaction hL2ODE
  exact paper_physical_theorem2_certificates_from_original_sr_ode_ae
    measure well hs hfinite hpositive
    uPhysical utPhysical RPhysical RtPhysical
    γ₁ Rstar γ₂ γmin γmax
    smin smax amin amax bmin bmax Pbound
    hγmin hsmin hamin hbmin hbmax hinit ha hb hz
    huPhysical hRPhysical hPhysicalODE hγ hint
    R_L2 Rdot Kγ Cγ (Cmult * CU + Creact) Mh
    hCγ hK hrep hSRDeriv hSRRate hgeometry
    B₀ C wellRegion β volume α μcoer M psi psiRate FD D DRate
    LB Lpsi LpsiRate LD LDRate
    hBC hα hμ hM hμM hvertexCoercive hvertexUpper
    hLB hLpsi hLpsiRate hLD hLDRate hMh
    hpsi hpsiRate hB hD hDRate hpsiDeriv hDDeriv


end ReservoirSeismicityControl
