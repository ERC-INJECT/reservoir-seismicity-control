import ReservoirSeismicityControl.SeismicityUniformBounds
import ReservoirSeismicityControl.PaperPhysicalSRAveragesFinalCertificates

/-!
# Stage 60: original SR ODE to the demand-control certificate

The uniform physical SR comparison theorem from Appendix A.2 gives an
explicit strictly positive lower bound and finite upper bound for R.
This module passes those bounds to the *actual* spatial gamma₁*R well
averages, and then to the established demand-gain certificates.

Unlike Stage 59, the SR well positivity box is not a new assumption.
The remaining nontrivial physical hypotheses are still explicit:
  * pointwise differentiable SR and pressure trajectories solving the ODE;
  * strong L² SR representatives and their a.e. rate bounds;
  * integrability of physical well products;
  * regional Psi and its a.e. derivative;
  * bounded demand, vertex positivity/upper tests, matrix compatibility.
The pointwise-to-a.e. Caratheodory bridge and physical off-diagonal
observation bounds are NOT proved by this file.

No Qdot assumption, sorry, or custom axioms.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The original SR evolution law supplies the positivity box required by
Stage 59. The result is the same concrete demand-controller certificate,
with physical SR box constants derived from uniform logistic comparison. -/
theorem paper_physical_theorem2_certificates_from_original_sr_ode_ae
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
    (R_L2 Rdot : ℝ → Lp ℝ 2 measure)
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ CR Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * RPhysical x (max τ 0))
    (hSRDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt R_L2 (Rdot t) t)
    (hSRRate : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
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
  have hphysical := physical_sr_uniform_bounds_from_original_ode
    uPhysical utPhysical RPhysical RtPhysical γ₁ Rstar γ₂
    smin smax amin amax bmin bmax Pbound
    hsmin hinit hamin hbmin ha hb hz huPhysical hRPhysical hPhysicalODE
  have hpositiveLower :
      0 < (smin⁻¹ + bmax / amin)⁻¹ / Real.exp Pbound := by
    apply div_pos
    · apply inv_pos.mpr
      exact add_pos_of_pos_of_nonneg (inv_pos.mpr hsmin)
        (div_nonneg hbmax hamin.le)
    · exact Real.exp_pos _
  have hRbox : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        (smin⁻¹ + bmax / amin)⁻¹ / Real.exp Pbound ≤ RPhysical x t ∧
          RPhysical x t ≤ (min smax⁻¹ (bmin / amax))⁻¹ /
            Real.exp (-Pbound) := by
    intro t ht j
    exact Filter.Eventually.of_forall (fun x => hphysical x t ht)
  exact paper_physical_theorem2_certificates_from_sr_L2_ae
    measure well hs hfinite hpositive γ₁ (fun τ x => RPhysical x τ)
    γmin γmax
    ((min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-Pbound))
    (fun _ => (smin⁻¹ + bmax / amin)⁻¹ / Real.exp Pbound)
    hγmin (fun _ => hpositiveLower) hγ hRbox hint
    R_L2 Rdot Kγ Cγ CR Mh hCγ hK hrep hSRDeriv hSRRate hgeometry
    B₀ C wellRegion β volume α μcoer M psi psiRate FD D DRate
    LB Lpsi LpsiRate LD LDRate hBC hα hμ hM hμM
    hvertexCoercive hvertexUpper
    hLB hLpsi hLpsiRate hLD hLDRate hMh
    hpsi hpsiRate hB hD hDRate hpsiDeriv hDDeriv

end ReservoirSeismicityControl
