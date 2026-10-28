import ReservoirSeismicityControl.Paper2026.PositiveDemandP3PhysicalReaction
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionA3L2
import Mathlib.Tactic

/-!
# P3 -> B19: eliminate the three free SR-reaction L² norm premises

Appendix A.3 and Assumption 3 provide essential bounds on γ₂, γ₂,t, R and R*.
The already-verified finite-volume Hölder theorem converts them to the actual
L² value, forcing and multiplier bounds for all SR output regions, a.e. in time.
These *derived* bounds are supplied to the accepted signed SR reaction-to-B19
certificate. The extra representative and strong-L² product-rule conditions
are precisely the remaining mathematical applicability obligations; neither
Q_t nor a stronger pointwise estimate on R_t is assumed.

The theorem remains conditional on near/far diffusion bounds, a.e. product
rule, physical SR evolution, and Assumption 6. It does not prove stability.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped BigOperators Matrix

theorem positive_demand_B19_from_A3_reaction_P3_A2_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (measure : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        Rmin j ≤ Rphysical t x ∧ Rphysical t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * Rphysical t x) (well j) measure)
    (R_L2 Rdot Udot reaction : ℝ → Lp ℝ 2 measure)
    (Kpressure : ℝ → (Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure))
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ Cmult CU Creact Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * Rphysical (max τ 0) x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R_L2 (Rdot t) t)
    (hKpressure : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Kpressure t‖ ≤ Cmult)
    (hU : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Udot t‖ ≤ CU)
    (hreaction : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reaction t‖ ≤ Creact)
    (hL2ODE : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Rdot t = -(Kpressure t (Udot t)) - reaction t)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) *
        (Cγ * (Cmult * CU + Creact))) /
        measure.real (well j) ≤ Mh)
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (nearPsi farPsi :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (nearRate farRate :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceVelocity referenceAcceleration :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceScale :
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lnear Lfar Lvelocity : ℝ)
    (LnearRate LfarRate Lacceleration : ℝ)
    (srRegions : Fin r → Set X)
    (hSRMeasurable : ∀ i, MeasurableSet (srRegions i))
    (hSRFinite : ∀ i, measure (srRegions i) ≠ ⊤)
    (hSRPositive : ∀ i, 0 < measure.real (srRegions i))
    (γ₂ γ₂Rate RRatePhysical : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (srEmbed : Fin r →
      (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (SRF SRFdot SRforcing : Fin r → ℝ → Lp ℝ 2 measure)
    (SRmultiplier : Fin r → ℝ →
      (Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure))
    (gamma2M Lgamma2t RM RstarM : ℝ)
    (hgamma2M : 0 ≤ gamma2M) (hLgamma2t : 0 ≤ Lgamma2t)
    (hRM : 0 ≤ RM) (hRstarM : 0 ≤ RstarM)
    (hSRRep : ∀ i τ, ∀ᵐ x ∂(measure.restrict (srRegions i)),
      ((SRF i τ) x : ℝ) =
        γ₂ τ x * Rphysical τ x * (Rphysical τ x - Rstar x))
    (hSRRateRep : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂(measure.restrict (srRegions i)),
        ((SRFdot i t) x : ℝ) =
          physicalSRReactionRateIntegrand γ₂ γ₂Rate Rphysical
            RRatePhysical Rstar t x)
    (hSRStrong : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt (SRF i) (SRFdot i t) t)
    (hSRDecomp : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      SRFdot i t = SRforcing i t + SRmultiplier i t (Rdot t))
    (hgammaA3 : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂measure, x ∈ srRegions i →
        0 ≤ γ₂ t x ∧ γ₂ t x ≤ gamma2M ∧
        |γ₂Rate t x| ≤ Lgamma2t)
    (hRA3 : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂measure, x ∈ srRegions i →
        0 ≤ Rphysical t x ∧ Rphysical t x ≤ RM)
    (hRstarA3 : ∀ i, ∀ᵐ x ∂measure,
      x ∈ srRegions i → 0 ≤ Rstar x ∧ Rstar x ≤ RstarM)
    (hSRValueRep : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂measure, ((SRF i t) x : ℝ) =
        (srRegions i).indicator (fun y =>
          γ₂ t y * Rphysical t y * (Rphysical t y - Rstar y)) x)
    (hSRForcingRep : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂measure, ((SRforcing i t) x : ℝ) =
        (srRegions i).indicator (fun y =>
          γ₂Rate t y * Rphysical t y * (Rphysical t y - Rstar y)) x)
    (hSRMultiplierRep : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ f : Lp ℝ 2 measure, ∀ᵐ x ∂measure,
        ((SRmultiplier i t f) x : ℝ) =
          (srRegions i).indicator (fun y =>
            γ₂ t y * (2 * Rphysical t y - Rstar y) * (f y : ℝ)) x)
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ LD LDRate : ℝ)
    (hδ : δ < 1)
    (hLnear : 0 ≤ Lnear) (hLfar : 0 ≤ Lfar)
    (hLvelocity : 0 ≤ Lvelocity)
    (hLnearRate : 0 ≤ LnearRate) (hLfarRate : 0 ≤ LfarRate)
    (hLacceleration : 0 ≤ Lacceleration)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hnearBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearPsi t‖ ≤ Lnear)
    (hfarBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farPsi t‖ ≤ Lfar)
    (hvelocityBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceVelocity t‖ ≤ Lvelocity)
    (hnearRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearRate t‖ ≤ LnearRate)
    (hfarRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farRate t‖ ≤ LfarRate)
    (haccelerationBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceAcceleration t‖ ≤ Lacceleration)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hnearDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt nearPsi (nearRate t) t)
    (hfarDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt farPsi (farRate t) t)
    (hvelocityDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt referenceVelocity (referenceAcceleration t) t)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        positiveDemandGainCLM Bᵤ₀ wellRegion β volume
          (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
            measure well γ₁ Rphysical) α κ C t‖ ≤ δ) :
    let SRvalueBound : Fin r → ℝ := fun i =>
      gamma2M * RM * (RM + RstarM) *
        (measure.real (srRegions i)) ^ (1 / (2 : ℝ))
    let SRforcingBound : Fin r → ℝ := fun i =>
      Lgamma2t * RM * (RM + RstarM) *
        (measure.real (srRegions i)) ^ (1 / (2 : ℝ))
    let SRmultiplierBound : Fin r → ℝ := fun _ =>
      gamma2M * (2 * RM + RstarM)
    let reactionPsi : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      physicalSRFiniteReactionPsi measure srRegions γ₂ Rphysical Rstar
        sign gamma10 R0star srEmbed
    let reactionRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      physicalSRFiniteReactionRate measure srRegions γ₂ γ₂Rate Rphysical
        RRatePhysical Rstar sign gamma10 R0star srEmbed
    let Lreaction : ℝ := max 0 (∑ i : Fin r, ‖srEmbed i‖ *
      (|(-sign / (gamma10 * R0star))| *
        (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
          SRvalueBound i) / measure.real (srRegions i))))
    let LreactionRate : ℝ := max 0 (∑ i : Fin r, ‖srEmbed i‖ *
      (|(-sign / (gamma10 * R0star))| *
        (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
          (SRforcingBound i + SRmultiplierBound i *
            (Cmult * CU + Creact))) / measure.real (srRegions i))))
    let referencePsi : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      fun t => -(referenceScale (referenceVelocity t))
    let referenceRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      fun t => -(referenceScale (referenceAcceleration t))
    let Lreference : ℝ := ‖referenceScale‖ * Lvelocity
    let LreferenceRate : ℝ := ‖referenceScale‖ * Lacceleration
    let psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents
      nearPsi farPsi reactionPsi referencePsi
    let psiRate := ReservoirSeismicityControl.paperRegionalPsiRateFromComponents
      nearRate farRate reactionRate referenceRate
    let Lpsi : ℝ := Lnear + Lfar + Lreaction + Lreference
    let LpsiRate : ℝ :=
      LnearRate + LfarRate + LreactionRate + LreferenceRate
    let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
      measure well γ₁ Rphysical
    let LB :=
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume
          (fun _ => 0) α 0) +
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) *
          max 0 (γmax * Rmax)
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖deriv (fun s : ℝ =>
          Ring.inverse
            (positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C s)
            (ReservoirSeismicityControl.paperDemandPsi psi
              (positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ)
              FD D s)) t‖ ≤
        (1 / (1 - δ)) *
          (LpsiRate +
            (ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
              (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh) *
                (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
        (1 / (1 - δ)) *
          ((ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
              (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh *
                ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C) *
            ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD)))) := by
  classical
  let SRvalueBound : Fin r → ℝ := fun i =>
    gamma2M * RM * (RM + RstarM) *
      (measure.real (srRegions i)) ^ (1 / (2 : ℝ))
  let SRforcingBound : Fin r → ℝ := fun i =>
    Lgamma2t * RM * (RM + RstarM) *
      (measure.real (srRegions i)) ^ (1 / (2 : ℝ))
  let SRmultiplierBound : Fin r → ℝ := fun _ =>
    gamma2M * (2 * RM + RstarM)

  -- The *same* A3 constants bound the actual reaction, coefficient forcing,
  -- and multiplication operator, for almost every time in every output region.
  have hAll (i : Fin r) :
      ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖SRF i t‖ ≤ SRvalueBound i ∧
        ‖SRforcing i t‖ ≤ SRforcingBound i ∧
        ‖SRmultiplier i t‖ ≤ SRmultiplierBound i := by
    filter_upwards [hgammaA3 i, hRA3 i, hSRValueRep i,
      hSRForcingRep i, hSRMultiplierRep i] with t hγ hR hV hF hK
    exact physical_sr_A3_actual_reaction_L2_bounds
      measure (srRegions i) (hSRMeasurable i) (hSRFinite i)
      (γ₂ t) (γ₂Rate t) (Rphysical t) Rstar
      gamma2M Lgamma2t RM RstarM
      hgamma2M hLgamma2t hRM hRstarM
      (SRF i t) (SRforcing i t) (SRmultiplier i t)
      hγ hR (hRstarA3 i) hV hF hK
  have hSRValue : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRF i t‖ ≤ SRvalueBound i := by
    intro i
    filter_upwards [hAll i] with t h
    exact h.1
  have hSRForcing : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRforcing i t‖ ≤ SRforcingBound i := by
    intro i
    filter_upwards [hAll i] with t h
    exact h.2.1
  have hSRMultiplier : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRmultiplier i t‖ ≤ SRmultiplierBound i := by
    intro i
    filter_upwards [hAll i] with t h
    exact h.2.2

  -- Reuse the accepted physical P3/A2-to-B19 certificate unchanged.
  -- No new bound on the aggregate perturbation is assumed.
  exact positive_demand_B19_from_physical_sr_reaction_P3_A2_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Udot reaction Kpressure Kγ Cγ Cmult CU Creact Mh
    hCγ hK hrep hSRDeriv hKpressure hU hreaction hL2ODE hgeometry
    Bᵤ₀ wellRegion β volume α κ C
    nearPsi farPsi nearRate farRate
    referenceVelocity referenceAcceleration referenceScale
    Lnear Lfar Lvelocity LnearRate LfarRate Lacceleration
    srRegions hSRMeasurable hSRFinite hSRPositive
    γ₂ γ₂Rate RRatePhysical Rstar sign gamma10 R0star srEmbed
    SRF SRFdot SRforcing SRmultiplier
    SRvalueBound SRforcingBound SRmultiplierBound
    hSRRep hSRRateRep hSRStrong hSRDecomp
    hSRValue hSRForcing hSRMultiplier
    FD D DRate δ LD LDRate hδ hLnear hLfar
    hLvelocity hLnearRate hLfarRate hLacceleration
    hLD hLDRate hMh hnearBound hfarBound hvelocityBound
    hnearRateBound hfarRateBound haccelerationBound
    hD hDRate hnearDeriv hfarDeriv hvelocityDeriv
    hDDeriv hcontraction

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_reaction_P3_A2_ae
