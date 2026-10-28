import ReservoirSeismicityControl.Paper2026.PositiveDemandP3Bridge

/-!
# P3 / Assumption 2: physical reference contribution in B19

Appendix A.3 defines the reference contribution as minus the reference
velocity after fixed output-error normalization. For SR regions that fixed
normalization carries `s/(gamma10 * R0star)`; for pressure regions it is 1.
The concrete normalization is passed as `referenceScale`, a constant bounded
linear map on the finite output space, not a newly postulated derivative.

This theorem removes three independent P3/B19 inputs: the reference
component bound, its derivative bound, and its HasDerivAt certificate.
They follow from Assumption 2's bounded reference first and second time
derivatives and the elementary chain rule for a fixed linear map.

Remaining P3 hypotheses (near/far diffusion and SR reaction components) are
unchanged. In particular no Qdot or new semigroup theory is introduced.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- A.3 reference part, specializing the passed P3-to-B19 theorem to the
actual negative time derivative of the normalized reference. -/
theorem positive_demand_B19_from_sr_evolution_P3_A2_ae
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
    (nearPsi farPsi reactionPsi :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (nearRate farRate reactionRate :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceVelocity referenceAcceleration :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceScale :
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lnear Lfar Lreaction Lvelocity : ℝ)
    (LnearRate LfarRate LreactionRate Lacceleration : ℝ)
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ LD LDRate : ℝ)
    (hδ : δ < 1)
    (hLnear : 0 ≤ Lnear) (hLfar : 0 ≤ Lfar)
    (hLreaction : 0 ≤ Lreaction) (hLvelocity : 0 ≤ Lvelocity)
    (hLnearRate : 0 ≤ LnearRate) (hLfarRate : 0 ≤ LfarRate)
    (hLreactionRate : 0 ≤ LreactionRate)
    (hLacceleration : 0 ≤ Lacceleration)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hnearBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearPsi t‖ ≤ Lnear)
    (hfarBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farPsi t‖ ≤ Lfar)
    (hreactionBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionPsi t‖ ≤ Lreaction)
    (hvelocityBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceVelocity t‖ ≤ Lvelocity)
    (hnearRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearRate t‖ ≤ LnearRate)
    (hfarRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farRate t‖ ≤ LfarRate)
    (hreactionRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionRate t‖ ≤ LreactionRate)
    (haccelerationBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceAcceleration t‖ ≤ Lacceleration)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hnearDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt nearPsi (nearRate t) t)
    (hfarDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt farPsi (farRate t) t)
    (hreactionDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt reactionPsi (reactionRate t) t)
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
  let referencePsi : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun t => -(referenceScale (referenceVelocity t))
  let referenceRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun t => -(referenceScale (referenceAcceleration t))
  let Lreference : ℝ := ‖referenceScale‖ * Lvelocity
  let LreferenceRate : ℝ := ‖referenceScale‖ * Lacceleration
  have hLreference : 0 ≤ Lreference :=
    mul_nonneg (norm_nonneg referenceScale) hLvelocity
  have hLreferenceRate : 0 ≤ LreferenceRate :=
    mul_nonneg (norm_nonneg referenceScale) hLacceleration
  have hreferenceBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referencePsi t‖ ≤ Lreference := by
    filter_upwards [hvelocityBound] with t ht
    change ‖-(referenceScale (referenceVelocity t))‖ ≤ ‖referenceScale‖ * Lvelocity
    calc
      _ = ‖referenceScale (referenceVelocity t)‖ := norm_neg _
      _ ≤ ‖referenceScale‖ * ‖referenceVelocity t‖ := referenceScale.le_opNorm _
      _ ≤ ‖referenceScale‖ * Lvelocity :=
        mul_le_mul_of_nonneg_left ht (norm_nonneg referenceScale)
  have hreferenceRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceRate t‖ ≤ LreferenceRate := by
    filter_upwards [haccelerationBound] with t ht
    change ‖-(referenceScale (referenceAcceleration t))‖ ≤
      ‖referenceScale‖ * Lacceleration
    calc
      _ = ‖referenceScale (referenceAcceleration t)‖ := norm_neg _
      _ ≤ ‖referenceScale‖ * ‖referenceAcceleration t‖ := referenceScale.le_opNorm _
      _ ≤ ‖referenceScale‖ * Lacceleration :=
        mul_le_mul_of_nonneg_left ht (norm_nonneg referenceScale)
  have hreferenceDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt referencePsi (referenceRate t) t := by
    filter_upwards [hvelocityDeriv] with t ht
    change HasDerivAt (fun s => -(referenceScale (referenceVelocity s)))
      (-(referenceScale (referenceAcceleration t))) t
    exact (referenceScale.hasFDerivAt.comp_hasDerivAt t ht).neg
  let psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents
    nearPsi farPsi reactionPsi referencePsi
  let psiRate := ReservoirSeismicityControl.paperRegionalPsiRateFromComponents
    nearRate farRate reactionRate referenceRate
  let Lpsi : ℝ := Lnear + Lfar + Lreaction + Lreference
  let LpsiRate : ℝ :=
    LnearRate + LfarRate + LreactionRate + LreferenceRate
  have hLpsi : 0 ≤ Lpsi := by
    dsimp [Lpsi]
    positivity
  have hLpsiRate : 0 ≤ LpsiRate := by
    dsimp [LpsiRate]
    positivity
  have hpsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi := by
    exact ReservoirSeismicityControl.paper_regional_psi_norm_from_components_ae
      nearPsi farPsi reactionPsi referencePsi
      Lnear Lfar Lreaction Lreference
      hnearBound hfarBound hreactionBound hreferenceBound
  have hpsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psiRate t‖ ≤ LpsiRate := by
    exact ReservoirSeismicityControl.paper_regional_psi_rate_from_components_ae
      nearRate farRate reactionRate referenceRate
      LnearRate LfarRate LreactionRate LreferenceRate
      hnearRateBound hfarRateBound hreactionRateBound hreferenceRateBound
  have hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t := by
    exact ReservoirSeismicityControl.paper_regional_psi_hasDerivAt_from_components_ae
      nearPsi farPsi reactionPsi referencePsi
      nearRate farRate reactionRate referenceRate
      hnearDeriv hfarDeriv hreactionDeriv hreferenceDeriv
  exact positive_demand_B19_from_sr_evolution_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Udot reaction Kpressure Kγ Cγ Cmult CU Creact Mh
    hCγ hK hrep hSRDeriv hKpressure hU hreaction hL2ODE hgeometry
    Bᵤ₀ wellRegion β volume α κ C psi psiRate FD D DRate
    δ Lpsi LpsiRate LD LDRate hδ hLpsi hLpsiRate hLD hLDRate hMh
    hpsi hpsiRate hD hDRate hpsiDeriv hDDeriv hcontraction


end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_A2_ae
