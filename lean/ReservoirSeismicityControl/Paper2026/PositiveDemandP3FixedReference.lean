import ReservoirSeismicityControl.Paper2026.PositiveDemandP3CanonicalB19
import Mathlib.Tactic

/-!
# P3 / A2 / eq. (12): fixed reference normalization

The manuscript fixes the reference scaling: pressure channels have coefficient 1,
and SR channels have coefficient s/(gamma10*R0star). The earlier B19 theorem
accepted an arbitrary bounded linear reference operator. This module supplies
the literal diagonal matrix and specializes the existing, locally accepted B19
certificate to it. No additional regularity, PDE, or stability premise is added.

The a.e. strong reaction-field differentiation and near/far PDE estimates remain
explicit obligations; this module does not claim that Theorem 2 is closed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix BigOperators

/-- Equation (12): the exact pressure/SR reference normalizer. -/
noncomputable def paperReferenceScaleMatrix {u r : ℕ}
    (s gamma10 R0star : ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ :=
  Matrix.diagonal (fun k => match k with
    | Sum.inl _ => 1
    | Sum.inr _ => s / (gamma10 * R0star))

/-- The fixed normalization, represented as a continuous Euclidean map. -/
noncomputable def paperReferenceScaleCLM {u r : ℕ}
    (s gamma10 R0star : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
    (paperReferenceScaleMatrix (u := u) (r := r) s gamma10 R0star)

/-- The normalization does not alter pressure references. -/
theorem paper_reference_scale_pressure {u r : ℕ}
    (s gamma10 R0star : ℝ)
    (v : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) (i : Fin u) :
    (paperReferenceScaleCLM s gamma10 R0star v).ofLp (Sum.inl i) =
      v.ofLp (Sum.inl i) := by
  classical
  simp [paperReferenceScaleCLM, paperReferenceScaleMatrix,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

/-- Each SR reference receives exactly s/(gamma10*R0star). -/
theorem paper_reference_scale_SR {u r : ℕ}
    (s gamma10 R0star : ℝ)
    (v : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) (i : Fin r) :
    (paperReferenceScaleCLM s gamma10 R0star v).ofLp (Sum.inr i) =
      (s / (gamma10 * R0star)) * v.ofLp (Sum.inr i) := by
  classical
  simp [paperReferenceScaleCLM, paperReferenceScaleMatrix,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

/-- The fixed operator preserves the previously checked reference chain rule. -/
theorem paper_reference_scale_hasDerivAt {u r : ℕ}
    (s gamma10 R0star : ℝ)
    (v dv : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (t : ℝ) (hv : HasDerivAt v (dv t) t) :
    HasDerivAt
      (fun tau => -(paperReferenceScaleCLM s gamma10 R0star (v tau)))
      (-(paperReferenceScaleCLM s gamma10 R0star (dv t))) t := by
  exact ((paperReferenceScaleCLM s gamma10 R0star).hasFDerivAt.comp_hasDerivAt t hv).neg

/-- B19 with the literal fixed reference normalizer in equation (12). -/
theorem positive_demand_B19_from_A3_fixed_reference_ae
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
    (Lnear Lfar Lvelocity : ℝ)
    (LnearRate LfarRate Lacceleration : ℝ)
    (srRegions : Fin r → Set X)
    (hSRMeasurable : ∀ i, MeasurableSet (srRegions i))
    (hSRFinite : ∀ i, measure (srRegions i) ≠ ⊤)
    (hSRPositive : ∀ i, 0 < measure.real (srRegions i))
    (γ₂ γ₂Rate RRatePhysical : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
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
        sign gamma10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let reactionRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      physicalSRFiniteReactionRate measure srRegions γ₂ γ₂Rate Rphysical
        RRatePhysical Rstar sign gamma10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let Lreaction : ℝ := max 0 (∑ i : Fin r, ‖(paperSRCoordinateEmbed (u := u) (r := r)) i‖ *
      (|(-sign / (gamma10 * R0star))| *
        (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
          SRvalueBound i) / measure.real (srRegions i))))
    let LreactionRate : ℝ := max 0 (∑ i : Fin r, ‖(paperSRCoordinateEmbed (u := u) (r := r)) i‖ *
      (|(-sign / (gamma10 * R0star))| *
        (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
          (SRforcingBound i + SRmultiplierBound i *
            (Cmult * CU + Creact))) / measure.real (srRegions i))))
    let referencePsi : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      fun t => -((paperReferenceScaleCLM (u := u) (r := r) sign gamma10 R0star) (referenceVelocity t))
    let referenceRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      fun t => -((paperReferenceScaleCLM (u := u) (r := r) sign gamma10 R0star) (referenceAcceleration t))
    let Lreference : ℝ := ‖(paperReferenceScaleCLM (u := u) (r := r) sign gamma10 R0star)‖ * Lvelocity
    let LreferenceRate : ℝ := ‖(paperReferenceScaleCLM (u := u) (r := r) sign gamma10 R0star)‖ * Lacceleration
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
  exact positive_demand_B19_from_A3_canonical_SR_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Udot reaction Kpressure Kγ Cγ Cmult CU Creact Mh
    hCγ hK hrep hSRDeriv hKpressure hU hreaction hL2ODE hgeometry
    Bᵤ₀ wellRegion β volume α κ C
    nearPsi farPsi nearRate farRate
    referenceVelocity referenceAcceleration (paperReferenceScaleCLM (u := u) (r := r) sign gamma10 R0star)
    Lnear Lfar Lvelocity LnearRate LfarRate Lacceleration
    srRegions hSRMeasurable hSRFinite hSRPositive
    γ₂ γ₂Rate RRatePhysical Rstar sign gamma10 R0star
    SRF SRFdot SRforcing SRmultiplier
    gamma2M Lgamma2t RM RstarM
    hgamma2M hLgamma2t hRM hRstarM
    hSRRep hSRRateRep hSRStrong hSRDecomp
    hgammaA3 hRA3 hRstarA3
    hSRValueRep hSRForcingRep hSRMultiplierRep
    FD D DRate δ LD LDRate
    hδ hLnear hLfar hLvelocity hLnearRate hLfarRate hLacceleration
    hLD hLDRate hMh
    hnearBound hfarBound hvelocityBound
    hnearRateBound hfarRateBound haccelerationBound hD hDRate
    hnearDeriv hfarDeriv hvelocityDeriv hDDeriv hcontraction

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_pressure
#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_SR
#print axioms ReservoirSeismicityControl.Paper2026.paper_reference_scale_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_A3_fixed_reference_ae
