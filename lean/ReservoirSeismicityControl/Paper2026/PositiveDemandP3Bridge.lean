import ReservoirSeismicityControl.Paper2026.PositiveDemandPhysicalRates
import ReservoirSeismicityControl.PaperRegionalPerturbationComponents

/-!
# P3 → P5: regional perturbation components in the B19 certificate

This is the exact Appendix A.3 to Appendix B interface: instead of assuming
bounds and an a.e. derivative for the entire regional perturbation, build
Psi and its derivative from the near, far, SR reaction and reference terms.
The existing Stage 60 component assembly proves all three formerly independent
Psi premises of B19. The existing P5 strong L2 SR evolution proof is reused.

The component derivatives and bounds, in particular the off-diagonal far
term and near-well regularity, remain explicit obligations of Appendix A.3.
They are NOT asserted to follow unconditionally from A1--A6 here. No Qdot
assumption or foundational PDE/stability theorem is introduced.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- P3/P5 certificate: transport the A.3 component derivative and bounds to
B19 for the physical SR well integrals and signed L2 evolution. -/
theorem positive_demand_B19_from_sr_evolution_P3_ae
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
    (nearPsi farPsi reactionPsi referencePsi :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (nearRate farRate reactionRate referenceRate :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lnear Lfar Lreaction Lreference : ℝ)
    (LnearRate LfarRate LreactionRate LreferenceRate : ℝ)
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ LD LDRate : ℝ)
    (hδ : δ < 1)
    (hLnear : 0 ≤ Lnear) (hLfar : 0 ≤ Lfar)
    (hLreaction : 0 ≤ Lreaction) (hLreference : 0 ≤ Lreference)
    (hLnearRate : 0 ≤ LnearRate) (hLfarRate : 0 ≤ LfarRate)
    (hLreactionRate : 0 ≤ LreactionRate)
    (hLreferenceRate : 0 ≤ LreferenceRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hnearBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearPsi t‖ ≤ Lnear)
    (hfarBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farPsi t‖ ≤ Lfar)
    (hreactionBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionPsi t‖ ≤ Lreaction)
    (hreferenceBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referencePsi t‖ ≤ Lreference)
    (hnearRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖nearRate t‖ ≤ LnearRate)
    (hfarRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖farRate t‖ ≤ LfarRate)
    (hreactionRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionRate t‖ ≤ LreactionRate)
    (hreferenceRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceRate t‖ ≤ LreferenceRate)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hnearDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt nearPsi (nearRate t) t)
    (hfarDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt farPsi (farRate t) t)
    (hreactionDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt reactionPsi (reactionRate t) t)
    (hreferenceDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt referencePsi (referenceRate t) t)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        positiveDemandGainCLM Bᵤ₀ wellRegion β volume
          (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
            measure well γ₁ Rphysical) α κ C t‖ ≤ δ) :
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

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_P3_ae
