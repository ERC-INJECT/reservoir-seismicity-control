import ReservoirSeismicityControl.Paper2026.PositiveSRReactionValue
import ReservoirSeismicityControl.Paper2026.PositiveDemandP3References
import Mathlib.Tactic

/-!
# P3 -> P5: signed finite-region SR reaction in the physical B19 certificate

The finite-dimensional reaction input is the *actual* normalized signed
regional integral from Appendix A.3, with its derivative given by the actual
reaction-rate integrand. The previously independent reactionPsi, reactionRate,
reaction amplitude, derivative amplitude and derivative identity hypotheses
of the accepted P3/A2 B19 theorem are removed.

External applicability obligations are preserved explicitly: A3 coefficient
bounds, L2 representatives/strong product rule, and the physical signed SR
ODE; PDE near/far estimates and Assumption 6 vertex tests are still open.
No new assumptions about the final Psi, Qdot, or MIMO stability are added.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped BigOperators Matrix

/-- Appendix A.3 finite-region reaction component, transported into the
accepted Appendix B B19 a.e. normalized demand derivative certificate. -/
theorem positive_demand_B19_from_physical_sr_reaction_P3_A2_ae
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
    (SRvalueBound SRforcingBound SRmultiplierBound : Fin r → ℝ)
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
    (hSRValue : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRF i t‖ ≤ SRvalueBound i)
    (hSRForcing : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRforcing i t‖ ≤ SRforcingBound i)
    (hSRMultiplier : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖SRmultiplier i t‖ ≤ SRmultiplierBound i)
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
  have hSRValueAll : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ i : Fin r, ‖SRF i t‖ ≤ SRvalueBound i := by
    have hFinite (s : Finset (Fin r)) :
        ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
          ∀ i ∈ s, ‖SRF i t‖ ≤ SRvalueBound i := by
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with t
          simp
      | @insert a s ha ih =>
          filter_upwards [hSRValue a, ih] with t hat hst i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hat
          · exact hst i his
    filter_upwards [hFinite Finset.univ] with t ht i
    exact ht i (Finset.mem_univ i)
  have hreactionBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionPsi t‖ ≤ Lreaction := by
    filter_upwards [hSRValueAll] with t ht
    dsimp [reactionPsi, Lreaction]
    calc
      ‖physicalSRFiniteReactionPsi measure srRegions γ₂ Rphysical Rstar
          sign gamma10 R0star srEmbed t‖ ≤
        ∑ i : Fin r, ‖srEmbed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
              ‖SRF i t‖) / measure.real (srRegions i))) :=
        physical_sr_finite_reaction_value_from_L2
          measure srRegions hSRMeasurable hSRFinite hSRPositive
          γ₂ Rphysical Rstar sign gamma10 R0star
          srEmbed (fun i => SRF i t) t (fun i => hSRRep i t)
      _ ≤ ∑ i : Fin r, ‖srEmbed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
              SRvalueBound i) / measure.real (srRegions i))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hroot : 0 ≤ (measure.real (srRegions i)) ^ (1 / (2 : ℝ)) := by
          positivity
        have hmean :
            ((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) * ‖SRF i t‖) /
                measure.real (srRegions i) ≤
              ((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) * SRvalueBound i) /
                measure.real (srRegions i) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ht i) hroot) (hSRPositive i).le
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmean (abs_nonneg _))
          (norm_nonneg (srEmbed i))
      _ ≤ max 0 (∑ i : Fin r, ‖srEmbed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
              SRvalueBound i) / measure.real (srRegions i)))) :=
        le_max_right _ _
  have hreactionAE : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt reactionPsi (reactionRate t) t ∧
      ‖reactionRate t‖ ≤
        ∑ i : Fin r, ‖srEmbed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((measure.real (srRegions i)) ^ (1 / (2 : ℝ)) *
              (SRforcingBound i + SRmultiplierBound i *
                (Cmult * CU + Creact))) / measure.real (srRegions i))) := by
    exact physical_sr_finite_reaction_ae_from_evolution
      measure srRegions hSRMeasurable hSRFinite hSRPositive
      γ₂ γ₂Rate Rphysical RRatePhysical Rstar sign gamma10 R0star
      srEmbed SRF SRFdot SRforcing SRmultiplier
      Rdot Udot reaction Kpressure SRforcingBound SRmultiplierBound
      Cmult CU Creact hSRRep hSRRateRep hSRStrong hSRDecomp
      hSRForcing hSRMultiplier hKpressure hU hreaction hL2ODE
  have hreactionRateBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reactionRate t‖ ≤ LreactionRate := by
    filter_upwards [hreactionAE] with t ht
    exact le_trans ht.2 (le_max_right _ _)
  have hreactionDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt reactionPsi (reactionRate t) t := by
    filter_upwards [hreactionAE] with t ht
    exact ht.1
  exact positive_demand_B19_from_sr_evolution_P3_A2_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Udot reaction Kpressure Kγ Cγ Cmult CU Creact Mh
    hCγ hK hrep hSRDeriv hKpressure hU hreaction hL2ODE hgeometry
    Bᵤ₀ wellRegion β volume α κ C
    nearPsi farPsi reactionPsi nearRate farRate reactionRate
    referenceVelocity referenceAcceleration referenceScale
    Lnear Lfar Lreaction Lvelocity
    LnearRate LfarRate LreactionRate Lacceleration
    FD D DRate δ LD LDRate hδ hLnear hLfar
    (le_max_left _ _) hLvelocity hLnearRate hLfarRate
    (le_max_left _ _) hLacceleration hLD hLDRate hMh
    hnearBound hfarBound hreactionBound hvelocityBound
    hnearRateBound hfarRateBound hreactionRateBound haccelerationBound
    hD hDRate hnearDeriv hfarDeriv hreactionDeriv
    hvelocityDeriv hDDeriv hcontraction

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_physical_sr_reaction_P3_A2_ae
