import ReservoirSeismicityControl.Paper2026.PositiveDemandPhysicalBounds
import ReservoirSeismicityControl.PaperPhysicalSRAveragesToDemand
import ReservoirSeismicityControl.SeismicityPhysicalL2RateBridge

/-!
# P5 / Appendix B (B19): actual SR well-integral derivative and norm inputs

Reuses the already verified L²-to-well-average a.e. derivative and rate
estimates (Stage 58) and the locally built physical positive well-operator
bound. It instantiates B19 without independently assuming the well-mean
rate, its differentiability, or an abstract bound on B(t).

The strong L² SR evolution, representative identity, regional Psi/Psi-dot,
demand derivative and corrected positive gain contraction remain explicit
paper-specific hypotheses. The second theorem derives the L² SR rate bound
from the signed pressure-to-SR evolution with an abstract multiplier K(t)
whose sign is included in that multiplier. It does not assume Q-dot.
No PDE regularity or external MIMO stability theorem is reproved.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- B19 for the actual physical Lebesgue averages: removes the *standalone*
well-average derivative, well-average rate, and B-operator bound hypotheses
from `positive_demand_normalized_rate_ae`. The remaining contraction is the
B16/B18 condition on the allocation, not an unconditional assertion. -/
theorem positive_demand_B19_from_actual_sr_L2_ae
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
    (R_L2 Rdot : ℝ → Lp ℝ 2 measure)
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ CR Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * Rphysical (max τ 0) x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R_L2 (Rdot t) t)
    (hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        measure.real (well j) ≤ Mh)
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ Lpsi LpsiRate LD LDRate : ℝ)
    (hδ : δ < 1)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hpsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psiRate t‖ ≤ LpsiRate)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        positiveDemandGainCLM Bᵤ₀ wellRegion β volume
          (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
            measure well γ₁ Rphysical) α κ C t‖ ≤ δ) :
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
  let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
    measure well γ₁ Rphysical
  let hRate := ReservoirSeismicityControl.paperPhysicalSRWellRateFromL2 measure well
    hs (fun j => ne_of_lt (hfinite j)) Kγ Rdot
  let LB : ℝ :=
    ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 0) α 0) +
    ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) *
        max 0 (γmax * Rmax)
  have hinputs := ReservoirSeismicityControl.paper_physical_sr_well_stage56_inputs_from_L2
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Kγ Cγ CR Mh hCγ hK hrep hSRDeriv hSRRate hgeometry
  have hLB : 0 ≤ LB := by
    dsimp [LB, ReservoirSeismicityControl.paperMatrixEuclideanOpNorm]
    positivity
  have hB_all := positive_demand_B19_well_operator_from_actual_sr_integrals
    measure well γ₁ Rphysical γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRmin hγ hR hint
    Bᵤ₀ wellRegion β volume α κ
  have hB : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ t‖ ≤ LB := by
    exact Filter.Eventually.of_forall hB_all
  exact positive_demand_normalized_rate_ae
    Bᵤ₀ wellRegion β volume h hRate α κ C
    psi psiRate FD D DRate
    δ LB Lpsi LpsiRate LD LDRate Mh
    hδ hLB hLpsi hLpsiRate hLD hLDRate hMh
    hinputs.2.2.1 hinputs.2.2.2
    hpsi hpsiRate hB hD hDRate hpsiDeriv hDDeriv hcontraction

/-- The same physical B19 certificate when the L² SR-rate bound is derived
from the strong pressure-to-SR equation rather than assumed separately.
For s in {-1, 1} the signed pressure coupling is carried inside `Kpressure`;
its required identity and multiplier norm bound are explicit premises. -/
theorem positive_demand_B19_from_sr_evolution_ae
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
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ Lpsi LpsiRate LD LDRate : ℝ)
    (hδ : δ < 1)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hpsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psiRate t‖ ≤ LpsiRate)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        positiveDemandGainCLM Bᵤ₀ wellRegion β volume
          (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
            measure well γ₁ Rphysical) α κ C t‖ ≤ δ) :
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
  have hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ Cmult * CU + Creact :=
    ReservoirSeismicityControl.sr_rate_L2_from_pressure_ae measure Udot Rdot reaction Kpressure
      Cmult CU Creact hKpressure hU hreaction hL2ODE
  exact positive_demand_B19_from_actual_sr_L2_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Kγ Cγ (Cmult * CU + Creact) Mh
    hCγ hK hrep hSRDeriv hSRRate hgeometry
    Bᵤ₀ wellRegion β volume α κ C psi psiRate FD D DRate
    δ Lpsi LpsiRate LD LDRate hδ hLpsi hLpsiRate hLD hLDRate hMh
    hpsi hpsiRate hD hDRate hpsiDeriv hDDeriv hcontraction

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_actual_sr_L2_ae
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_from_sr_evolution_ae
