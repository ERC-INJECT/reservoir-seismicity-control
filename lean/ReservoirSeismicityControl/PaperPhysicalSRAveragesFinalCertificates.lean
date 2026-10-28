import ReservoirSeismicityControl.PaperPhysicalSRAveragesToDemand

/-!
# Stage 59: integrate physical SR well averages with the demand-controller certificate

Stages 49--51 and 58 derive the sensitivities and their a.e. derivatives from
actual normalized well integrals of gamma₁ * R. Stage 56 proves a uniform
Euclidean gain contraction and an a.e. normalized-perturbation derivative bound
when those sensitivity estimates are available.

This module instantiates Stage 56 with the *actual* well averages, so that the
sensitivity-box, sensitivity-differentiability, and sensitivity-rate hypotheses
are no longer independently assumed in the final certificate.

Remaining analytic premises are displayed in the theorem: the strong L² SR
trajectory, its physical representative and rate bound (Appendix A.2), the
regional perturbation and its derivative (Appendix A.3), bounded demand and
its derivative, and the Appendix B allocation/vertex assumptions.

In particular, neither Qdot nor Qddot is a hypothesis. This theorem does not
formalize the external MIMO super-twisting stability theorem or claim to have
proved PDE-ODE existence from the raw coefficients.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- Stage 56, specialized to the *physical* gamma₁-weighted well averages.
All four Stage 56 premises `hlo`, `hhi`, `hwellDeriv` and `hwellRate`
are derived by Stage 58, not supplied as independent assumptions here. -/
theorem paper_physical_theorem2_certificates_from_sr_L2_ae
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
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ v : Fin r → ℝ,
        μcoer * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
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
        (paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical)
        α (paperPhysicalDemandScale α μcoer M) t‖ ≤ LB)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t) :
    let h := paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical
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
  have hinputs := paper_physical_sr_well_stage56_inputs_from_L2
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Kγ Cγ CR Mh hCγ hK hrep hSRDeriv hSRRate hgeometry
  rcases hinputs with ⟨hlo, hhi, hwellDeriv, hwellRate⟩
  exact paper_physical_theorem2_certificates_from_vertices_ae
    B₀ C wellRegion β volume
    (fun j => γmin * Rmin j) (fun _ => γmax * Rmax)
    (paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical)
    (paperPhysicalSRWellRateFromL2 measure well hs
      (fun k => ne_of_lt (hfinite k)) Kγ Rdot)
    α μcoer M psi psiRate FD D DRate
    LB Lpsi LpsiRate LD LDRate Mh
    hBC hα hμ hM hμM hlo hhi hvertexCoercive hvertexUpper
    hLB hLpsi hLpsiRate hLD hLDRate hMh
    hwellDeriv hwellRate hpsi hpsiRate hB hD hDRate
    hpsiDeriv hDDeriv

end ReservoirSeismicityControl
