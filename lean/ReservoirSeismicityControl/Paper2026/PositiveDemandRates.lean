import ReservoirSeismicityControl.Paper2026.PositiveDemandBridge
import ReservoirSeismicityControl.PaperPhysicalEuclideanDemandBridge

/-!
# P5 — Appendix B (B19) for the corrected, positive signed-SR input

The existing proof of the a.e. derivative bound for G_W⁻¹ Ψ_W was written
for the legacy matrix with a negative SR coefficient.  The newest paper uses
a positive SR coefficient (15) because the signed tracking error cancels s.

This module transfers the *same* established derivative and inverse-gain
certificate to the physical positive matrix, using the exact matrix equality
proved in PositiveDemandBridge.  No new differentiation or stability theorem
is introduced, and the physical beta is NOT negated: '-β' occurs only as the
argument of a legacy algebraic definition.

The bounds on the regional perturbation, the physical well sensitivities,
the demand data and the vertex conditions are explicitly retained as inputs.
P0--P3 still need to show them from the paper's PDE/ODE assumptions.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- Physical well-control map, before nullspace allocation. -/
noncomputable def positiveDemandWellCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ) :
    ℝ → EuclideanSpace ℝ (Fin w) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => ReservoirSeismicityControl.paperMatrixToEuclideanCLM
    (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (h t) α κ)

/-- This identity is of entire functions, so it also transports Ψ+B F_D D
without assuming an independent bound on the demand correction. -/
theorem positive_demand_wellCLM_eq_legacy_rebased {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ) :
    positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ =
      ReservoirSeismicityControl.paperPhysicalWellCLM Bᵤ₀ wellRegion (-β) volume h α κ := by
  funext t
  change ReservoirSeismicityControl.paperMatrixToEuclideanCLM
      (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (h t) α κ) =
    ReservoirSeismicityControl.paperMatrixToEuclideanCLM
      (ReservoirSeismicityControl.paperPhysicalDemandWellMatrix
        Bᵤ₀ wellRegion (-β) volume (h t) α κ)
  rw [positive_demand_matrix_eq_legacy_rebased]

/-- The physical well-derivative geometry, with the pressure derivative zero. -/
noncomputable def positiveDemandRateGeometry {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 1) 0 κ

theorem positive_demand_rate_geometry_eq_legacy_rebased {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ) :
    positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ =
      ReservoirSeismicityControl.paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion (-β) volume κ := by
  change positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 1) 0 κ =
    ReservoirSeismicityControl.paperPhysicalDemandWellMatrix
      Bᵤ₀ wellRegion (-β) volume (fun _ => 1) 0 κ
  exact positive_demand_matrix_eq_legacy_rebased _ _ _ _ _ _ _

/-- Equation (B19), with the *positive* physical B(t), G_W(t)=B(t)C_W
and Ψ_W(t)=Ψ(t)+B(t)F_D D(t). This theorem removes the old negative-sign
interface, without asserting any of the as-yet-unverified PDE rate bounds. -/
theorem positive_demand_normalized_rate_ae
    {u r w : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (δ LB Lpsi LpsiRate LD LDRate Mh : ℝ)
    (hδ : δ < 1) (hLB : 0 ≤ LB)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hwellDeriv : ∀ j : Fin w, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hwellRate : ∀ j : Fin w, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
       |hRate t j| ≤ Mh)
    (hpsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psiRate t‖ ≤ LpsiRate)
    (hB : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
       ‖positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ t‖ ≤ LB)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
       HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
       HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
       ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
               EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
         positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C t‖ ≤ δ) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖deriv (fun s : ℝ =>
          Ring.inverse (positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C s)
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
  have hlegacyB : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖ReservoirSeismicityControl.paperPhysicalWellCLM Bᵤ₀ wellRegion (-β) volume h α κ t‖ ≤ LB := by
    simpa only [positive_demand_wellCLM_eq_legacy_rebased] using hB
  have hlegacyContraction : ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
             EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        ReservoirSeismicityControl.paperPhysicalGainCLM Bᵤ₀ wellRegion (-β) volume h α κ C t‖ ≤ δ := by
    intro t
    simpa only [positive_demand_gain_eq_legacy_rebased] using hcontraction t
  have hbase := ReservoirSeismicityControl.paper_physical_normalized_demand_rate_no_representation_assumptions_ae
    Bᵤ₀ wellRegion (-β) volume h hRate α κ C psi psiRate FD D DRate
    δ LB Lpsi LpsiRate LD LDRate Mh
    hδ hLB hLpsi hLpsiRate hLD hLDRate hMh
    hwellDeriv hwellRate hpsi hpsiRate hlegacyB hD hDRate
    hpsiDeriv hDDeriv hlegacyContraction
  simpa only [positive_demand_wellCLM_eq_legacy_rebased,
    positive_demand_gain_eq_legacy_rebased,
    positive_demand_rate_geometry_eq_legacy_rebased] using hbase

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_wellCLM_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_rate_geometry_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_normalized_rate_ae
