import ReservoirSeismicityControl.PaperPhysicalNormalizedDemandRates
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Stage 55 — The physical matrix-to-Euclidean-operator bridge

The matrix derivative in Stage 52 uses the entrywise matrix norm.  The gain
and the rate estimates in Stages 53–54 use genuine Euclidean operator norms.
This file identifies their common finite-dimensional continuous-linear-map
representation and transports the *actual* physical derivatives through it.

In particular, the final theorem supplies, rather than assumes,
`hBDeriv`, `hGainDeriv`, `hBRateModel` and `hGainRateModel` from Stage 54.

The field estimate for `psiRate`, the bounds for physical B and D, and the
strict contraction (certified separately by the block/vertex lemmas) remain
explicit assumptions.  There are no Qdot or Qddot hypotheses.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix
open scoped Matrix.Norms.Elementwise

/-- Canonical real rectangular matrix → Euclidean continuous-linear-operator
linear equivalence. This is definitionally identical to the representation in
the Stage 53 `paperMatrixEuclideanOpNorm` definition. -/
noncomputable def paperMatrixToEuclideanCLM
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Matrix m n ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :=
  Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap

/-- The Euclidean norm of the *actual* matrix operator is exactly the
induced operator norm used for the physical Stage 53 rate bounds. -/
theorem paper_matrix_toEuclideanCLM_norm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ‖paperMatrixToEuclideanCLM A‖ = paperMatrixEuclideanOpNorm A := by
  rfl

/-- The finite-dimensional linear equivalence preserves actual derivatives.
Its underlying linear map is continuous. This is a conversion lemma, not an
assumed bound on a matrix derivative. -/
theorem paper_matrix_toEuclideanCLM_hasDerivAt
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix m n ℝ) (A' : Matrix m n ℝ) (t : ℝ)
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => paperMatrixToEuclideanCLM (A s))
      (paperMatrixToEuclideanCLM A') t := by
  let T : Matrix m n ℝ →L[ℝ]
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :=
    (paperMatrixToEuclideanCLM (m := m) (n := n)).toLinearMap.toContinuousLinearMap
  change HasDerivAt (fun s => T (A s)) (T A') t
  exact T.hasFDerivAt.comp_hasDerivAt t hA

/-- The genuine physical well matrix, represented as a continuous linear
map between well fluxes and pressure/SR outputs. -/
noncomputable def paperPhysicalWellCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ) :
    ℝ → EuclideanSpace ℝ (Fin w) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => paperMatrixToEuclideanCLM
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h t) α κ)

/-- The actual physical derivative candidate in the same Euclidean space. -/
noncomputable def paperPhysicalWellRateCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (hRate : ℝ → Fin w → ℝ) (κ : ℝ) :
    ℝ → EuclideanSpace ℝ (Fin w) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => paperMatrixToEuclideanCLM
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ)

/-- The true physical *allocated* demand gain, as a square CLM. -/
noncomputable def paperPhysicalGainCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => paperMatrixToEuclideanCLM
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h t) α κ * C)

/-- The true physical *allocated* gain derivative, as a square CLM. -/
noncomputable def paperPhysicalGainRateCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (hRate : ℝ → Fin w → ℝ) (κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => paperMatrixToEuclideanCLM
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ * C)

/-- Discharges Stage 54's derivative premise `hBDeriv`. -/
theorem paper_physical_wellCLM_hasDerivAt_ae {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (hd : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t) :
    ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (paperPhysicalWellCLM Bᵤ₀ wellRegion β volume h α κ)
        (paperPhysicalWellRateCLM Bᵤ₀ wellRegion β volume hRate κ t) t := by
  filter_upwards [paper_physical_well_rates_common_ae h hRate hd] with t ht
  exact paper_matrix_toEuclideanCLM_hasDerivAt
    (fun s => paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h s) α κ)
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ) t
    (paper_physical_demand_matrix_hasDerivAt
       Bᵤ₀ wellRegion β volume h hRate α κ t ht)

/-- Discharges Stage 54's derivative premise `hGainDeriv`. -/
theorem paper_physical_gainCLM_hasDerivAt_ae {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hd : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t) :
    ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (paperPhysicalGainCLM Bᵤ₀ wellRegion β volume h α κ C)
        (paperPhysicalGainRateCLM Bᵤ₀ wellRegion β volume hRate κ C t) t := by
  filter_upwards [paper_physical_well_rates_common_ae h hRate hd] with t ht
  exact paper_matrix_toEuclideanCLM_hasDerivAt
    (fun s => paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h s) α κ * C)
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ * C) t
    (paper_physical_demand_gain_hasDerivAt
       Bᵤ₀ wellRegion β volume h hRate α κ C t ht)

/-- Discharges Stage 54's `hBRateModel`, by *equality* rather than an
independently postulated inequality. -/
theorem paper_physical_wellCLM_rate_norm {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (hRate : ℝ → Fin w → ℝ) (κ : ℝ) (t : ℝ) :
    ‖paperPhysicalWellRateCLM Bᵤ₀ wellRegion β volume hRate κ t‖ =
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ) := by
  exact paper_matrix_toEuclideanCLM_norm _

/-- Discharges Stage 54's `hGainRateModel`, again by exact equality. -/
theorem paper_physical_gainCLM_rate_norm {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (hRate : ℝ → Fin w → ℝ) (κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) (t : ℝ) :
    ‖paperPhysicalGainRateCLM Bᵤ₀ wellRegion β volume hRate κ C t‖ =
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ * C) := by
  exact paper_matrix_toEuclideanCLM_norm _

/-- Stage 55 final: the normalized perturbation derivative of the *actual*
physical demand gain. Four Stage 54 matrix/operator bridge assumptions are now
lemmas. The SR/PDE bounds and contraction remain the theorem's explicit input
hypotheses; none concerns a derivative of the well flux Q. -/
theorem paper_physical_normalized_demand_rate_no_representation_assumptions_ae
    {u r w : ℕ}
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : R →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → R)
    (δ LB Lpsi LpsiRate LD LDRate M : ℝ)
    (hδ : δ < 1) (hLB : 0 ≤ LB)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hM : 0 ≤ M)
    (hwellDeriv : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hwellRate : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       |hRate t j| ≤ M)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hB : ∀ᵐ t ∂paperPositiveTime,
       ‖paperPhysicalWellCLM Bᵤ₀ wellRegion β volume h α κ t‖ ≤ LB)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt D (DRate t) t)
    (hcontraction : ∀ t,
       ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
               EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
         paperPhysicalGainCLM Bᵤ₀ wellRegion β volume h α κ C t‖ ≤ δ) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (fun s : ℝ =>
          Ring.inverse (paperPhysicalGainCLM Bᵤ₀ wellRegion β volume h α κ C s)
            (paperDemandPsi psi
               (paperPhysicalWellCLM Bᵤ₀ wellRegion β volume h α κ)
               FD D s)) t‖ ≤
        (1 / (1 - δ)) *
          (LpsiRate +
            (paperMatrixEuclideanOpNorm
              (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M) *
                (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
        (1 / (1 - δ)) *
          ((paperMatrixEuclideanOpNorm
              (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M *
                paperMatrixEuclideanOpNorm C) *
            ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD)))) := by
  have hBDeriv := paper_physical_wellCLM_hasDerivAt_ae
    Bᵤ₀ wellRegion β volume h hRate α κ hwellDeriv
  have hGainDeriv := paper_physical_gainCLM_hasDerivAt_ae
    Bᵤ₀ wellRegion β volume h hRate α κ C hwellDeriv
  have hBRateModel : ∀ᵐ t ∂paperPositiveTime,
      ‖paperPhysicalWellRateCLM Bᵤ₀ wellRegion β volume hRate κ t‖ ≤
      paperMatrixEuclideanOpNorm
        (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
          wellRegion β volume (h s) α κ) t) := by
    filter_upwards [paper_physical_well_rates_common_ae h hRate hwellDeriv]
      with t ht
    rw [paper_physical_demand_matrix_deriv
      Bᵤ₀ wellRegion β volume h hRate α κ t ht]
    exact le_of_eq (paper_physical_wellCLM_rate_norm
      Bᵤ₀ wellRegion β volume hRate κ t)
  have hGainRateModel : ∀ᵐ t ∂paperPositiveTime,
      ‖paperPhysicalGainRateCLM Bᵤ₀ wellRegion β volume hRate κ C t‖ ≤
      paperMatrixEuclideanOpNorm
        (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
          wellRegion β volume (h s) α κ * C) t) := by
    filter_upwards [paper_physical_well_rates_common_ae h hRate hwellDeriv]
      with t ht
    rw [paper_physical_demand_gain_deriv
      Bᵤ₀ wellRegion β volume h hRate α κ C t ht]
    exact le_of_eq (paper_physical_gainCLM_rate_norm
      Bᵤ₀ wellRegion β volume hRate κ C t)
  exact paper_physical_normalized_demand_rate_bound_ae
    Bᵤ₀ wellRegion β volume h hRate α κ C
    psi psiRate
    (paperPhysicalWellCLM Bᵤ₀ wellRegion β volume h α κ)
    (paperPhysicalWellRateCLM Bᵤ₀ wellRegion β volume hRate κ)
    FD D DRate
    (paperPhysicalGainCLM Bᵤ₀ wellRegion β volume h α κ C)
    (paperPhysicalGainRateCLM Bᵤ₀ wellRegion β volume hRate κ C)
    δ LB Lpsi LpsiRate LD LDRate M
    hδ hLB hLpsi hLpsiRate hLD hLDRate hM
    hwellDeriv hwellRate hpsi hpsiRate hB hD hDRate
    hpsiDeriv hBDeriv hDDeriv hGainDeriv
    hBRateModel hGainRateModel hcontraction

end ReservoirSeismicityControl
