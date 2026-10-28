import ReservoirSeismicityControl.PaperPhysicalSRAveragesFinalCertificates
import ReservoirSeismicityControl.PaperPhysicalWellAverages
import ReservoirSeismicityControl.PaperPhysicalGainOpNormRates
import Mathlib.Tactic

/-!
# M3 — eliminate the independent physical demand well-operator norm bound

For Appendix B, the physical well operator is the sum of a CONSTANT pressure
matrix and a spatially varying SR matrix whose columns equal fixed geometric
columns multiplied by the actual average sensitivities h_j(t).

The proof produces a time-uniform induced Euclidean operator-norm bound from
only the positive spatial gamma1*R well-integral box of Appendix A.2.
The earlier Stage 59 Theorem 2 certificate assumes such an hB bound; this
module derives it constructively from the paper's physical coefficient bounds.
No demand/flux derivative, no pointwise gradient, no diagonal allocator and
no additional PDE regularity are assumed.

The explicit constant depends solely on the fixed pressure block, fixed well
geometry, and a scalar upper bound on the actual well averages.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- Split the actual physical well matrix into constant pressure and variable
SR blocks, without suppressing a pressure-to-SR coupling after allocation. -/
theorem paper_physical_well_matrix_pressure_plus_sr
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : Fin w → ℝ) (α κ : ℝ) :
    paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ =
      paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 0) α 0 +
      paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
        Matrix.diagonal h := by
  classical
  rw [← paper_physical_demand_rate_geometry_factor]
  ext i j
  cases i with
  | inl i =>
      change α * Bᵤ₀ i j = α * Bᵤ₀ i j + 0 * Bᵤ₀ i j
      ring
  | inr i =>
      change κ * paperPhysicalSRWellMatrix wellRegion β volume h i j =
        0 * paperPhysicalSRWellMatrix wellRegion β volume (fun _ => 0) i j +
          κ * paperPhysicalSRWellMatrix wellRegion β volume h i j
      ring

-- Increase the budget only for this matrix-norm proof; restore it below.
set_option maxHeartbeats 1500000

/-- Explicit induced Euclidean norm bound for the *unallocated* physical
well operator B(h), from the physical sensitivity box. The proof works with
abbreviations for the fixed pressure and geometry blocks to avoid repeated
large matrix elaborations. -/
theorem paper_physical_well_matrix_opNorm_from_scalar_box
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : Fin w → ℝ) (α κ H : ℝ)
    (hH : 0 ≤ H)
    (hh : ∀ j, |h j| ≤ H) :
    paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ) ≤
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 0) α 0) +
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * H := by
  classical
  let P : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 0) α 0
  let G : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ
  have hvec : ‖h‖ ≤ H := by
    apply (pi_norm_le_iff_of_nonneg hH).2
    intro j
    simpa only [Real.norm_eq_abs] using hh j
  have hdiag : ‖Matrix.diagonal h‖ ≤ H := by
    calc
      ‖Matrix.diagonal h‖ = ‖h‖ := Matrix.l2_opNorm_diagonal h
      _ ≤ H := hvec
  have hgeom : ‖G * Matrix.diagonal h‖ ≤ ‖G‖ * H := by
    calc
      ‖G * Matrix.diagonal h‖ ≤ ‖G‖ * ‖Matrix.diagonal h‖ :=
        Matrix.l2_opNorm_mul G (Matrix.diagonal h)
      _ ≤ ‖G‖ * H :=
        mul_le_mul_of_nonneg_left hdiag (norm_nonneg G)
  have hsplit :
      paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ =
        P + G * Matrix.diagonal h :=
    paper_physical_well_matrix_pressure_plus_sr Bᵤ₀ wellRegion β volume h α κ
  have hnorm :
      ‖paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ‖ ≤
        ‖P‖ + ‖G‖ * H := by
    calc
      ‖paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ‖ =
          ‖P + G * Matrix.diagonal h‖ := congrArg norm hsplit
      _ ≤ ‖P‖ + ‖G * Matrix.diagonal h‖ := norm_add_le _ _
      _ ≤ ‖P‖ + ‖G‖ * H := add_le_add_right hgeom ‖P‖
  simpa only [paperMatrixEuclideanOpNorm, ← Matrix.l2_opNorm_def, P, G] using hnorm

set_option maxHeartbeats 200000

/-- The physical SR box gives an explicit uniform LB for the actual
unallocated well control operator at EVERY real time. The negative-time
extension is the already verified frozen physical SR state, not a PDE claim
for t<0. In particular, this removes Stage 59's independent hB hypothesis. -/
theorem paper_physical_demand_wellCLM_bound_from_sr_integrals
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (measure : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        Rmin j ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * R t x) (well j) measure)
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (α κ : ℝ) :
    let H : ℝ := max 0 (γmax * Rmax)
    let LB : ℝ :=
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume
          (fun _ => 0) α 0) +
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * H
    ∀ t : ℝ,
      ‖paperPhysicalWellCLM Bᵤ₀ wellRegion β volume
        (paperNonnegativeTimeWellSensitivities measure well γ₁ R) α κ t‖ ≤ LB := by
  classical
  dsimp only
  let H : ℝ := max 0 (γmax * Rmax)
  have hH : 0 ≤ H := le_max_left _ _
  have hbox := paper_physical_well_sensitivity_box measure well γ₁ R
    γmin γmax Rmax Rmin hfinite hpositive hγmin hRmin hγ hR hint
  have hbounds (t : ℝ) (j : Fin w) :
      |paperNonnegativeTimeWellSensitivities measure well γ₁ R t j| ≤ H := by
    have hnonneg :
        0 ≤ paperNonnegativeTimeWellSensitivities measure well γ₁ R t j :=
      (mul_nonneg (le_of_lt hγmin) (le_of_lt (hRmin j))).trans (hbox.1 t j)
    calc
      |paperNonnegativeTimeWellSensitivities measure well γ₁ R t j| =
        paperNonnegativeTimeWellSensitivities measure well γ₁ R t j :=
          abs_of_nonneg hnonneg
      _ ≤ γmax * Rmax := hbox.2 t j
      _ ≤ H := le_max_right _ _
  intro t
  change paperMatrixEuclideanOpNorm
    (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume
      (paperNonnegativeTimeWellSensitivities measure well γ₁ R t) α κ) ≤ _
  exact paper_physical_well_matrix_opNorm_from_scalar_box
    Bᵤ₀ wellRegion β volume
    (paperNonnegativeTimeWellSensitivities measure well γ₁ R t)
    α κ H hH (hbounds t)

/-- The complete Stage 59 physical demand certificate, now WITHOUT an
independently assumed bound on the physical well operator. The remaining
finite vertex, spatial SR and regional perturbation hypotheses are displayed
explicitly. This does not prove the cited MIMO stability theorem. -/
theorem paper_physical_demand_certificate_without_well_operator_bound
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
    (Lpsi LpsiRate LD LDRate : ℝ)
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
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt D (DRate t) t) :
    let LB : ℝ :=
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandWellMatrix (fun i j => B₀ (Sum.inl i) j)
          wellRegion β volume (fun _ => 0) α 0) +
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry (fun i j => B₀ (Sum.inl i) j)
          wellRegion β volume (paperPhysicalDemandScale α μcoer M)) *
            max 0 (γmax * Rmax)
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
  let LB : ℝ :=
    paperMatrixEuclideanOpNorm
      (paperPhysicalDemandWellMatrix (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume (fun _ => 0) α 0) +
    paperMatrixEuclideanOpNorm
      (paperPhysicalDemandRateGeometry (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume (paperPhysicalDemandScale α μcoer M)) *
          max 0 (γmax * Rmax)
  have hLB : 0 ≤ LB := by
    dsimp [LB, paperMatrixEuclideanOpNorm]
    positivity
  have hB_all := paper_physical_demand_wellCLM_bound_from_sr_integrals
    measure well γ₁ Rphysical γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRmin hγ hR hint
    (fun i j => B₀ (Sum.inl i) j) wellRegion β volume α
    (paperPhysicalDemandScale α μcoer M)
  have hB : ∀ᵐ t ∂paperPositiveTime,
      ‖paperPhysicalWellCLM
        (fun i j => B₀ (Sum.inl i) j) wellRegion β volume
        (paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical)
        α (paperPhysicalDemandScale α μcoer M) t‖ ≤ LB := by
    exact Filter.Eventually.of_forall hB_all
  exact paper_physical_theorem2_certificates_from_sr_L2_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Kγ Cγ CR Mh hCγ hK hrep hSRDeriv hSRRate hgeometry
    B₀ C wellRegion β volume α μcoer M psi psiRate FD D DRate
    LB Lpsi LpsiRate LD LDRate hBC hα hμ hM hμM
    hvertexCoercive hvertexUpper
    hLB hLpsi hLpsiRate hLD hLDRate hMh
    hpsi hpsiRate hB hD hDRate hpsiDeriv hDDeriv

#print axioms ReservoirSeismicityControl.paper_physical_well_matrix_pressure_plus_sr
#print axioms ReservoirSeismicityControl.paper_physical_well_matrix_opNorm_from_scalar_box
#print axioms ReservoirSeismicityControl.paper_physical_demand_wellCLM_bound_from_sr_integrals
#print axioms ReservoirSeismicityControl.paper_physical_demand_certificate_without_well_operator_bound

end ReservoirSeismicityControl
