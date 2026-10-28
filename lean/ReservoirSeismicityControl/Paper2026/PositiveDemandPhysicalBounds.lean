import ReservoirSeismicityControl.Paper2026.PositiveDemandAllocation
import ReservoirSeismicityControl.PaperPhysicalDemandWellNormFromSR

/-!
# P5 / Appendix B — actual SR well integrals in the allocation certificate

The B16/B18 theorem currently accepts a function `h` with an assumed box.
Appendix B does not posit arbitrary `h`: its components are the *actual* well
averages of gamma_1 R.  The existing `paper_physical_well_sensitivity_box`
proves the box from the local A.2 bounds.  We instantiate the positive,
non-diagonal B16 and the constructed nullspace allocator with those integrals.

The existing operator-norm estimate on the physical unallocated well matrix
is likewise transported from the old sign convention to the positive SR row.
No new PDE estimate, convexity theorem or stability theorem is proved.

Unresolved physical premises are explicit: local pointwise SR bounds and
integrability, the allocation inverse certificates and finite B16 vertex
conditions, and a.e. derivative/perturbation-rate bounds for B19.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- Appendix B's physical h_j(t) satisfies the finite B16 box. Therefore the
nominal inverse and the finite vertex conditions imply the B18 contraction
for the *actual SR well integrals* and the *constructed* C_W = N J. This
removes both independent hypotheses `lo ≤ h` and `h ≤ hi` from P5. -/
theorem positive_demand_B18_from_actual_sr_integrals
    {X : Type*} [MeasurableSpace X] {u r w nr k : ℕ}
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
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Sum (Fin u) (Fin r)) ℝ)
    (K : Matrix (Fin nr) (Fin nr) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (μ M : ℝ)
    (hWN : W * N = 0)
    (hBJ : (B₀ * N) * J = 1)
    (hWK : (W * W.transpose) * K = 1)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hB₀SR : ∀ i j, B₀ (Sum.inr i) j =
      srNominalMatrix wellRegion β₀ volume i j)
    (hα : ((β₀ / β) - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hB16Vertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveB16SymBlock wellRegion β β₀ volume (N * J) hV).mulVec v) i)
    (hTVertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveB16Action wellRegion β β₀ volume (N * J)
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
      measure well γ₁ R
    let a := β₀ / β
    let κ := ReservoirSeismicityControl.paperPhysicalDemandScale a μ M
    let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin a μ M
    W * (N * J) = 0 ∧
      W * (W.transpose * K) = 1 ∧
      δ < 1 ∧
      ∀ t : ℝ,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
              EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h a κ (N * J) t‖ ≤ δ := by
  have hbox := ReservoirSeismicityControl.paper_physical_well_sensitivity_box
    measure well γ₁ R γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRmin hγ hR hint
  exact positive_demand_B16_from_allocation
    B₀ W N J K wellRegion β β₀ volume
    (fun j => γmin * Rmin j) (fun _ => γmax * Rmax)
    (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities measure well γ₁ R)
    μ M hWN hBJ hWK hβ hβ₀ hvol hB₀SR hα hμ hM hμM
    hbox.1 hbox.2 hB16Vertices hTVertices

/-- Appendix B's bounded *actual* well input B(t), in the positive
SR-sign convention. This removes the standalone B(t) bound required by B19;
the constant is calculated from the fixed pressure block, the fixed SR
geometry and the A.2 upper bound on gamma_1 R. -/
theorem positive_demand_B19_well_operator_from_actual_sr_integrals
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
    let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
      measure well γ₁ R
    let H : ℝ := max 0 (γmax * Rmax)
    let LB : ℝ :=
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume
          (fun _ => 0) α 0) +
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * H
    ∀ t : ℝ,
      ‖positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ t‖ ≤ LB := by
  have hlegacy := ReservoirSeismicityControl.paper_physical_demand_wellCLM_bound_from_sr_integrals
    measure well γ₁ R γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRmin hγ hR hint
    Bᵤ₀ wellRegion (-β) volume α κ
  simpa only [positive_demand_wellCLM_eq_legacy_rebased,
    positive_demand_matrix_eq_legacy_rebased,
    positive_demand_rate_geometry_eq_legacy_rebased] using hlegacy

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B18_from_actual_sr_integrals
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B19_well_operator_from_actual_sr_integrals
