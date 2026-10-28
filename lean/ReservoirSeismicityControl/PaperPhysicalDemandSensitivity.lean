import ReservoirSeismicityControl.PaperDemandBlockGainBridge
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Stage 45: Appendix B's actual well-sensitivity matrix

The SR coefficient with its common positive factor κ_R removed is
  Bhat_R(h)ᵢⱼ = -hⱼ / (β |V_{R_i}|)
when well j belongs to SR region i, and zero otherwise.

This module models that coefficient using the well-region map and the
physical regional volume. It proves the support identity, the affine
dependence on h, and identifies the complete constrained gain B(h) C_W
with the non-diagonal block matrix formalized in Stage 44.

Assumption A6's nominal identity B₀ C_W = I is supplied as two explicit
pressure-row identities. The vertex coercivity certificate is *not*
proved in this module. It is the next remaining algebraic step.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- The physical unscaled SR sensitivity matrix of Appendix B. The minus
sign and the regional-volume denominator are retained explicitly. -/
noncomputable def paperPhysicalSRWellMatrix {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then
    (-1 / (β * volume i)) * h j else 0

/-- A well outside an SR region has no sensitivity in that region. -/
theorem paper_physical_sr_well_off_region
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (i : Fin r) (j : Fin w)
    (hj : wellRegion j ≠ some i) :
    paperPhysicalSRWellMatrix wellRegion β volume h i j = 0 := by
  simp [paperPhysicalSRWellMatrix, hj]

/-- A well belonging to a region has exactly the unscaled coefficient
in equation (B.4), including its physical negative sign. -/
theorem paper_physical_sr_well_in_region
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (i : Fin r) (j : Fin w)
    (hj : wellRegion j = some i) :
    paperPhysicalSRWellMatrix wellRegion β volume h i j =
      (-1 / (β * volume i)) * h j := by
  simp [paperPhysicalSRWellMatrix, hj]

/-- Physical SR sensitivity is affine (indeed linear) in the well averages h.
This is the algebraic reason the vertex checks in Appendix B are valid. -/
theorem paper_physical_sr_well_affine
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h₀ h₁ : Fin w → ℝ) (θ : ℝ) :
    paperPhysicalSRWellMatrix wellRegion β volume
        (fun j => θ * h₀ j + (1 - θ) * h₁ j) =
      θ • paperPhysicalSRWellMatrix wellRegion β volume h₀ +
        (1 - θ) • paperPhysicalSRWellMatrix wellRegion β volume h₁ := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp [paperPhysicalSRWellMatrix, hj, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · simp [paperPhysicalSRWellMatrix, hj, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]

/-- The actual pressure/SR well matrix before multiplying by the
nominal demand allocation C_W. -/
noncomputable def paperPhysicalDemandWellMatrix {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (α κ : ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  fun i j => match i with
    | Sum.inl a => α * Bᵤ₀ a j
    | Sum.inr a => κ * paperPhysicalSRWellMatrix
        wellRegion β volume h a j

/-- The physical pressure-to-SR and SR-to-SR blocks after the well
allocator C_W is applied. Both are generally non-diagonal. -/
noncomputable def paperPhysicalSRPressureBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    Matrix (Fin r) (Fin u) ℝ :=
  fun i j => ∑ k : Fin w,
    paperPhysicalSRWellMatrix wellRegion β volume h i k * C k (Sum.inl j)

noncomputable def paperPhysicalSRSRBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => ∑ k : Fin w,
    paperPhysicalSRWellMatrix wellRegion β volume h i k * C k (Sum.inr j)

/-- The well-level gain B(h) C_W is exactly the Appendix B block matrix.
The pressure identities are the pressure rows of B₀ C_W = I, derived
in the paper from the A6 full-rank assumption. -/
theorem paper_physical_demand_gain_eq_block
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (α κ : ℝ)
    (hpressureId : ∀ i j : Fin u,
      (∑ k : Fin w, Bᵤ₀ i k * C k (Sum.inl j)) =
        if i = j then 1 else 0)
    (hpressureZero : ∀ (i : Fin u) (j : Fin r),
      (∑ k : Fin w, Bᵤ₀ i k * C k (Sum.inr j)) = 0) :
    paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ * C =
      paperDemandBlockGainMatrix α κ
        (paperPhysicalSRPressureBlock wellRegion β volume h C)
        (paperPhysicalSRSRBlock wellRegion β volume h C) := by
  classical
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (∑ k : Fin w, (α * Bᵤ₀ i k) * C k (Sum.inl j)) =
        (if i = j then α else 0)
      calc
        _ = α * (∑ k : Fin w, Bᵤ₀ i k * C k (Sum.inl j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = α * (if i = j then (1 : ℝ) else 0) := by
          rw [hpressureId i j]
        _ = (if i = j then α else 0) := by
          split_ifs <;> ring
    | inr j =>
      change (∑ k : Fin w, (α * Bᵤ₀ i k) * C k (Sum.inr j)) = 0
      calc
        _ = α * (∑ k : Fin w, Bᵤ₀ i k * C k (Sum.inr j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = α * 0 := by rw [hpressureZero i j]
        _ = 0 := by ring
  | inr i =>
    cases j with
    | inl j =>
      change (∑ k : Fin w,
          (κ * paperPhysicalSRWellMatrix wellRegion β volume h i k) *
            C k (Sum.inl j)) =
        κ * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h i k *
            C k (Sum.inl j))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    | inr j =>
      change (∑ k : Fin w,
          (κ * paperPhysicalSRWellMatrix wellRegion β volume h i k) *
            C k (Sum.inr j)) =
        κ * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h i k *
            C k (Sum.inr j))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end ReservoirSeismicityControl
