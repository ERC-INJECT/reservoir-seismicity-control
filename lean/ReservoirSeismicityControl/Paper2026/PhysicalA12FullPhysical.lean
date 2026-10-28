import ReservoirSeismicityControl.Paper2026.PhysicalA12FullNominal
import Mathlib.Tactic

/-!
# P4 / A.4: the complete physical pressure--SR gain is diagonal

This is the next paper-specific step after the locally verified full
nominal right inverse. Equation (15) gives the pressure coefficient
`1/(beta * volume)` and the *actual* signed-model SR coefficient as a
spatial mean of `gamma_1 R` divided by `normalization * beta * volume`.
The single well-to-output assignment is the Assumption 4 partition.

We prove that the actual physical matrix times the verified nominal
Gram right inverse has zero cross-output entries, including pressure/SR
couplings; its pressure diagonal is exactly beta0/beta. Neither result
assumes the desired gain contraction or adds a new geometric condition.

The arithmetic SR regional average (A11), full operator-norm bound (A12),
and gain derivative (A14) are subsequent obligations. The physical
strong SR regularity is not asserted here.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- The complete physical well-input matrix (15), expressed using the
same Assumption 4 assignment as the nominal matrix (17). The SR mean
is the actual Lebesgue well integral, not a free sensitivity vector. -/
noncomputable def paperA12FullPhysicalMatrix
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (t : ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  fun i j => if assignment j = some i then
    match i with
    | Sum.inl _ => 1 / (β * volume i)
    | Sum.inr _ =>
        paperPhysicalSRWellMean μ (well j) γ₁ R t /
          (normalization * β * volume i)
  else 0

/-- The pressure row of the *physical* matrix is the known constant
`beta0/beta` times its nominal row (15)--(17). -/
theorem paper_A12_full_physical_pressure_row
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) (t : ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvolume : ∀ i, volume i ≠ 0)
    (i : Fin u) (j : Fin w) :
    paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
        (Sum.inl i) j =
      (β₀ / β) *
        paperA12FullNominalMatrix assignment β₀ volume (Sum.inl i) j := by
  classical
  change (if assignment j = some (Sum.inl i) then
      (1 : ℝ) / (β * volume (Sum.inl i)) else 0) =
    (β₀ / β) * (if assignment j = some (Sum.inl i) then
      (1 : ℝ) / (β₀ * volume (Sum.inl i)) else 0)
  by_cases hj : assignment j = some (Sum.inl i)
  · simp only [if_pos hj]
    field_simp [hβ, hβ₀, hvolume (Sum.inl i)]
    <;> ring
  · simp only [if_neg hj, mul_zero]

/-- The product of the full physical matrix with the nominal Gram right
inverse has no off-diagonal entries, including pressure--SR cross terms.
This is the exact structural argument preceding (A11) in Appendix A.4. -/
theorem paper_A12_full_physical_off_diagonal_zero
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) (t : ℝ)
    (i k : Sum (Fin u) (Fin r)) (hik : i ≠ k) :
    (paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t *
        paperA12FullNominalRightInverse
          (paperA12FullNominalMatrix assignment β₀ volume)) i k = 0 := by
  classical
  change (∑ j : Fin w,
    paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t i j *
      (paperA12FullNominalMatrix assignment β₀ volume k j /
        paperA12FullGramDiag (paperA12FullNominalMatrix assignment β₀ volume) k)) = 0
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : assignment j = some i
  · have hjk : assignment j ≠ some k := by
      intro h
      exact hik (Option.some.inj (hji.symm.trans h))
    have hnom : paperA12FullNominalMatrix assignment β₀ volume k j = 0 := by
      simp [paperA12FullNominalMatrix, hjk]
    rw [hnom]
    simp
  · have hphys :
        paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t i j = 0 := by
      simp [paperA12FullPhysicalMatrix, hji]
    rw [hphys]
    simp

/-- At each pressure output, the full physical gain's diagonal entry
is exactly the pressure ratio from (A12). No contraction bound is assumed. -/
theorem paper_A12_full_physical_pressure_gain
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) (t : ℝ)
    (hβ : β ≠ 0) (hβ₀ : 0 < β₀)
    (hvolume : ∀ i, 0 < volume i)
    (hcovered : ∀ i : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some i)
    (i : Fin u) :
    (paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t *
        paperA12FullNominalRightInverse
          (paperA12FullNominalMatrix assignment β₀ volume))
        (Sum.inl i) (Sum.inl i) = β₀ / β := by
  classical
  let B₀ := paperA12FullNominalMatrix assignment β₀ volume
  have hright : B₀ * paperA12FullNominalRightInverse B₀ = 1 :=
    paper_A12_full_nominal_right_inverse_from_A4
      assignment β₀ volume hβ₀ hvolume hcovered
  have hdiag :
      (∑ j : Fin w, B₀ (Sum.inl i) j *
        (B₀ (Sum.inl i) j / paperA12FullGramDiag B₀ (Sum.inl i))) = 1 := by
    have h := congrArg
      (fun M : Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ =>
        M (Sum.inl i) (Sum.inl i)) hright
    simpa [Matrix.mul_apply, paperA12FullNominalRightInverse] using h
  change (∑ j : Fin w,
    paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
      (Sum.inl i) j *
      (B₀ (Sum.inl i) j / paperA12FullGramDiag B₀ (Sum.inl i))) = β₀ / β
  calc
    _ = (β₀ / β) *
        (∑ j : Fin w, B₀ (Sum.inl i) j *
          (B₀ (Sum.inl i) j / paperA12FullGramDiag B₀ (Sum.inl i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [paper_A12_full_physical_pressure_row μ well γ₁ R assignment
        β β₀ normalization volume t hβ (ne_of_gt hβ₀)
        (fun k => ne_of_gt (hvolume k)) i j]
      ring
    _ = β₀ / β := by rw [hdiag]; ring

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_row
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_off_diagonal_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_pressure_gain
