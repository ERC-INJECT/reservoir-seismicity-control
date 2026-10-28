import ReservoirSeismicityControl.MatrixStructure

/-!
# ReservoirSeismicityControl: row-structured nominal right inverse

For a nominal well matrix whose distinct observation rows have disjoint
supports, this module constructs an explicit right inverse using the
(nonzero) diagonal entries of its Gram matrix.

The statements are finite-dimensional. They do not yet establish the full
Moore--Penrose characterization or the norm inequalities of Theorems 1--2.
-/

namespace ReservoirSeismicityControl

/-- The diagonal entry of `B₀ B₀ᵀ` for a given output region. -/
def nominalGramDiag {m n : ℕ}
    (B₀ : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin n, B₀ i j * B₀ i j

/-- Explicit nominal right inverse when the Gram matrix is diagonal. -/
noncomputable def nominalRightInverse {m n : ℕ}
    (B₀ : Fin m → Fin n → ℝ) (j : Fin n) (i : Fin m) : ℝ :=
  B₀ i j / nominalGramDiag B₀ i

private theorem sum_product_div
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (i k : Fin m) (d : ℝ) :
    (∑ j : Fin n, B i j * (B₀ k j / d)) =
      (∑ j : Fin n, B i j * B₀ k j) / d := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The proposed inverse has `B₀ C = I`, provided each nominal
    Gram diagonal entry is nonzero. -/
theorem nominal_right_inverse_entry
    {m n : ℕ}
    (B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (hdiag : ∀ i, nominalGramDiag B₀ i ≠ 0)
    (i k : Fin m) :
    (∑ j : Fin n, B₀ i j * nominalRightInverse B₀ j k) =
      if i = k then 1 else 0 := by
  change (∑ j : Fin n, B₀ i j * (B₀ k j / nominalGramDiag B₀ k)) =
    if i = k then 1 else 0
  rw [sum_product_div]
  by_cases hik : i = k
  · subst k
    simp only [ite_true]
    change nominalGramDiag B₀ i / nominalGramDiag B₀ i = 1
    exact div_self (hdiag i)
  · rw [if_neg hik]
    have hzero := nominal_gram_offdiag_zero B₀ wellRegion hB₀ i k hik
    simp [hzero]

/-- Actual and nominal observation rows with different well supports
    have zero product after applying the nominal right inverse. -/
theorem actual_right_inverse_offdiag_zero
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ i j, wellRegion j ≠ some i → B i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (i k : Fin m) (hik : i ≠ k) :
    (∑ j : Fin n, B i j * nominalRightInverse B₀ j k) = 0 := by
  change (∑ j : Fin n, B i j * (B₀ k j / nominalGramDiag B₀ k)) = 0
  rw [sum_product_div]
  have hzero := cross_gram_offdiag_zero B B₀ wellRegion hB hB₀ i k hik
  simp [hzero]

/-- Proportional actual/nominal observation rows retain precisely
    that proportionality factor on the diagonal of `B C`. -/
theorem proportional_row_right_inverse_diagonal
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (hdiag : ∀ i, nominalGramDiag B₀ i ≠ 0)
    (i : Fin m) (ρ : ℝ)
    (hrow : ∀ j, B i j = ρ * B₀ i j) :
    (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) = ρ := by
  calc
    (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) =
        ∑ j : Fin n, ρ * (B₀ i j * nominalRightInverse B₀ j i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrow j]
          ring
    _ = ρ * (∑ j : Fin n, B₀ i j * nominalRightInverse B₀ j i) := by
          rw [Finset.mul_sum]
    _ = ρ := by
          rw [nominal_right_inverse_entry B₀ wellRegion hB₀ hdiag i i]
          simp

end ReservoirSeismicityControl
