import ReservoirSeismicityControl.MatrixRightInverse

open scoped Matrix

/-!
# ReservoirSeismicityControl: induced Euclidean contraction for disjoint-support well matrices

This module establishes the vector norm inequality for G = B C, where
C is the explicitly constructed nominal right inverse, and the rows of
B and B₀ have disjoint well supports.

If each diagonal gain gᵢ lies in a *uniform* interval 0 < gmin ≤ gᵢ ≤
gmax < 2, then there exists an explicit δ < 1 such that

  ∑ᵢ |(G - I)x|ᵢ² ≤ δ² ∑ᵢ |xᵢ|².

This is the squared Euclidean version of ‖G - I‖₂ ≤ δ, assuming the
usual operator norm is induced by the Euclidean vector norm.

The lemma abstracts the uniform gain interval. Proving that the physical
PDE--ODE sensitivities satisfy this interval, proving the Moore--Penrose
characterization of C, and proving the constrained matrix inequality in
Appendix B are separate tasks.
-/

namespace ReservoirSeismicityControl

/-- The explicit nominal inverse is a right inverse, as a rectangular
matrix identity rather than just entrywise equations. -/
theorem nominal_right_inverse_matrix
    {m n : ℕ}
    (B₀ : Matrix (Fin m) (Fin n) ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (hdiag : ∀ i, nominalGramDiag B₀ i ≠ 0) :
    B₀ * Matrix.of (fun j i => nominalRightInverse B₀ j i) = 1 := by
  classical
  ext i k
  change (∑ j : Fin n, B₀ i j * nominalRightInverse B₀ j k) =
    if i = k then 1 else 0
  exact nominal_right_inverse_entry B₀ wellRegion hB₀ hdiag i k

/-- Multiplying an actual well matrix by the explicit nominal right
inverse gives a diagonal action on every output vector. -/
theorem actual_gain_action
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ i j, wellRegion j ≠ some i → B i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (x : Fin m → ℝ) (i : Fin m) :
    (∑ k : Fin m,
        (∑ j : Fin n, B i j * nominalRightInverse B₀ j k) * x k) =
      (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) * x i := by
  classical
  calc
    (∑ k : Fin m,
        (∑ j : Fin n, B i j * nominalRightInverse B₀ j k) * x k) =
      ∑ k : Fin m,
        (if k = i then
          (∑ j : Fin n, B i j * nominalRightInverse B₀ j i)
        else 0) * x k := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hki : k = i
          · subst k
            simp
          · have hik : i ≠ k := Ne.symm hki
            have hzero := actual_right_inverse_offdiag_zero
              B B₀ wellRegion hB hB₀ i k hik
            simp [hki, hzero]
    _ = (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) * x i := by
      simp

/-- Every entry of an interval between `lo` and `hi` lies within the
largest endpoint distance from one. -/
theorem interval_gain_error_bound
    (lo hi g : ℝ) (hlo : lo ≤ g) (hhi : g ≤ hi) :
    |g - 1| ≤ max |lo - 1| |hi - 1| := by
  apply abs_le.mpr
  constructor
  · have hA : |lo - 1| ≤ max |lo - 1| |hi - 1| :=
      le_max_left _ _
    have hneg := (abs_le.mp hA).1
    linarith
  · have hB : |hi - 1| ≤ max |lo - 1| |hi - 1| :=
      le_max_right _ _
    have hpos := (abs_le.mp hB).2
    linarith

/-- A strictly positive uniform gain interval strictly below two gives
an explicit contractive margin independent of the output dimension. -/
theorem interval_gain_margin_lt_one
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi < 2) :
    0 ≤ max |lo - 1| |hi - 1| ∧
      max |lo - 1| |hi - 1| < 1 := by
  have h0 : 0 ≤ max |lo - 1| |hi - 1| :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hlo2 : lo < 2 := lt_of_le_of_lt hle hhi
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo hle
  have hloabs : |lo - 1| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hhiabs : |hi - 1| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  exact ⟨h0, max_lt hloabs hhiabs⟩

/-- Squared Euclidean contraction for a diagonal gain. -/
theorem diagonal_gain_energy_contraction
    {m : ℕ} (g x : Fin m → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hg : ∀ i, |g i - 1| ≤ δ) :
    (∑ i : Fin m, ((g i - 1) * x i) ^ 2) ≤
      δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := by
  classical
  have hterm (i : Fin m) :
      ((g i - 1) * x i) ^ 2 ≤ δ ^ 2 * (x i) ^ 2 := by
    have hpair := abs_le.mp (hg i)
    have hl : 0 ≤ δ - (g i - 1) := by linarith [hpair.2]
    have hr : 0 ≤ δ + (g i - 1) := by linarith [hpair.1]
    have hsq : (g i - 1) ^ 2 ≤ δ ^ 2 := by
      nlinarith [mul_nonneg hl hr]
    calc
      ((g i - 1) * x i) ^ 2 = (g i - 1) ^ 2 * (x i) ^ 2 := by ring
      _ ≤ δ ^ 2 * (x i) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  calc
    (∑ i : Fin m, ((g i - 1) * x i) ^ 2) ≤
        ∑ i : Fin m, δ ^ 2 * (x i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact hterm i
    _ = δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := by
      rw [Finset.mul_sum]

/-- The actual gain `B C` is uniformly contractive whenever its
(nonzero) diagonal entries lie between `lo` and `hi`.

This is the matrix norm estimate for the disjoint-support, unconstrained
controller, expressed directly in Euclidean vector norm squares. -/
theorem actual_gain_energy_contraction
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ i j, wellRegion j ≠ some i → B i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi < 2)
    (hgain : ∀ i,
      lo ≤ (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) ∧
      (∑ j : Fin n, B i j * nominalRightInverse B₀ j i) ≤ hi)
    (x : Fin m → ℝ) :
    let δ : ℝ := max |lo - 1| |hi - 1|
    (∑ i : Fin m,
      ((∑ k : Fin m,
        (∑ j : Fin n, B i j * nominalRightInverse B₀ j k) * x k) - x i) ^ 2) ≤
        δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) ∧ δ < 1 := by
  dsimp only
  have hmargin := interval_gain_margin_lt_one lo hi hlo hle hhi
  let g : Fin m → ℝ := fun i =>
    ∑ j : Fin n, B i j * nominalRightInverse B₀ j i
  have hg : ∀ i, |g i - 1| ≤ max |lo - 1| |hi - 1| := by
    intro i
    exact interval_gain_error_bound lo hi (g i) (hgain i).1 (hgain i).2
  constructor
  · calc
      (∑ i : Fin m,
        ((∑ k : Fin m,
          (∑ j : Fin n, B i j * nominalRightInverse B₀ j k) * x k) - x i) ^ 2) =
        ∑ i : Fin m, ((g i - 1) * x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [actual_gain_action B B₀ wellRegion hB hB₀ x i]
          dsimp [g]
          ring
      _ ≤ (max |lo - 1| |hi - 1|) ^ 2 *
          (∑ i : Fin m, (x i) ^ 2) :=
        diagonal_gain_energy_contraction g x _ hmargin.1 hg
  · exact hmargin.2

end ReservoirSeismicityControl
