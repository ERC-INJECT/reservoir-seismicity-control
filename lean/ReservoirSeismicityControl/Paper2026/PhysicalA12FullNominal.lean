import ReservoirSeismicityControl.Paper2026.PhysicalA12Geometry
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: full nominal pressure--SR Gram and right inverse

In (17), the pressure and SR rows have the same nominal supported-well
coefficient, with their own output-region volumes. Assumption 4 assigns
wells to disjoint output regions and gives every output region at least one
well. We use one well-assignment map for BOTH output types, so disjointness
is structural rather than imposed as a new analytic hypothesis.

This proves the strictly positive full Gram diagonal, the vanishing
cross-row Gram terms, and the exact right-inverse identity
`B₀ C₀ = I` for the matrix in (17). The usual identification of this
Gram right inverse with the Moore--Penrose pseudoinverse is standard
finite-dimensional linear algebra and is NOT reproved here.

The physical G = B C₀, its A12 operator norm, and A14 rate are not
claimed by this module. Spatial PDE estimates remain separate.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- Both types of observation rows of (17), with their respective positive
volumes. `assignment j = some i` states that the well support is in output
region `i`; `none` covers wells in no output region. -/
noncomputable def paperA12FullNominalMatrix {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  fun i j => if assignment j = some i then 1 / (β₀ * volume i) else 0

/-- Diagonal entry of the full nominal matrix Gram, including pressure
and SR output rows. -/
noncomputable def paperA12FullGramDiag {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (i : Sum (Fin u) (Fin r)) : ℝ :=
  ∑ j : Fin w, B₀ i j * B₀ i j

/-- Assumption 4 makes every diagonal entry of `B₀ B₀ᵀ` strictly
positive, now including pressure as well as SR output regions. -/
theorem paper_A12_full_nominal_gram_pos
    {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (hβ₀ : 0 < β₀) (hvolume : ∀ i, 0 < volume i)
    (hcovered : ∀ i : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some i)
    (i : Sum (Fin u) (Fin r)) :
    0 < paperA12FullGramDiag
      (paperA12FullNominalMatrix assignment β₀ volume) i := by
  classical
  obtain ⟨j, hj⟩ := hcovered i
  have hentry :
      0 < paperA12FullNominalMatrix assignment β₀ volume i j := by
    simp only [paperA12FullNominalMatrix, if_pos hj]
    exact div_pos (by norm_num : (0 : ℝ) < 1)
      (mul_pos hβ₀ (hvolume i))
  have hsingle :
      paperA12FullNominalMatrix assignment β₀ volume i j *
        paperA12FullNominalMatrix assignment β₀ volume i j ≤
      paperA12FullGramDiag
        (paperA12FullNominalMatrix assignment β₀ volume) i := by
    change paperA12FullNominalMatrix assignment β₀ volume i j *
        paperA12FullNominalMatrix assignment β₀ volume i j ≤
      ∑ k : Fin w, paperA12FullNominalMatrix assignment β₀ volume i k *
        paperA12FullNominalMatrix assignment β₀ volume i k
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin w)))
      (f := fun k : Fin w =>
        paperA12FullNominalMatrix assignment β₀ volume i k *
        paperA12FullNominalMatrix assignment β₀ volume i k)
      (by intro k hk; exact mul_self_nonneg _)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos hentry hentry) hsingle

/-- Different full-output rows have disjoint nominal well support,
including every pressure/SR cross pair. This is automatic from the
single region-assignment map of Assumption 4. -/
theorem paper_A12_full_nominal_cross_gram_zero
    {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (i k : Sum (Fin u) (Fin r)) (hik : i ≠ k) :
    (∑ j : Fin w,
      paperA12FullNominalMatrix assignment β₀ volume i j *
        paperA12FullNominalMatrix assignment β₀ volume k j) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : assignment j = some i
  · have hjk : assignment j ≠ some k := by
      intro h
      exact hik (Option.some.inj (hji.symm.trans h))
    change
      (if assignment j = some i then (1 : ℝ) / (β₀ * volume i) else 0) *
        (if assignment j = some k then (1 : ℝ) / (β₀ * volume k) else 0) = 0
    simp only [if_pos hji, if_neg hjk, mul_zero]
  · simp [paperA12FullNominalMatrix, hji]

/-- The canonical Gram right inverse, for the actual full nominal
matrix of equation (17). -/
noncomputable def paperA12FullNominalRightInverse {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ) :
    Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ :=
  fun j i => B₀ i j / paperA12FullGramDiag B₀ i

/-- Full-output A4 rank certificate: no free `B₀ C₀ = I` hypothesis.
This establishes the right-inverse expression used before (A11).
It does not claim the full physical A12 mismatch or A14 derivative. -/
theorem paper_A12_full_nominal_right_inverse_from_A4
    {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (hβ₀ : 0 < β₀) (hvolume : ∀ i, 0 < volume i)
    (hcovered : ∀ i : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some i) :
    let B₀ := paperA12FullNominalMatrix assignment β₀ volume
    B₀ * paperA12FullNominalRightInverse B₀ = 1 := by
  classical
  dsimp only
  let B₀ := paperA12FullNominalMatrix assignment β₀ volume
  have hfactor (i k : Sum (Fin u) (Fin r)) :
      (∑ j : Fin w, B₀ i j *
        (B₀ k j / paperA12FullGramDiag B₀ k)) =
      (∑ j : Fin w, B₀ i j * B₀ k j) /
        paperA12FullGramDiag B₀ k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  ext i k
  change (∑ j : Fin w, B₀ i j *
    (B₀ k j / paperA12FullGramDiag B₀ k)) =
      if i = k then (1 : ℝ) else 0
  rw [hfactor i k]
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl]
    change paperA12FullGramDiag B₀ i /
      paperA12FullGramDiag B₀ i = 1
    exact div_self (ne_of_gt
      (paper_A12_full_nominal_gram_pos
        assignment β₀ volume hβ₀ hvolume hcovered i))
  · rw [if_neg hik]
    rw [paper_A12_full_nominal_cross_gram_zero
      assignment β₀ volume i k hik, zero_div]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_gram_pos
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_cross_gram_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_nominal_right_inverse_from_A4
