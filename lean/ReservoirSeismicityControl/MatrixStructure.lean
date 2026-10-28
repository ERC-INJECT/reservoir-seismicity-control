import Mathlib

/-!
# ReservoirSeismicityControl: finite-dimensional row-support structure

This module formalizes a structural step of Appendix A.4. Each well either
belongs to one output region or belongs to none. Consequently, distinct
pressure/SR observation rows have disjoint well supports, so the off-diagonal
entries of `B * B₀ᵀ` and `B₀ * B₀ᵀ` vanish.

This does NOT prove the Moore--Penrose pseudoinverse formula, the full
matrix-norm uncertainty estimate, or the PDE-dependent positivity bounds.
-/

namespace ReservoirSeismicityControl

/-- When each well is assigned to at most one observation region, the
    cross Gram entry between distinct actual/nominal rows is zero. -/
theorem cross_gram_offdiag_zero
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ i j, wellRegion j ≠ some i → B i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (i k : Fin m) (hik : i ≠ k) :
    (∑ j : Fin n, B i j * B₀ k j) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : wellRegion j = some i
  · have hjk : wellRegion j ≠ some k := by
      intro h
      have hsome : some i = some k := hji.symm.trans h
      exact hik (Option.some.inj hsome)
    rw [hB₀ k j hjk, mul_zero]
  · rw [hB i j hji, zero_mul]

/-- The nominal Gram matrix is diagonal under the same geometric
    support condition. This is the first step toward `B₀ B₀ᵀ` invertibility. -/
theorem nominal_gram_offdiag_zero
    {m n : ℕ}
    (B₀ : Fin m → Fin n → ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (i k : Fin m) (hik : i ≠ k) :
    (∑ j : Fin n, B₀ i j * B₀ k j) = 0 := by
  exact cross_gram_offdiag_zero B₀ B₀ wellRegion hB₀ hB₀ i k hik

/-- Pressure rows of the actual well matrix are a common scalar multiple
    of their nominal counterparts, as in equations (15)--(17). -/
theorem proportional_rows_cross_gram
    {m n : ℕ}
    (B B₀ : Fin m → Fin n → ℝ)
    (ρ : ℝ)
    (hrow : ∀ i j, B i j = ρ * B₀ i j)
    (i k : Fin m) :
    (∑ j : Fin n, B i j * B₀ k j) =
      ρ * (∑ j : Fin n, B₀ i j * B₀ k j) := by
  classical
  calc
    (∑ j : Fin n, B i j * B₀ k j) =
        ∑ j : Fin n, ρ * (B₀ i j * B₀ k j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrow i j]
          ring
    _ = ρ * (∑ j : Fin n, B₀ i j * B₀ k j) := by
          rw [Finset.mul_sum]

end ReservoirSeismicityControl
