import ReservoirSeismicityControl.MatrixContraction
import ReservoirSeismicityControl.Algebra

/-!
# Appendix B: non-diagonal demand-constrained contraction

The vector indices below represent the pressure block (`u`) and the SR
block (`v`) of a demand-constrained error. The vectors `p` and `q`
represent `\widehat B_R C_u u` and `\widehat B_R C_R v` respectively.

Unlike the unconstrained gain, the SR block can contain off-diagonal
entries. The new lemmas retain the full cross term and assume precisely
its two required operator properties: a positive symmetric SR part and
an operator-norm bound for the full SR row.

NOT YET COMPILED. This file contains no `sorry`, but mathematical
verification requires successful compilation and an axiom audit.
-/

namespace ReservoirSeismicityControl

/-- Young's inequality summed over the SR output coordinates. -/
theorem finite_vector_young
    {r : ℕ} (v p : Fin r → ℝ) (μ : ℝ) (hμ : 0 < μ) :
    (∑ i : Fin r, -2 * v i * p i) ≤
      μ * (∑ i : Fin r, (v i) ^ 2) +
      (∑ i : Fin r, (p i) ^ 2) / μ := by
  classical
  have hsum :
      (∑ i : Fin r, -2 * v i * p i) ≤
        ∑ i : Fin r, (μ * (v i) ^ 2 + (p i) ^ 2 / μ) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      -2 * v i * p i = 2 * v i * (-(p i)) := by ring
      _ ≤ μ * (v i) ^ 2 + (-(p i)) ^ 2 / μ :=
        young_cross_term μ (v i) (-(p i)) hμ
      _ = μ * (v i) ^ 2 + (p i) ^ 2 / μ := by ring
  calc
    (∑ i : Fin r, -2 * v i * p i) ≤
        ∑ i : Fin r, (μ * (v i) ^ 2 + (p i) ^ 2 / μ) := hsum
    _ = μ * (∑ i : Fin r, (v i) ^ 2) +
          (∑ i : Fin r, (p i) ^ 2) / μ := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.sum_div]

/-- Under `‖p‖² ≤ M²‖u‖²`, control the mixed pressure--SR term.
The scalar `μ` is the positive SR coercivity margin. -/
theorem demand_cross_term_bound
    {n r : ℕ} (u : Fin n → ℝ) (v p : Fin r → ℝ)
    (μ M : ℝ) (hμ : 0 < μ)
    (hp : (∑ i : Fin r, (p i) ^ 2) ≤
       M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) :
    (∑ i : Fin r, -2 * v i * p i) ≤
      μ * (∑ i : Fin r, (v i) ^ 2) +
      (M ^ 2 / μ) * (∑ j : Fin n, (u j) ^ 2) := by
  have hdiv :
      (∑ i : Fin r, (p i) ^ 2) / μ ≤
        (M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) / μ :=
    (div_le_div_iff_of_pos_right hμ).2 hp
  calc
    (∑ i : Fin r, -2 * v i * p i) ≤
        μ * (∑ i : Fin r, (v i) ^ 2) +
          (∑ i : Fin r, (p i) ^ 2) / μ :=
      finite_vector_young v p μ hμ
    _ ≤ μ * (∑ i : Fin r, (v i) ^ 2) +
          (M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) / μ := by
      exact add_le_add_right hdiv _
    _ = μ * (∑ i : Fin r, (v i) ^ 2) +
          (M ^ 2 / μ) * (∑ j : Fin n, (u j) ^ 2) := by ring

/-- Exact block-norm expansion with the SR cross term retained. -/
theorem demand_block_energy_identity
    {n r : ℕ} (u : Fin n → ℝ) (v p q : Fin r → ℝ)
    (ε κ : ℝ) :
    ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
      (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) =
    ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
      (∑ i : Fin r, (v i) ^ 2) +
      κ ^ 2 * (∑ i : Fin r, (p i + q i) ^ 2) -
      2 * κ * (∑ i : Fin r, v i * q i) -
      2 * κ * (∑ i : Fin r, v i * p i) := by
  classical
  have h :
      (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) =
        ∑ i : Fin r,
          ((v i) ^ 2 + κ ^ 2 * (p i + q i) ^ 2 -
            2 * κ * (v i * q i) - 2 * κ * (v i * p i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

/-- The general (possibly non-diagonal) block energy estimate in Appendix B.
The three analytic matrix assumptions are SR coercivity, bounded full
SR action, and bounded pressure-to-SR action. They must eventually be
obtained from the physical demand allocation. -/
theorem demand_block_energy_bound
    {n r : ℕ} (u : Fin n → ℝ) (v p q : Fin r → ℝ)
    (ε κ μ M : ℝ) (hμ : 0 < μ) (hκ : 0 ≤ κ)
    (hcoercive :
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        (∑ i : Fin r, v i * q i))
    (hfull :
      (∑ i : Fin r, (p i + q i) ^ 2) ≤
        M ^ 2 * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)))
    (hpress :
      (∑ i : Fin r, (p i) ^ 2) ≤
        M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) :
    ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
      (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) ≤
    (ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2) *
      (∑ j : Fin n, (u j) ^ 2) +
    (1 - κ * μ + κ ^ 2 * M ^ 2) *
      (∑ i : Fin r, (v i) ^ 2) := by
  let U : ℝ := ∑ j : Fin n, (u j) ^ 2
  let V : ℝ := ∑ i : Fin r, (v i) ^ 2
  let F : ℝ := ∑ i : Fin r, (p i + q i) ^ 2
  let Dp : ℝ := ∑ i : Fin r, v i * p i
  let Dq : ℝ := ∑ i : Fin r, v i * q i
  have hy :
      (∑ i : Fin r, -2 * v i * p i) ≤
        μ * V + (M ^ 2 / μ) * U :=
    demand_cross_term_bound u v p μ M hμ hpress
  have hy' : -2 * Dp ≤ μ * V + (M ^ 2 / μ) * U := by
    calc
      -2 * Dp = (∑ i : Fin r, -2 * v i * p i) := by
        dsimp [Dp]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := hy
  have hfull' : F ≤ M ^ 2 * (U + V) := hfull
  have hcoercive' : μ * V ≤ Dq := hcoercive
  have h1 : κ ^ 2 * F ≤ κ ^ 2 * (M ^ 2 * (U + V)) :=
    mul_le_mul_of_nonneg_left hfull' (sq_nonneg κ)
  have h2 : -2 * κ * Dq ≤ -2 * κ * (μ * V) := by
    have hc := mul_le_mul_of_nonneg_left hcoercive' hκ
    linarith
  have h3 : -2 * κ * Dp ≤ κ * (μ * V + (M ^ 2 / μ) * U) := by
    have hp := mul_le_mul_of_nonneg_left hy' hκ
    calc
      -2 * κ * Dp = κ * (-2 * Dp) := by ring
      _ ≤ κ * (μ * V + (M ^ 2 / μ) * U) := hp
  have hE :
      ε ^ 2 * U + (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) =
        ε ^ 2 * U + V + κ ^ 2 * F - 2 * κ * Dq - 2 * κ * Dp := by
    exact demand_block_energy_identity u v p q ε κ
  change ε ^ 2 * U + (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) ≤
    (ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2) * U +
      (1 - κ * μ + κ ^ 2 * M ^ 2) * V
  calc
    ε ^ 2 * U + (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) =
        ε ^ 2 * U + V + κ ^ 2 * F - 2 * κ * Dq - 2 * κ * Dp := hE
    _ ≤ ε ^ 2 * U + V + κ ^ 2 * (M ^ 2 * (U + V)) -
          2 * κ * Dq - 2 * κ * Dp := by
      linarith only [h1]
    _ ≤ ε ^ 2 * U + V + κ ^ 2 * (M ^ 2 * (U + V)) -
          2 * κ * (μ * V) - 2 * κ * Dp := by
      linarith only [h2]
    _ ≤ ε ^ 2 * U + V + κ ^ 2 * (M ^ 2 * (U + V)) -
          2 * κ * (μ * V) + κ * (μ * V + (M ^ 2 / μ) * U) := by
      linarith only [h3]
    _ = (ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2) * U +
          (1 - κ * μ + κ ^ 2 * M ^ 2) * V := by ring

end ReservoirSeismicityControl
