import Mathlib

/-!
# Algebraic checks for the ReservoirSeismicityControl PDE--ODE controller

Corresponds to the uncertainty calculations in Appendices A.4 and B
of NLD_2026(9).tex.

STATUS: compiled successfully by the user with Lean 4.35.0-rc4 and Mathlib
(13 October 2026). Only the four theorems in this file are verified.

No `sorry` or custom `axiom` occurs in this module. The results below
are deliberately limited to scalar identities and strict positivity.
They do NOT formalize the PDE/ODE estimates, matrix norms, or external
MIMO super-twisting theorem.
-/


namespace ReservoirSeismicityControl

/-- The nominal compressibility interval implies strict scalar mismatch
    smaller than one, as used in Appendices A.4 and B. -/
theorem beta_mismatch_lt_one
    (β β₀ : ℝ) (hβ : 0 < β) (hβ₀ : 0 < β₀) (hub : β₀ < 2 * β) :
    |β₀ / β - 1| < 1 := by
  apply abs_lt.mpr
  constructor
  · have hp : 0 < β₀ / β := div_pos hβ₀ hβ
    linarith
  · have hp : β₀ / β < 2 := (div_lt_iff₀ hβ).2 (by linarith)
    linarith

/-- Exact expansion of the mixed pressure--SR square. This is the scalar
    counterpart of the cross term that must be retained in Appendix B. -/
theorem constrained_cross_term_identity
    (ε κ xᵤ xᵣ a b : ℝ) :
    (ε * xᵤ) ^ 2 + (κ * (a + b) - xᵣ) ^ 2 =
      ε ^ 2 * xᵤ ^ 2 + xᵣ ^ 2 + κ ^ 2 * (a + b) ^ 2
        - 2 * κ * xᵣ * a - 2 * κ * xᵣ * b := by
  ring

/-- A scalar Young inequality with the coefficient appearing in B. -/
theorem young_cross_term
    (μ r z : ℝ) (hμ : 0 < μ) :
    2 * r * z ≤ μ * r ^ 2 + z ^ 2 / μ := by
  have hp : 0 ≤ (μ * r - z) ^ 2 / μ :=
    div_nonneg (sq_nonneg _) (le_of_lt hμ)
  have heq : μ * r ^ 2 + z ^ 2 / μ =
      2 * r * z + (μ * r - z) ^ 2 / μ := by
    field_simp; ring
  rw [heq]
  linarith

/-- Both squared contraction margins in (B20) are strictly smaller
    than one when the compressibility mismatch and SR authority obey
    their stated ranges. Here rho corresponds to μ/M. -/
theorem constrained_margin_lt_one
    (ε ρ : ℝ) (hε : ε ^ 2 < 1) (hρ : 0 < ρ) :
    1 - (1 - ε ^ 2) / 4 < 1 ∧
      1 - ((1 - ε ^ 4) * ρ ^ 2) / 4 < 1 := by
  have hfirst : 0 < 1 - ε ^ 2 := by linarith
  have hproduct : 0 < (1 - ε ^ 2) * (1 + ε ^ 2) :=
    mul_pos hfirst (by positivity)
  have heq : (1 - ε ^ 2) * (1 + ε ^ 2) = 1 - ε ^ 4 := by
    ring
  rw [heq] at hproduct
  have hrho : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hh : 0 < (1 - ε ^ 4) * ρ ^ 2 := mul_pos hproduct hrho
  constructor <;> linarith

/-- The SR coefficient in (B20) is an exact algebraic identity for the
    selected scaling κ = (1-ε²) μ/(2M²). -/
theorem constrained_sr_coefficient_identity
    (ε μ M : ℝ) (hM : 0 < M) :
    let κ : ℝ := (1 - ε ^ 2) * μ / (2 * M ^ 2)
    1 - κ * μ + κ ^ 2 * M ^ 2 =
      1 - (1 - ε ^ 4) * μ ^ 2 / (4 * M ^ 2) := by
  dsimp
  field_simp [ne_of_gt hM]
  ring

/-- The pressure coefficient in (B20) is at most
    `1 - (1-ε²)/4`, provided `0 < μ ≤ M` and `ε² < 1`.
    This verifies the scalar bound, not the matrix Young inequality. -/
theorem constrained_pressure_coefficient_bound
    (ε μ M : ℝ) (hε : ε ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M) :
    let κ : ℝ := (1 - ε ^ 2) * μ / (2 * M ^ 2)
    ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2 ≤
      1 - (1 - ε ^ 2) / 4 := by
  let κ : ℝ := (1 - ε ^ 2) * μ / (2 * M ^ 2)
  have hμsq : μ ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ M - μ)
      (by linarith : 0 ≤ M + μ)]
  have hεsq : (1 - ε ^ 2) ^ 2 ≤ 1 - ε ^ 2 := by
    have hεnonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ε ^ 2) hεnonneg]
  have hkey : (1 - ε ^ 2) ^ 2 * μ ^ 2 ≤
      (1 - ε ^ 2) * M ^ 2 :=
    (mul_le_mul_of_nonneg_left hμsq (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hεsq (sq_nonneg _))
  have hfrac : (1 - ε ^ 2) ^ 2 * μ ^ 2 / (4 * M ^ 2) ≤
      (1 - ε ^ 2) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * M ^ 2)).2
    have hfour : (1 - ε ^ 2) / 4 * (4 * M ^ 2) =
        (1 - ε ^ 2) * M ^ 2 := by ring
    rw [hfour]
    exact hkey
  have heq : ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2 =
      (1 + ε ^ 2) / 2 +
        (1 - ε ^ 2) ^ 2 * μ ^ 2 / (4 * M ^ 2) := by
    dsimp [κ]
    field_simp [ne_of_gt hμ, ne_of_gt hM]
    ring
  dsimp only
  rw [heq]
  linarith

end ReservoirSeismicityControl
