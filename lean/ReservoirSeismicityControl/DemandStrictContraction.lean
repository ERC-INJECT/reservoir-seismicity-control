import ReservoirSeismicityControl.DemandContraction
import ReservoirSeismicityControl.Algebra

/-!
# Appendix B: selected scaling gives a strict demand-constrained contraction

Under the SR coercivity and operator bounds used in Appendix B, choosing
  κ = (1-ε²) μ / (2 M²)
gives a squared-vector contraction with an explicit factor ρ < 1.

The two vector blocks represent pressure and SR outputs. The SR actions
`p` and `q` are abstract vectors, satisfying the exact coercivity and
norm assumptions of the Stage 8 energy estimate. The construction of
those assumptions from the reservoir-dependent matrices is a separate
formalization task.

No `sorry` or custom axioms appear here. This module MUST be compiled
and audited locally before its results can be called machine-verified.
-/

namespace ReservoirSeismicityControl

/-- Under the Appendix B hypotheses and selected SR scaling, the squared
energy of the non-diagonal block error is bounded by `ρ` times the
squared input energy, for an explicit `ρ < 1`. The result is uniform in
both block dimensions and retains the pressure--SR cross term. -/
theorem demand_selected_scaling_energy_contraction
    {n r : ℕ} (u : Fin n → ℝ) (v p q : Fin r → ℝ)
    (ε μ M : ℝ)
    (hε : ε ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
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
    let κ : ℝ := (1 - ε ^ 2) * μ / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - ε ^ 2) / 4)
      (1 - (1 - ε ^ 4) * μ ^ 2 / (4 * M ^ 2))
    ρ < 1 ∧
      ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
        (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) ≤
      ρ * ((∑ j : Fin n, (u j) ^ 2) +
        (∑ i : Fin r, (v i) ^ 2)) := by
  let κ : ℝ := (1 - ε ^ 2) * μ / (2 * M ^ 2)
  let ρu : ℝ := 1 - (1 - ε ^ 2) / 4
  let ρR : ℝ := 1 - (1 - ε ^ 4) * μ ^ 2 / (4 * M ^ 2)
  let ρ : ℝ := max ρu ρR
  change ρ < 1 ∧
    ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
      (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) ≤
      ρ * ((∑ j : Fin n, (u j) ^ 2) +
        (∑ i : Fin r, (v i) ^ 2))

  have hκ : 0 ≤ κ := by
    dsimp [κ]
    apply div_nonneg
    · exact mul_nonneg (by linarith : 0 ≤ 1 - ε ^ 2) (le_of_lt hμ)
    · positivity
  have hεfour : 0 < 1 - ε ^ 4 := by
    have hh : 0 < (1 - ε ^ 2) * (1 + ε ^ 2) :=
      mul_pos (by linarith) (by positivity)
    nlinarith only [hh]
  have hρu : ρu < 1 := by
    dsimp [ρu]
    linarith
  have hρR : ρR < 1 := by
    have hh : 0 < (1 - ε ^ 4) * μ ^ 2 / (4 * M ^ 2) :=
      div_pos (mul_pos hεfour (sq_pos_of_pos hμ)) (by positivity)
    dsimp [ρR]
    linarith
  have hρ : ρ < 1 := max_lt hρu hρR
  have hcoefU :
      ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2 ≤ ρu := by
    exact constrained_pressure_coefficient_bound ε μ M hε hμ hM hμM
  have hcoefR :
      1 - κ * μ + κ ^ 2 * M ^ 2 = ρR := by
    exact constrained_sr_coefficient_identity ε μ M hM
  have hU : 0 ≤ (∑ j : Fin n, (u j) ^ 2) := by
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg _
  have hV : 0 ≤ (∑ i : Fin r, (v i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg _
  constructor
  · exact hρ
  · calc
      ε ^ 2 * (∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (κ * (p i + q i) - v i) ^ 2) ≤
          (ε ^ 2 + κ * M ^ 2 / μ + κ ^ 2 * M ^ 2) *
            (∑ j : Fin n, (u j) ^ 2) +
          (1 - κ * μ + κ ^ 2 * M ^ 2) *
            (∑ i : Fin r, (v i) ^ 2) :=
        demand_block_energy_bound u v p q ε κ μ M hμ hκ
          hcoercive hfull hpress
      _ ≤ ρu * (∑ j : Fin n, (u j) ^ 2) +
          ρR * (∑ i : Fin r, (v i) ^ 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hcoefU hU
        · rw [hcoefR]
      _ ≤ ρ * (∑ j : Fin n, (u j) ^ 2) +
          ρ * (∑ i : Fin r, (v i) ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left ρu ρR) hU)
          (mul_le_mul_of_nonneg_right (le_max_right ρu ρR) hV)
      _ = ρ * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)) := by ring

end ReservoirSeismicityControl
