import ReservoirSeismicityControl.DemandStrictContraction

/-!
# Appendix B: a matrix-indexed demand-contraction certificate

This file instantiates the already verified Stage 9 vector-energy inequality
with genuine matrices P and Q and their actions `P.mulVec u` and `Q.mulVec v`.
The full (non-diagonal) pressure-to-SR and SR-to-SR interactions are retained.

The coercivity and two squared-action bounds are hypotheses. Establishing
those from the physical well-support matrix, the demand null-space basis,
and the PDE-dependent sensitivity interval remains a separate task.

These proofs contain no `sorry`, `admit`, or custom axioms. Compilation and
`#print axioms` in the user's Lean environment are required for verification.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- Matrix-valued form of Appendix B's strict contraction. Here `α` is the
actual-to-nominal pressure gain `β₀ / β`, while `P` and `Q` are the unscaled
SR blocks `\widehat B_R C_u` and `\widehat B_R C_R`. -/
theorem demand_matrix_action_contraction
    {n r : ℕ}
    (P : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (u : Fin n → ℝ) (v : Fin r → ℝ)
    (α μ M : ℝ)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hcoercive :
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        ∑ i : Fin r, v i * (Q.mulVec v) i)
    (hfull :
      (∑ i : Fin r, ((P.mulVec u) i + (Q.mulVec v) i) ^ 2) ≤
        M ^ 2 * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)))
    (hpress :
      (∑ i : Fin r, ((P.mulVec u) i) ^ 2) ≤
        M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) :
    let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
    ρ < 1 ∧
      (∑ j : Fin n, (α * u j - u j) ^ 2) +
      (∑ i : Fin r,
        (κ * ((P.mulVec u) i + (Q.mulVec v) i) - v i) ^ 2) ≤
      ρ * ((∑ j : Fin n, (u j) ^ 2) +
        (∑ i : Fin r, (v i) ^ 2)) := by
  have hpressure :
      (∑ j : Fin n, (α * u j - u j) ^ 2) =
        (α - 1) ^ 2 * (∑ j : Fin n, (u j) ^ 2) := by
    calc
      (∑ j : Fin n, (α * u j - u j) ^ 2) =
          ∑ j : Fin n, ((α - 1) ^ 2 * (u j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (α - 1) ^ 2 * (∑ j : Fin n, (u j) ^ 2) := by
        rw [Finset.mul_sum]
  have hmain := demand_selected_scaling_energy_contraction
    u v (P.mulVec u) (Q.mulVec v) (α - 1) μ M
    hα hμ hM hμM hcoercive hfull hpress
  constructor
  · exact hmain.1
  · rw [hpressure]
    exact hmain.2

/-- Uniform matrix certificate: if the Appendix B block hypotheses hold
for every vector, one contraction factor works for the whole gain matrix.
This theorem is still abstract in the well sensitivities. -/
theorem demand_matrix_uniform_contraction
    {n r : ℕ}
    (P : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (α μ M : ℝ)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hcoercive : ∀ v : Fin r → ℝ,
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        ∑ i : Fin r, v i * (Q.mulVec v) i)
    (hfull : ∀ (u : Fin n → ℝ) (v : Fin r → ℝ),
      (∑ i : Fin r, ((P.mulVec u) i + (Q.mulVec v) i) ^ 2) ≤
        M ^ 2 * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)))
    (hpress : ∀ u : Fin n → ℝ,
      (∑ i : Fin r, ((P.mulVec u) i) ^ 2) ≤
        M ^ 2 * (∑ j : Fin n, (u j) ^ 2)) :
    let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
    ρ < 1 ∧
      ∀ (u : Fin n → ℝ) (v : Fin r → ℝ),
        (∑ j : Fin n, (α * u j - u j) ^ 2) +
        (∑ i : Fin r,
          (κ * ((P.mulVec u) i + (Q.mulVec v) i) - v i) ^ 2) ≤
        ρ * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)) := by
  let u₀ : Fin n → ℝ := fun _ => 0
  let v₀ : Fin r → ℝ := fun _ => 0
  have hzero := demand_matrix_action_contraction
    P Q u₀ v₀ α μ M hα hμ hM hμM
    (hcoercive v₀) (hfull u₀ v₀) (hpress u₀)
  constructor
  · exact hzero.1
  · intro u v
    exact (demand_matrix_action_contraction
      P Q u v α μ M hα hμ hM hμM
      (hcoercive v) (hfull u v) (hpress u)).2

end ReservoirSeismicityControl
