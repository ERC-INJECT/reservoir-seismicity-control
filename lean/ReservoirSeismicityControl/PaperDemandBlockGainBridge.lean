import ReservoirSeismicityControl.PaperMatrixGainBridge
import ReservoirSeismicityControl.DemandMatrixAction
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Stage 44: non-diagonal demand gain, from Appendix B to operator contraction

Stage 10 supplies a **uniform squared-action inequality** for the pressure
and seismicity blocks. Stage 43 converts such inequalities into bounds on
Euclidean matrix operators, and Stage 42 obtains their inverses. This file
connects the three using a single `Sum (Fin n) (Fin r)` output index.

`P` and `Q` here are the unscaled SR blocks of Appendix B. In particular,
`P` is **not** assumed to vanish. The physical well-sensitivity bounds and
the identification of `P`, `Q` with the well operators remain the same
explicit hypotheses as in Stage 10. Neither Qdot nor a diagonal SR matrix
is assumed.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- Appendix B gain, with pressure and seismicity output indices in a
single finite-dimensional Euclidean vector. The off-diagonal block `P`
is retained exactly. -/
def paperDemandBlockGainMatrix {n r : ℕ}
    (α κ : ℝ)
    (P : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl a, Sum.inl b => if a = b then α else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr a, Sum.inl b => κ * P a b
    | Sum.inr a, Sum.inr b => κ * Q a b

/-- The upper gain block is exactly `α I`, including its zero cross-block. -/
theorem paper_demand_block_pressure_action
    {n r : ℕ} (α κ : ℝ)
    (P : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (x : Sum (Fin n) (Fin r) → ℝ) (i : Fin n) :
    ((paperDemandBlockGainMatrix α κ P Q).mulVec x) (Sum.inl i) =
      α * x (Sum.inl i) := by
  classical
  simp [paperDemandBlockGainMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

/-- The lower gain block is `κ (P u + Q v)` with the full, non-diagonal
pressure-to-SR and SR-to-SR couplings. -/
theorem paper_demand_block_seismicity_action
    {n r : ℕ} (α κ : ℝ)
    (P : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (x : Sum (Fin n) (Fin r) → ℝ) (i : Fin r) :
    ((paperDemandBlockGainMatrix α κ P Q).mulVec x) (Sum.inr i) =
      κ * ((P.mulVec (fun j => x (Sum.inl j))) i +
           (Q.mulVec (fun j => x (Sum.inr j))) i) := by
  classical
  simp [paperDemandBlockGainMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Finset.mul_sum, mul_add, mul_assoc]

/-- The genuine block-matrix version of Stage 10's squared contraction.
There is no additional block-action hypothesis: the two action identities
above prove that the block matrix realizes the paper's decomposition. -/
theorem paper_demand_block_squared_action_certificate
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
    ρ < 1 ∧ ∀ x : Sum (Fin n) (Fin r) → ℝ,
      (∑ i : Sum (Fin n) (Fin r),
          (((paperDemandBlockGainMatrix α κ P Q).mulVec x) i - x i) ^ 2) ≤
      ρ * (∑ i : Sum (Fin n) (Fin r), (x i) ^ 2) := by
  classical
  let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
  let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
  change ρ < 1 ∧ ∀ x : Sum (Fin n) (Fin r) → ℝ,
      (∑ i : Sum (Fin n) (Fin r),
          (((paperDemandBlockGainMatrix α κ P Q).mulVec x) i - x i) ^ 2) ≤
      ρ * (∑ i : Sum (Fin n) (Fin r), (x i) ^ 2)
  have hstage10 := demand_matrix_uniform_contraction
    P Q α μ M hα hμ hM hμM hcoercive hfull hpress
  change ρ < 1 ∧ ∀ (u : Fin n → ℝ) (v : Fin r → ℝ),
    (∑ j : Fin n, (α * u j - u j) ^ 2) +
      (∑ i : Fin r,
        (κ * ((P.mulVec u) i + (Q.mulVec v) i) - v i) ^ 2) ≤
      ρ * ((∑ j : Fin n, (u j) ^ 2) +
        (∑ i : Fin r, (v i) ^ 2)) at hstage10
  constructor
  · exact hstage10.1
  · intro x
    let u : Fin n → ℝ := fun i => x (Sum.inl i)
    let v : Fin r → ℝ := fun i => x (Sum.inr i)
    have hbase := hstage10.2 u v
    calc
      (∑ i : Sum (Fin n) (Fin r),
          (((paperDemandBlockGainMatrix α κ P Q).mulVec x) i - x i) ^ 2) =
        (∑ j : Fin n, (α * u j - u j) ^ 2) +
        (∑ i : Fin r,
          (κ * ((P.mulVec u) i + (Q.mulVec v) i) - v i) ^ 2) := by
        rw [Fintype.sum_sum_type]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          rw [paper_demand_block_pressure_action]
        · apply Finset.sum_congr rfl
          intro i _
          rw [paper_demand_block_seismicity_action]
      _ ≤ ρ * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)) := hbase
      _ = ρ * (∑ i : Sum (Fin n) (Fin r), (x i) ^ 2) := by
        simp only [Fintype.sum_sum_type, u, v]

/-- The Stage 43 norm argument is not specific to `Fin m`: a `Sum` of
finite index types is equally a Euclidean output space. -/
theorem paper_sum_matrix_squared_action_to_opNorm
    {n r : ℕ}
    (A : Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (henergy : ∀ x : Sum (Fin n) (Fin r) → ℝ,
      (∑ i : Sum (Fin n) (Fin r), ((A.mulVec x) i - x i) ^ 2) ≤
        δ ^ 2 * (∑ i : Sum (Fin n) (Fin r), (x i) ^ 2)) :
    ‖(1 : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
       EuclideanSpace ℝ (Sum (Fin n) (Fin r))) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin n) (Fin r)) A‖ ≤ δ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  let L : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin n) (Fin r)) :=
    (1 : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin n) (Fin r))) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin n) (Fin r)) A
  have hcoord (i : Sum (Fin n) (Fin r)) : (L x).ofLp i =
      x.ofLp i - (A.mulVec x.ofLp) i := by
    simp [L, Matrix.ofLp_toEuclideanCLM]
  have hsquared : ‖L x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖L x‖ ^ 2 =
          ∑ i : Sum (Fin n) (Fin r),
            ((A.mulVec x.ofLp) i - x.ofLp i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoord i]
        ring
      _ ≤ δ ^ 2 * (∑ i : Sum (Fin n) (Fin r),
          (x.ofLp i) ^ 2) := henergy x.ofLp
      _ = δ ^ 2 * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have hx : 0 ≤ ‖L x‖ := norm_nonneg _
  have hy : 0 ≤ δ * ‖x‖ := mul_nonneg hδ (norm_nonneg _)
  change ‖L x‖ ≤ δ * ‖x‖
  nlinarith

/-- The *actual non-diagonal* block gain is an operator contraction in
ordinary Euclidean coordinates; the prescribed demand scaling is κ. -/
theorem paper_demand_block_opNorm_contraction
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
    let δ : ℝ := Real.sqrt ρ
    δ < 1 ∧ ‖(1 : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin n) (Fin r))) -
       Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin n) (Fin r))
         (paperDemandBlockGainMatrix α κ P Q)‖ ≤ δ := by
  classical
  let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
  let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
  let δ : ℝ := Real.sqrt ρ
  change δ < 1 ∧ ‖(1 : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin n) (Fin r))) -
       Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin n) (Fin r))
         (paperDemandBlockGainMatrix α κ P Q)‖ ≤ δ
  have hcert := paper_demand_block_squared_action_certificate
    P Q α μ M hα hμ hM hμM hcoercive hfull hpress
  change ρ < 1 ∧ ∀ x : Sum (Fin n) (Fin r) → ℝ,
      (∑ i : Sum (Fin n) (Fin r),
          (((paperDemandBlockGainMatrix α κ P Q).mulVec x) i - x i) ^ 2) ≤
      ρ * (∑ i : Sum (Fin n) (Fin r), (x i) ^ 2) at hcert
  have hρnonneg : 0 ≤ ρ := by
    have hleft : (0 : ℝ) ≤ 1 - (1 - (α - 1) ^ 2) / 4 := by
      nlinarith [sq_nonneg (α - 1)]
    exact le_trans hleft (le_max_left _ _)
  have hδnonneg : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsquare : δ ^ 2 = ρ := Real.sq_sqrt hρnonneg
  have hδlt : δ < 1 := by
    nlinarith [hδsquare, hδnonneg, hcert.1]
  constructor
  · exact hδlt
  · apply paper_sum_matrix_squared_action_to_opNorm _ δ hδnonneg
    intro x
    rw [hδsquare]
    exact hcert.2 x

/-- Uniform demand-coefficient hypotheses yield a uniform Euclidean
contraction and hence the same canonical inverse certificate as Stage 42.
The matrices `P(t)` and `Q(t)` may vary with the seismicity field. -/
theorem paper_actual_demand_gain_inverse_certificate
    {n r : ℕ}
    (P : ℝ → Matrix (Fin r) (Fin n) ℝ)
    (Q : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (α μ M : ℝ)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hcoercive : ∀ t v,
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        ∑ i : Fin r, v i * ((Q t).mulVec v) i)
    (hfull : ∀ t (u : Fin n → ℝ) (v : Fin r → ℝ),
      (∑ i : Fin r, (((P t).mulVec u) i + ((Q t).mulVec v) i) ^ 2) ≤
        M ^ 2 * ((∑ j : Fin n, (u j) ^ 2) +
          (∑ i : Fin r, (v i) ^ 2)))
    (hpress : ∀ t (u : Fin n → ℝ),
      (∑ i : Fin r, (((P t).mulVec u) i) ^ 2) ≤
        M ^ 2 * (∑ j : Fin n, (u j) ^ 2))
    (t : ℝ) (x : EuclideanSpace ℝ (Sum (Fin n) (Fin r))) :
    let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
    let δ : ℝ := Real.sqrt ρ
    let G : ℝ → EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
         EuclideanSpace ℝ (Sum (Fin n) (Fin r)) :=
       fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
         (n := Sum (Fin n) (Fin r))
         (paperDemandBlockGainMatrix α κ (P s) (Q s))
    IsUnit (G t) ∧ ‖Ring.inverse (G t) x‖ ≤
      (1 / (1 - δ)) * ‖x‖ := by
  classical
  let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
  let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
  let δ : ℝ := Real.sqrt ρ
  let G : ℝ → EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
    EuclideanSpace ℝ (Sum (Fin n) (Fin r)) :=
       fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
         (n := Sum (Fin n) (Fin r))
         (paperDemandBlockGainMatrix α κ (P s) (Q s))
  change IsUnit (G t) ∧ ‖Ring.inverse (G t) x‖ ≤
      (1 / (1 - δ)) * ‖x‖
  have hcert (s : ℝ) := paper_demand_block_opNorm_contraction
      (P s) (Q s) α μ M hα hμ hM hμM
      (hcoercive s) (hfull s) (hpress s)
  have hδ : δ < 1 := (hcert t).1
  have hclose : ∀ s,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin n) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin n) (Fin r))) - G s‖ ≤ δ := by
    intro s
    exact (hcert s).2
  constructor
  · exact paper_gain_isUnit_of_contraction G δ hδ hclose t
  · exact paper_gain_ringInverse_action_bound_of_contraction
      G δ hδ hclose t x

end ReservoirSeismicityControl
