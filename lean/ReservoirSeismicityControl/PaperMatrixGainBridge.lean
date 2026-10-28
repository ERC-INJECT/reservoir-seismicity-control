import ReservoirSeismicityControl.PaperGainContraction
import ReservoirSeismicityControl.MatrixContraction
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Stage 43 — From the actual well matrices to the Euclidean operator gain

Stages 6–7 established a squared Euclidean contraction for the actual
unconstrained gain `B(t) C₀`, with the explicit nominal right inverse
`C₀ = nominalRightInverse B₀`. Stage 42 needs an operator-norm bound on
`1 - G(t)`. The following result connects those *same* estimates using
Mathlib's isometric Euclidean-space representation of real matrices.

The physical row interval `lo ≤ gᵢ(t) ≤ hi` remains a hypothesis,
just as in Stage 7. No mesh or time derivative of Q appears here.

The weighted, non-diagonal demand controller is *not* covered by the
unconstrained well-support hypothesis and must be treated separately.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- The actual well matrix composed with the explicitly constructed
nominal right inverse of Stage 6. -/
noncomputable def paperWellGainMatrix {m n : ℕ}
    (B B₀ : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i k => ∑ j : Fin n, B i j * nominalRightInverse B₀ j k

/-- Conversion of a uniform squared Euclidean matrix action bound into
an induced operator-norm bound. This is the missing finite-dimensional
bridge between Stage 7 and Stage 42. -/
theorem paper_matrix_squared_action_to_opNorm
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (henergy : ∀ x : Fin m → ℝ,
      (∑ i : Fin m, ((A.mulVec x) i - x i) ^ 2) ≤
        δ ^ 2 * (∑ i : Fin m, (x i) ^ 2)) :
    ‖(1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) A‖ ≤ δ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) A
  have hcoord (i : Fin m) : (L x).ofLp i =
      x.ofLp i - (A.mulVec x.ofLp) i := by
    simp [L, Matrix.ofLp_toEuclideanCLM]
  have hsquared : ‖L x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖L x‖ ^ 2 =
          ∑ i : Fin m, ((A.mulVec x.ofLp) i - x.ofLp i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoord i]
        ring
      _ ≤ δ ^ 2 * (∑ i : Fin m, (x.ofLp i) ^ 2) := henergy x.ofLp
      _ = δ ^ 2 * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have hx : 0 ≤ ‖L x‖ := norm_nonneg _
  have hy : 0 ≤ δ * ‖x‖ := mul_nonneg hδ (norm_nonneg _)
  change ‖L x‖ ≤ δ * ‖x‖
  nlinarith

/-- Stage 7's physical well matrix contraction is *exactly* an
operator-norm contraction when the output carries the Euclidean norm. -/
theorem paper_actual_well_gain_opNorm_contraction
    {m n : ℕ}
    (B : ℝ → Matrix (Fin m) (Fin n) ℝ)
    (B₀ : Matrix (Fin m) (Fin n) ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ t i j, wellRegion j ≠ some i → B t i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi < 2)
    (hgain : ∀ t i,
      lo ≤ (∑ j : Fin n, B t i j * nominalRightInverse B₀ j i) ∧
      (∑ j : Fin n, B t i j * nominalRightInverse B₀ j i) ≤ hi) :
    let δ : ℝ := max |lo - 1| |hi - 1|
    δ < 1 ∧ ∀ t,
      ‖(1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) (paperWellGainMatrix (B t) B₀)‖ ≤ δ := by
  classical
  dsimp only
  have hmargin := interval_gain_margin_lt_one lo hi hlo hle hhi
  constructor
  · exact hmargin.2
  · intro t
    apply paper_matrix_squared_action_to_opNorm
      (paperWellGainMatrix (B t) B₀)
      (max |lo - 1| |hi - 1|) hmargin.1
    intro x
    have h := (actual_gain_energy_contraction
      (B t) B₀ wellRegion (hB t) hB₀
      lo hi hlo hle hhi (hgain t) x).1
    simpa only [paperWellGainMatrix, Matrix.mulVec, dotProduct] using h

/-- The actual unconstrained well gain has a canonical inverse with
an explicitly controlled action norm, with no independent isUnit or
inverse bound hypotheses. -/
theorem paper_actual_well_gain_inverse_certificate
    {m n : ℕ}
    (B : ℝ → Matrix (Fin m) (Fin n) ℝ)
    (B₀ : Matrix (Fin m) (Fin n) ℝ)
    (wellRegion : Fin n → Option (Fin m))
    (hB : ∀ t i j, wellRegion j ≠ some i → B t i j = 0)
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hhi : hi < 2)
    (hgain : ∀ t i,
      lo ≤ (∑ j : Fin n, B t i j * nominalRightInverse B₀ j i) ∧
      (∑ j : Fin n, B t i j * nominalRightInverse B₀ j i) ≤ hi)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    let δ : ℝ := max |lo - 1| |hi - 1|
    let G : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      fun s => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) (paperWellGainMatrix (B s) B₀)
    IsUnit (G t) ∧
      ‖Ring.inverse (G t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ := by
  classical
  dsimp only
  let δ : ℝ := max |lo - 1| |hi - 1|
  let G : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun s => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) (paperWellGainMatrix (B s) B₀)
  have hcert := paper_actual_well_gain_opNorm_contraction
    B B₀ wellRegion hB hB₀ lo hi hlo hle hhi hgain
  have hδ : δ < 1 := by
    exact hcert.1
  have hclose : ∀ s, ‖(1 : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m)) - G s‖ ≤ δ := by
    exact hcert.2
  constructor
  · exact paper_gain_isUnit_of_contraction G δ hδ hclose t
  · exact paper_gain_ringInverse_action_bound_of_contraction
      G δ hδ hclose t x

end ReservoirSeismicityControl
