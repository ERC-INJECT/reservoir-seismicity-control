import ReservoirSeismicityControl.Paper2026.SignedPhysicalBridge
import ReservoirSeismicityControl.PaperPhysicalDemandFinalCertificates
import Mathlib.Tactic

/-!
# P5: Appendix B with the positive SR coefficient of the 2026 manuscript

The retained Stage 45--59 demand proofs used an old SR row
  -h_j / (β |V_{R_i}|).
The signed error in (12) changes that row to
  +h_j / (β |V_{R_i}|), regardless of s = ±1.

We do NOT change the old proof files or interpret the physical β as negative.
The substitution `βlegacy = -βphysical` is an exact algebraic equality of
matrix coefficients: it lets us reuse the already proved block-gain and vertex
certificates with the correct positive physical SR sensitivity. The actual
physical β remains positive, and the vertex tests are now on the positive row.

This file addresses P5's SIGN and finite-dimensional contraction only.
The physical A.1--A.3 and allocation hypotheses still require verification.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- Positive unscaled SR well sensitivity in (15), before κ_R. -/
noncomputable def positiveSRWellMatrix {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then
    (1 / (β * volume i)) * h j else 0

/-- P5: exact bridge to all existing demand proofs. This is substitution
inside an old algebraic matrix, NOT a change of the physical parameter β. -/
theorem positive_sr_matrix_eq_legacy_rebased {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) :
    positiveSRWellMatrix wellRegion β volume h =
      ReservoirSeismicityControl.paperPhysicalSRWellMatrix wellRegion (-β) volume h := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp [positiveSRWellMatrix, ReservoirSeismicityControl.paperPhysicalSRWellMatrix,
      hj, neg_mul, div_eq_mul_inv]
  · simp [positiveSRWellMatrix, ReservoirSeismicityControl.paperPhysicalSRWellMatrix, hj]

/-- P0 -> P5: the new unscaled matrix is precisely the physical spatial
integral coefficient (15) once κ_R = 1/(γ₁₀ R₀*) is included. -/
theorem physical_sr_matrix_eq_scaled_positive
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ) :
    srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t =
      (1 / normalization) • positiveSRWellMatrix wellRegion β volume
        (fun j => ReservoirSeismicityControl.paperPhysicalSRWellMean μ (well j) γ₁ R t) := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp only [srPhysicalMatrix, positiveSRWellMatrix,
      Matrix.smul_apply, smul_eq_mul, if_pos hj]
    simp [div_eq_mul_inv, mul_inv_rev] <;> ring
  · simp [srPhysicalMatrix, positiveSRWellMatrix, hj]

/-- The entire pressure/SR well input matrix with the correct positive SR
rows. `κ = (γ₁₀ R₀*)⁻¹` and `α = β₀/β` in the manuscript. -/
noncomputable def positiveDemandWellMatrix {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (α κ : ℝ) : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  fun i j => match i with
    | Sum.inl a => α * Bᵤ₀ a j
    | Sum.inr a => κ * positiveSRWellMatrix wellRegion β volume h a j

/-- P5: no new proof of the old finite-dimensional matrix algebra is needed. -/
theorem positive_demand_matrix_eq_legacy_rebased {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) (α κ : ℝ) :
    positiveDemandWellMatrix Bᵤ₀ wellRegion β volume h α κ =
      ReservoirSeismicityControl.paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion (-β)
        volume h α κ := by
  classical
  ext i j
  cases i with
  | inl i => rfl
  | inr i =>
    change κ * positiveSRWellMatrix wellRegion β volume h i j =
      κ * ReservoirSeismicityControl.paperPhysicalSRWellMatrix wellRegion (-β) volume h i j
    rw [positive_sr_matrix_eq_legacy_rebased]

/-- The actual positive SR-to-pressure coupling after multiplying by C_W. -/
noncomputable def positiveSRPressureBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    Matrix (Fin r) (Fin u) ℝ :=
  fun i j => ∑ k : Fin w,
    positiveSRWellMatrix wellRegion β volume h i k * C k (Sum.inl j)

/-- The actual positive SR-to-SR coupling after multiplying by C_W. -/
noncomputable def positiveSRSRBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => ∑ k : Fin w,
    positiveSRWellMatrix wellRegion β volume h i k * C k (Sum.inr j)

theorem positive_sr_pressure_block_eq_legacy_rebased {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    positiveSRPressureBlock wellRegion β volume h C =
      ReservoirSeismicityControl.paperPhysicalSRPressureBlock wellRegion (-β) volume h C := by
  classical
  ext i j
  simp only [positiveSRPressureBlock, ReservoirSeismicityControl.paperPhysicalSRPressureBlock]
  rw [positive_sr_matrix_eq_legacy_rebased]

theorem positive_sr_sr_block_eq_legacy_rebased {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    positiveSRSRBlock wellRegion β volume h C =
      ReservoirSeismicityControl.paperPhysicalSRSRBlock wellRegion (-β) volume h C := by
  classical
  ext i j
  simp only [positiveSRSRBlock, ReservoirSeismicityControl.paperPhysicalSRSRBlock]
  rw [positive_sr_matrix_eq_legacy_rebased]

/-- Full positive SR allocated row action before κ_R. The manuscript
rewrites its two blocks as E(h)C_u and a diag(H)+E(h)C_R in (B15);
that particular mean/deviation identity remains to be checked. -/
noncomputable def positiveSRCombinedAction {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) :
    Fin r → ℝ :=
  fun i => ((positiveSRPressureBlock wellRegion β volume h C).mulVec xᵤ) i +
    ((positiveSRSRBlock wellRegion β volume h C).mulVec xᵣ) i

theorem positive_sr_combined_action_eq_legacy_rebased {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) :
    positiveSRCombinedAction wellRegion β volume C h xᵤ xᵣ =
      ReservoirSeismicityControl.paperPhysicalSRCombinedAction wellRegion (-β) volume C h xᵤ xᵣ := by
  funext i
  simp only [positiveSRCombinedAction, ReservoirSeismicityControl.paperPhysicalSRCombinedAction]
  rw [positive_sr_pressure_block_eq_legacy_rebased,
    positive_sr_sr_block_eq_legacy_rebased]

/-- P5: the allocated gain with positive SR coefficients, in Euclidean
operator norm, not an abstract preassumed gain. -/
noncomputable def positiveDemandGainCLM {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => ReservoirSeismicityControl.paperMatrixToEuclideanCLM
    (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume (h t) α κ * C)

theorem positive_demand_gain_eq_legacy_rebased {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) (t : ℝ) :
    positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C t =
      ReservoirSeismicityControl.paperPhysicalGainCLM Bᵤ₀ wellRegion (-β) volume h α κ C t := by
  classical
  dsimp only [positiveDemandGainCLM, ReservoirSeismicityControl.paperPhysicalGainCLM]
  rw [positive_demand_matrix_eq_legacy_rebased]

/-- P5, (B16)--(B18): contraction for the physically POSITIVE SR matrix,
using the already verified finite-vertex contraction proof. This removes
any need to redo the block spectral/Young estimates or add a new sign
hypothesis. The only vertex conditions are the manuscript's actual ones. -/
theorem positive_demand_contraction_from_vertices
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (lo hi : Fin w → ℝ) (h : ℝ → Fin w → ℝ)
    (α μ M : ℝ)
    (hBC : B₀ * C = 1)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hlo : ∀ t j, lo j ≤ h t j)
    (hhi : ∀ t j, h t j ≤ hi j)
    (hvertexCoercive : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    let κ := ReservoirSeismicityControl.paperPhysicalDemandScale α μ M
    let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin α μ M
    δ < 1 ∧
      ∀ t : ℝ,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h α κ C t‖ ≤ δ := by
  classical
  have hc : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((ReservoirSeismicityControl.paperPhysicalSRSRBlock wellRegion (-β) volume hV C).mulVec v) i := by
    intro hV hvertex v
    simpa only [positive_sr_sr_block_eq_legacy_rebased] using
      hvertexCoercive hV hvertex v
  have hu : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (ReservoirSeismicityControl.paperPhysicalSRCombinedAction wellRegion (-β) volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)) := by
    intro hV hvertex xᵤ xᵣ
    simpa only [positive_sr_combined_action_eq_legacy_rebased] using
      hvertexUpper hV hvertex xᵤ xᵣ
  have hbase := ReservoirSeismicityControl.paper_physical_demand_contraction_from_vertices
    B₀ C wellRegion (-β) volume lo hi h α μ M
    hBC hα hμ hM hμM hlo hhi hc hu
  change ReservoirSeismicityControl.paperPhysicalDemandMargin α μ M < 1 ∧
    ∀ t,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        ReservoirSeismicityControl.paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
          wellRegion (-β) volume h α (ReservoirSeismicityControl.paperPhysicalDemandScale α μ M) C t‖ ≤
        ReservoirSeismicityControl.paperPhysicalDemandMargin α μ M at hbase
  refine ⟨hbase.1, ?_⟩
  intro t
  -- Transport the already proved norm bound through an explicit gain equality.
  -- Avoid tactic rewriting under the dependent matrix/CLM elaboration.
  have hEq :
      positiveDemandGainCLM
        (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume h α
          (ReservoirSeismicityControl.paperPhysicalDemandScale α μ M) C t =
      ReservoirSeismicityControl.paperPhysicalGainCLM
        (fun i j => B₀ (Sum.inl i) j)
        wellRegion (-β) volume h α
          (ReservoirSeismicityControl.paperPhysicalDemandScale α μ M) C t :=
    positive_demand_gain_eq_legacy_rebased
      (fun i j => B₀ (Sum.inl i) j)
      wellRegion β volume h α (ReservoirSeismicityControl.paperPhysicalDemandScale α μ M) C t
  have hNormEq := congrArg
    (fun G : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r)) =>
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r))) - G‖) hEq
  exact hNormEq.le.trans (hbase.2 t)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_matrix_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_matrix_eq_scaled_positive
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_matrix_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_gain_eq_legacy_rebased
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_vertices
