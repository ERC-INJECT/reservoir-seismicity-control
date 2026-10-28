import ReservoirSeismicityControl.Paper2026.PositiveDemandB15
import Mathlib.Tactic

/-!
# P5 / Appendix B (B16): manuscript's mean/deviation vertex test

The B15 identity has been compiled locally. Here we *use* it to express
Assumption 6's finite vertex test in the paper's actual variables
  a diag(H(h)) + E(h) C_R  (symmetric part >= μ I),
  T(h) = [E(h) C_u, a diag(H(h)) + E(h) C_R].

The existing verified contraction theorem expects equivalent quadratic and
norm inequalities for the positive physical sensitivity blocks. We prove
those equivalences rather than assuming new, independent vertex conditions.
The vertex tests and B₀ C_W = I remain explicit A6 obligations; none is
asserted for an arbitrary proposed demand matrix W.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- Bottom-right B15 block *before* the common positive factor κ_R. -/
noncomputable def positiveB16SRBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    (if i = j then (β₀ / β) * positiveSRRegionMean wellRegion h i else 0) +
      ∑ k : Fin w,
        positiveSRDeviation wellRegion β volume h
          (positiveSRRegionMean wellRegion h) i k * C k (Sum.inr j)

/-- Bottom-left B15 block, before κ_R. -/
noncomputable def positiveB16CrossBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) : Matrix (Fin r) (Fin u) ℝ :=
  fun i j => ∑ k : Fin w,
    positiveSRDeviation wellRegion β volume h
      (positiveSRRegionMean wellRegion h) i k * C k (Sum.inl j)

/-- The literal symmetric matrix of B16; its positive quadratic form is
what is meant by the Loewner inequality in Assumption 6. -/
noncomputable def positiveB16SymBlock {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (positiveB16SRBlock wellRegion β β₀ volume C h i j +
    positiveB16SRBlock wellRegion β β₀ volume C h j i) / 2

/-- The two-block physical T(h) used to define M in Appendix B. -/
noncomputable def positiveB16Action {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ)
    (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) : Fin r → ℝ :=
  fun i => ((positiveB16CrossBlock wellRegion β volume C h).mulVec xᵤ) i +
    ((positiveB16SRBlock wellRegion β β₀ volume C h).mulVec xᵣ) i

/-- Use B15, without any extra E C_W = 0 assumption. -/
theorem positive_B16_sr_block_eq_physical {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
      srNominalMatrix wellRegion β₀ volume i k) :
    positiveSRSRBlock wellRegion β volume h C =
      positiveB16SRBlock wellRegion β β₀ volume C h := by
  classical
  ext i j
  have hs := positive_sr_allocated_mean_deviation
    B₀ C wellRegion β β₀ volume h
    (positiveSRRegionMean wellRegion h)
    hβ hβ₀ hvol hBC hB₀SR i (Sum.inr j)
  by_cases hij : i = j
  · subst j
    simpa [positiveSRSRBlock, positiveB16SRBlock] using hs
  · have hne : (Sum.inr i : Sum (Fin u) (Fin r)) ≠ Sum.inr j := by
      intro heq
      exact hij (Sum.inr.inj heq)
    simpa [positiveSRSRBlock, positiveB16SRBlock, hij, hne] using hs

/-- The B15 E(h) C_u term equals the actual positive SR-pressure block. -/
theorem positive_B16_cross_block_eq_physical {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
      srNominalMatrix wellRegion β₀ volume i k) :
    positiveSRPressureBlock wellRegion β volume h C =
      positiveB16CrossBlock wellRegion β volume C h := by
  classical
  ext i j
  have hs := positive_sr_allocated_mean_deviation
    B₀ C wellRegion β β₀ volume h
    (positiveSRRegionMean wellRegion h)
    hβ hβ₀ hvol hBC hB₀SR i (Sum.inl j)
  simpa [positiveSRPressureBlock, positiveB16CrossBlock] using hs

/-- The upper test on the *explicit* T(h), rather than a free block action. -/
theorem positive_B16_action_eq_physical {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
      srNominalMatrix wellRegion β₀ volume i k)
    (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) :
    positiveSRCombinedAction wellRegion β volume C h xᵤ xᵣ =
      positiveB16Action wellRegion β β₀ volume C h xᵤ xᵣ := by
  funext i
  change ((positiveSRPressureBlock wellRegion β volume h C).mulVec xᵤ) i +
      ((positiveSRSRBlock wellRegion β volume h C).mulVec xᵣ) i =
    ((positiveB16CrossBlock wellRegion β volume C h).mulVec xᵤ) i +
      ((positiveB16SRBlock wellRegion β β₀ volume C h).mulVec xᵣ) i
  rw [positive_B16_cross_block_eq_physical B₀ C wellRegion β β₀ volume h
      hβ hβ₀ hvol hBC hB₀SR,
    positive_B16_sr_block_eq_physical B₀ C wellRegion β β₀ volume h
      hβ hβ₀ hvol hBC hB₀SR]

/-- A real quadratic form depends only on the symmetric part of its matrix.
This is the exact conversion from the B16 Loewner form to the coercivity
input of the already proved contraction result. -/
theorem positive_B16_symmetric_quadratic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) :
    (∑ i : Fin r, v i *
      (Matrix.mulVec
        ((fun i j => (A i j + A j i) / 2) :
          Matrix (Fin r) (Fin r) ℝ) v) i) =
    ∑ i : Fin r, v i * (A.mulVec v) i := by
  classical
  have hswap :
      (∑ i : Fin r, ∑ j : Fin r, v i * (A j i * v j)) =
      ∑ i : Fin r, ∑ j : Fin r, v i * (A i j * v j) := by
    calc
      _ = ∑ j : Fin r, ∑ i : Fin r, v i * (A j i * v j) :=
        Finset.sum_comm
      _ = ∑ j : Fin r, ∑ i : Fin r, v j * (A j i * v i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := rfl
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i : Fin r, v i *
      (∑ j : Fin r, ((A i j + A j i) / 2) * v j)) =
      (∑ i : Fin r, ∑ j : Fin r, v i * (A i j * v j)) / 2 +
      (∑ i : Fin r, ∑ j : Fin r, v i * (A j i * v j)) / 2 := by
        calc
          _ = ∑ i : Fin r, ∑ j : Fin r,
                ((v i * (A i j * v j)) / 2 +
                  (v i * (A j i * v j)) / 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i : Fin r, ∑ j : Fin r, v i * (A i j * v j) := by
      rw [hswap]
      ring
    _ = ∑ i : Fin r, v i * (∑ j : Fin r, A i j * v j) := by
      simp only [Finset.mul_sum]

/-- The manuscript's B16 symmetric vertex inequality and the T-vertex upper
bound imply *exactly* the hypotheses of the existing P5/B18 certificate.
B₀ C_W = I is still explicitly assumed from the rank test in Assumption 6. -/
theorem positive_demand_contraction_from_B16_vertices
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (lo hi : Fin w → ℝ) (h : ℝ → Fin w → ℝ)
    (μ M : ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
      srNominalMatrix wellRegion β₀ volume i k)
    (hα : ((β₀ / β) - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hlo : ∀ t j, lo j ≤ h t j)
    (hhi : ∀ t j, h t j ≤ hi j)
    (hB16Vertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveB16SymBlock wellRegion β β₀ volume C hV).mulVec v) i)
    (hTVertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveB16Action wellRegion β β₀ volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    let a := β₀ / β
    let κ := ReservoirSeismicityControl.paperPhysicalDemandScale a μ M
    let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin a μ M
    δ < 1 ∧
      ∀ t : ℝ,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h a κ C t‖ ≤ δ := by
  classical
  have hc : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveSRSRBlock wellRegion β volume hV C).mulVec v) i := by
    intro hV hv v
    have hs :
        (∑ i : Fin r, v i *
          ((positiveB16SymBlock wellRegion β β₀ volume C hV).mulVec v) i) =
        ∑ i : Fin r, v i *
          ((positiveB16SRBlock wellRegion β β₀ volume C hV).mulVec v) i := by
      change (∑ i : Fin r, v i *
        (Matrix.mulVec
          ((fun i j =>
            (positiveB16SRBlock wellRegion β β₀ volume C hV i j +
              positiveB16SRBlock wellRegion β β₀ volume C hV j i) / 2) :
            Matrix (Fin r) (Fin r) ℝ) v) i) =
        ∑ i : Fin r, v i *
          ((positiveB16SRBlock wellRegion β β₀ volume C hV).mulVec v) i
      exact positive_B16_symmetric_quadratic
        (positiveB16SRBlock wellRegion β β₀ volume C hV) v
    have hphysical :
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveB16SRBlock wellRegion β β₀ volume C hV).mulVec v) i := by
      calc
        _ ≤ ∑ i : Fin r, v i *
            ((positiveB16SymBlock wellRegion β β₀ volume C hV).mulVec v) i :=
              hB16Vertices hV hv v
        _ = _ := hs
    rw [positive_B16_sr_block_eq_physical B₀ C wellRegion β β₀ volume hV
      hβ hβ₀ hvol hBC hB₀SR]
    exact hphysical
  have hu : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)) := by
    intro hV hv xᵤ xᵣ
    rw [positive_B16_action_eq_physical B₀ C wellRegion β β₀ volume hV
      hβ hβ₀ hvol hBC hB₀SR]
    exact hTVertices hV hv xᵤ xᵣ
  exact positive_demand_contraction_from_vertices
    B₀ C wellRegion β volume lo hi h (β₀ / β) μ M
    hBC hα hμ hM hμM hlo hhi hc hu

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_sr_block_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_cross_block_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_action_eq_physical
#print axioms ReservoirSeismicityControl.Paper2026.positive_B16_symmetric_quadratic
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_contraction_from_B16_vertices
