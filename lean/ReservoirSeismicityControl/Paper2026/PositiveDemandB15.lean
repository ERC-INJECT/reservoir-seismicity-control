import ReservoirSeismicityControl.Paper2026.PositiveDemandRates
import Mathlib.Tactic

/-!
# P5: Appendix B, equation (B15), positive physical SR gain

Here `H_i(h)` is the arithmetic mean of the physical well sensitivities
`h_j = |V_j^*|⁻¹ ∫_{V_j^*} γ₁ R` over the wells assigned to region i.
The exact algebraic identity

  B_R(h) = κ_R [ (β₀/β) diag(H(h)) B_R0 + E(h) ]

is verified entrywise, then multiplied by the actual allocation `C_W`.
The only nominal identities needed are the SR rows of `B₀` and
`B₀ C_W = I`, already furnished by the manuscript's A6 construction.
There is no independent diagonal-gain assumption: E(h) C_W is retained.
No additional PDE, convexity, or stability result is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- `I_i` in Appendix B, written using the physical well-to-region map. -/
def srRegionWells {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r)) (i : Fin r) : Finset (Fin w) :=
  Finset.univ.filter (fun j => wellRegion j = some i)

/-- `H_i(h) = (1/N_i) ∑_{j∈I_i} h_j` in Appendix B.
Nonemptiness of I_i is Assumption 4; the algebraic identity below does not
require division by N_i, and also applies to any vector H. -/
noncomputable def positiveSRRegionMean {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r)) (h : Fin w → ℝ) : Fin r → ℝ :=
  fun i => (∑ j ∈ srRegionWells wellRegion i, h j) /
    ((srRegionWells wellRegion i).card : ℝ)

/-- Deviation matrix `E(h)` in the manuscript, with the *positive* signed-SR
convention and actual regional volumes. -/
noncomputable def positiveSRDeviation {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h : Fin w → ℝ) (H : Fin r → ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then
    (h j - H i) / (β * volume i) else 0

/-- The physical input row is the sum of the regional-mean row and
its within-region deviation, exactly as in the line before (B15).
`H` is arbitrary here: the identity can then be specialized to `H(h)`.
The nominal SR row is `1/(β₀ |V_Ri|)` on the region's wells. -/
theorem positive_sr_mean_deviation_entry {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (h : Fin w → ℝ) (H : Fin r → ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (i : Fin r) (j : Fin w) :
    positiveSRWellMatrix wellRegion β volume h i j =
      (β₀ / β) * H i * srNominalMatrix wellRegion β₀ volume i j +
        positiveSRDeviation wellRegion β volume h H i j := by
  classical
  by_cases hj : wellRegion j = some i
  · simp only [positiveSRWellMatrix, srNominalMatrix,
      positiveSRDeviation, if_pos hj]
    field_simp [hβ, hβ₀, hvol i]
    <;> ring
  · simp [positiveSRWellMatrix, srNominalMatrix,
      positiveSRDeviation, hj]

/-- The exact B15 mean/deviation split after *any* constant well allocation C.
In particular, no premise `E C = 0` or diagonal gain is inserted. -/
theorem positive_sr_allocated_mean_deviation {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (h : Fin w → ℝ) (H : Fin r → ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
       srNominalMatrix wellRegion β₀ volume i k)
    (i : Fin r) (j : Sum (Fin u) (Fin r)) :
    (∑ k : Fin w, positiveSRWellMatrix wellRegion β volume h i k * C k j) =
      (β₀ / β) * H i * (if Sum.inr i = j then (1 : ℝ) else 0) +
        ∑ k : Fin w, positiveSRDeviation wellRegion β volume h H i k * C k j := by
  classical
  have hnom :
      (∑ k : Fin w, srNominalMatrix wellRegion β₀ volume i k * C k j) =
        if Sum.inr i = j then (1 : ℝ) else 0 := by
    calc
      _ = ∑ k : Fin w, B₀ (Sum.inr i) k * C k j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hB₀SR i k]
      _ = (1 : Matrix (Sum (Fin u) (Fin r))
          (Sum (Fin u) (Fin r)) ℝ) (Sum.inr i) j := by
        have h := congrArg
          (fun A : Matrix (Sum (Fin u) (Fin r))
             (Sum (Fin u) (Fin r)) ℝ => A (Sum.inr i) j) hBC
        simpa only [Matrix.mul_apply] using h
      _ = if Sum.inr i = j then (1 : ℝ) else 0 := by
        simp [Matrix.one_apply]
  calc
    _ = ∑ k : Fin w,
          (((β₀ / β) * H i * srNominalMatrix wellRegion β₀ volume i k) +
            positiveSRDeviation wellRegion β volume h H i k) * C k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [positive_sr_mean_deviation_entry wellRegion β β₀ volume h H
        hβ hβ₀ hvol i k]
    _ = ∑ k : Fin w,
          (((β₀ / β) * H i) *
              (srNominalMatrix wellRegion β₀ volume i k * C k j) +
            positiveSRDeviation wellRegion β volume h H i k * C k j) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (β₀ / β) * H i *
          (∑ k : Fin w, srNominalMatrix wellRegion β₀ volume i k * C k j) +
          ∑ k : Fin w,
            positiveSRDeviation wellRegion β volume h H i k * C k j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hnom]

/-- (B15), including the pressure-to-SR E C_u block and the full
SR-to-SR block. The physical H is the arithmetic region mean of the actual
well sensitivities. The equation follows from `B₀ C_W = I` and its nominal
SR rows; neither `E C_W = 0` nor a vertex inequality is assumed. -/
theorem positive_demand_B15_gain {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) (κ : ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hBC : B₀ * C = 1)
    (hB₀SR : ∀ i k, B₀ (Sum.inr i) k =
       srNominalMatrix wellRegion β₀ volume i k) :
    let a := β₀ / β
    let H := positiveSRRegionMean wellRegion h
    let E := positiveSRDeviation wellRegion β volume h H
    positiveDemandWellMatrix
        (fun i k => B₀ (Sum.inl i) k) wellRegion β volume h a κ * C =
      ReservoirSeismicityControl.paperDemandBlockGainMatrix a κ
        (fun i j => ∑ k : Fin w, E i k * C k (Sum.inl j))
        (fun i j => (if i = j then a * H i else 0) +
          ∑ k : Fin w, E i k * C k (Sum.inr j)) := by
  classical
  dsimp only
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hnom : (∑ k : Fin w,
          B₀ (Sum.inl i) k * C k (Sum.inl j)) =
          if i = j then (1 : ℝ) else 0 := by
        have h := congrArg
          (fun A : Matrix (Sum (Fin u) (Fin r))
             (Sum (Fin u) (Fin r)) ℝ => A (Sum.inl i) (Sum.inl j)) hBC
        simpa [Matrix.mul_apply, Matrix.one_apply] using h
      change (∑ k : Fin w,
          ((β₀ / β) * B₀ (Sum.inl i) k) * C k (Sum.inl j)) =
        (if i = j then β₀ / β else 0)
      calc
        _ = (β₀ / β) * (∑ k : Fin w,
            B₀ (Sum.inl i) k * C k (Sum.inl j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [hnom]; split_ifs <;> ring
    | inr j =>
      have hnom : (∑ k : Fin w,
          B₀ (Sum.inl i) k * C k (Sum.inr j)) = 0 := by
        have h := congrArg
          (fun A : Matrix (Sum (Fin u) (Fin r))
             (Sum (Fin u) (Fin r)) ℝ => A (Sum.inl i) (Sum.inr j)) hBC
        simpa [Matrix.mul_apply, Matrix.one_apply] using h
      change (∑ k : Fin w,
          ((β₀ / β) * B₀ (Sum.inl i) k) * C k (Sum.inr j)) = 0
      calc
        _ = (β₀ / β) * (∑ k : Fin w,
            B₀ (Sum.inl i) k * C k (Sum.inr j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by rw [hnom]; ring
  | inr i =>
    cases j with
    | inl j =>
      have hsplit := positive_sr_allocated_mean_deviation B₀ C
        wellRegion β β₀ volume h (positiveSRRegionMean wellRegion h)
        hβ hβ₀ hvol hBC hB₀SR i (Sum.inl j)
      change (∑ k : Fin w,
          (κ * positiveSRWellMatrix wellRegion β volume h i k) *
            C k (Sum.inl j)) =
        κ * (∑ k : Fin w,
          positiveSRDeviation wellRegion β volume h
            (positiveSRRegionMean wellRegion h) i k * C k (Sum.inl j))
      calc
        _ = κ * (∑ k : Fin w,
              positiveSRWellMatrix wellRegion β volume h i k *
                C k (Sum.inl j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by simpa only using congrArg (fun z : ℝ => κ * z) (by
          simpa using hsplit)
    | inr j =>
      have hsplit := positive_sr_allocated_mean_deviation B₀ C
        wellRegion β β₀ volume h (positiveSRRegionMean wellRegion h)
        hβ hβ₀ hvol hBC hB₀SR i (Sum.inr j)
      change (∑ k : Fin w,
          (κ * positiveSRWellMatrix wellRegion β volume h i k) *
            C k (Sum.inr j)) =
        κ * ((if i = j then (β₀ / β) *
            positiveSRRegionMean wellRegion h i else 0) +
          ∑ k : Fin w,
            positiveSRDeviation wellRegion β volume h
              (positiveSRRegionMean wellRegion h) i k * C k (Sum.inr j))
      calc
        _ = κ * (∑ k : Fin w,
              positiveSRWellMatrix wellRegion β volume h i k *
                C k (Sum.inr j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by simpa only using congrArg (fun z : ℝ => κ * z) (by
          simpa using hsplit)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_mean_deviation_entry
#print axioms ReservoirSeismicityControl.Paper2026.positive_sr_allocated_mean_deviation
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B15_gain
