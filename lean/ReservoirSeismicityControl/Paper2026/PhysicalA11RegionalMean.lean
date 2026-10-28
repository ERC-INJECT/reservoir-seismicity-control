import ReservoirSeismicityControl.Paper2026.PhysicalA12FullPhysical
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: the actual SR diagonal is the arithmetic mean (A11)

The preceding, locally accepted P4 module establishes the complete support
structure of B(t) B₀⁺ and its pressure diagonal. This module proves the
remaining *identification*, rather than taking an assembled SR gain as an
independent hypothesis. The scalar h_j(t) below is the actual well Lebesgue
mean of γ₁R, and the finite set I_i consists of wells assigned to SR region i.
Because the nominal B₀ coefficient is identical on I_i, its Gram-weighted
right-inverse reproduces exactly the ordinary arithmetic average in (A11).

No semigroup, Sobolev, or stability theorem is formalized here. Bounds on
H_i and the full A12 operator norm are separate ensuing steps.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- Actual physical SR row divided by its constant nominal row. -/
theorem paper_A11_full_physical_SR_row
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) (t : ℝ)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0) (hnorm : normalization ≠ 0)
    (hvolume : ∀ k, volume k ≠ 0)
    (i : Fin r) (j : Fin w) :
    paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
        (Sum.inr i) j =
      ((β₀ / β) * paperPhysicalSRWellMean μ (well j) γ₁ R t / normalization) *
        paperA12FullNominalMatrix assignment β₀ volume (Sum.inr i) j := by
  classical
  change (if assignment j = some (Sum.inr i) then
      paperPhysicalSRWellMean μ (well j) γ₁ R t /
        (normalization * β * volume (Sum.inr i)) else 0) =
    ((β₀ / β) * paperPhysicalSRWellMean μ (well j) γ₁ R t / normalization) *
      (if assignment j = some (Sum.inr i) then
        (1 : ℝ) / (β₀ * volume (Sum.inr i)) else 0)
  by_cases hj : assignment j = some (Sum.inr i)
  · simp only [if_pos hj]
    field_simp [hβ, hβ₀, hnorm, hvolume (Sum.inr i)]
    <;> ring
  · simp only [if_neg hj, mul_zero]

/-- Equation (A11), literally: in every SR output region, the diagonal of
B(t)B₀⁺ is (β₀/β)/normalization times the arithmetic average of the actual
Lebesgue well means in that region. The nonempty-region premise is exactly
the coverage clause of Assumption 4; it is NOT a new gain assumption. -/
theorem paper_A11_full_physical_SR_gain_arithmetic_mean
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) (t : ℝ)
    (hβ : β ≠ 0) (hβ₀ : 0 < β₀) (hnorm : normalization ≠ 0)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (i : Fin r) :
    let I : Finset (Fin w) :=
      Finset.univ.filter (fun j => assignment j = some (Sum.inr i))
    let H : ℝ :=
      (I.sum (fun j => paperPhysicalSRWellMean μ (well j) γ₁ R t)) /
        (I.card : ℝ)
    (paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t *
        paperA12FullNominalRightInverse
          (paperA12FullNominalMatrix assignment β₀ volume))
        (Sum.inr i) (Sum.inr i) = (β₀ / β) * H / normalization := by
  classical
  dsimp only
  let I : Finset (Fin w) :=
    Finset.univ.filter (fun j => assignment j = some (Sum.inr i))
  let B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    paperA12FullNominalMatrix assignment β₀ volume
  let c : ℝ := 1 / (β₀ * volume (Sum.inr i))
  let h : Fin w → ℝ := fun j => paperPhysicalSRWellMean μ (well j) γ₁ R t
  let a : ℝ := (β₀ / β) / normalization
  have hcpos : 0 < c := by
    have hden : 0 < β₀ * volume (Sum.inr i) :=
      mul_pos hβ₀ (hvolume (Sum.inr i))
    dsimp only [c]
    exact div_pos (by norm_num : (0 : ℝ) < 1) hden
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hIpos : 0 < I.card := Finset.card_pos.mpr (by
    obtain ⟨j, hj⟩ := hcovered (Sum.inr i)
    exact ⟨j, by simp [I, hj]⟩)
  have hI : (I.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hIpos)
  have hrow (j : Fin w) :
      paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
          (Sum.inr i) j = a * h j * B₀ (Sum.inr i) j := by
    have hsource := paper_A11_full_physical_SR_row
      μ well γ₁ R assignment β β₀ normalization volume t
      hβ (ne_of_gt hβ₀) hnorm (fun k => ne_of_gt (hvolume k)) i j
    dsimp only [a, h, B₀]
    convert hsource using 1 <;> ring
  have hnom (j : Fin w) :
      B₀ (Sum.inr i) j =
        if assignment j = some (Sum.inr i) then c else 0 := by
    rfl
  have hgram :
      paperA12FullGramDiag B₀ (Sum.inr i) = (I.card : ℝ) * (c * c) := by
    change (∑ j : Fin w, B₀ (Sum.inr i) j * B₀ (Sum.inr i) j) = _
    calc
      _ = ∑ j : Fin w,
          if assignment j = some (Sum.inr i) then c * c else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hnom]
            by_cases hji : assignment j = some (Sum.inr i)
            · simp only [if_pos hji]
            · simp only [if_neg hji, zero_mul]
      _ = I.sum (fun _ => c * c) := by
            simp only [I, Finset.sum_filter]
      _ = (I.card : ℝ) * (c * c) := by
            simp [nsmul_eq_mul]
  have hnumerator :
      (∑ j : Fin w,
        paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
          (Sum.inr i) j * B₀ (Sum.inr i) j) =
        a * (I.sum h) * (c * c) := by
    calc
      _ = ∑ j : Fin w, a * h j * (B₀ (Sum.inr i) j * B₀ (Sum.inr i) j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hrow]
            ring
      _ = ∑ j : Fin w,
          if assignment j = some (Sum.inr i) then a * h j * (c * c) else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hnom]
            by_cases hji : assignment j = some (Sum.inr i)
            · simp only [if_pos hji]
            · simp only [if_neg hji, zero_mul, mul_zero]
      _ = I.sum (fun j => a * h j * (c * c)) := by
            simp only [I, Finset.sum_filter]
      _ = a * (I.sum h) * (c * c) := by
            calc
              _ = I.sum (fun j => h j * (a * (c * c))) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (I.sum h) * (a * (c * c)) := by rw [Finset.sum_mul]
              _ = a * (I.sum h) * (c * c) := by ring
  have hfactor :
      (∑ j : Fin w,
        paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
          (Sum.inr i) j *
          (B₀ (Sum.inr i) j / paperA12FullGramDiag B₀ (Sum.inr i))) =
      (∑ j : Fin w,
        paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
          (Sum.inr i) j * B₀ (Sum.inr i) j) /
          paperA12FullGramDiag B₀ (Sum.inr i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∑ j : Fin w,
    paperA12FullPhysicalMatrix μ well γ₁ R assignment β normalization volume t
      (Sum.inr i) j *
      (B₀ (Sum.inr i) j / paperA12FullGramDiag B₀ (Sum.inr i))) =
    (β₀ / β) * ((I.sum h) / (I.card : ℝ)) / normalization
  rw [hfactor, hnumerator, hgram]
  dsimp only [a]
  field_simp [hI, hc, hnorm, hβ] <;> ring

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_row
#print axioms ReservoirSeismicityControl.Paper2026.paper_A11_full_physical_SR_gain_arithmetic_mean
