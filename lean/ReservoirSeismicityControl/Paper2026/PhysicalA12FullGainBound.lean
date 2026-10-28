import ReservoirSeismicityControl.Paper2026.PhysicalA11RegionalMean
import ReservoirSeismicityControl.Paper2026.PhysicalA12Normalization
import ReservoirSeismicityControl.PaperDemandBlockGainBridge
import ReservoirSeismicityControl.PaperPhysicalWellAverages
import Mathlib.Tactic

/-!
# P4: full physical A12 operator-norm bound

This closes the finite-dimensional part of (A12) for the *actual* signed-SR
well-integral matrix. It combines the locally verified A11 arithmetic mean,
the zero pressure/SR off-diagonal entries, the pressure ratio, the interval
bounds obtained from Assumptions 3 and A.2, and the existing Euclidean
squared-action-to-operator-norm bridge. No free gain contraction assumption
or new PDE result is introduced. This does not establish (A14), the
moving-SR weak derivative, or near/far analytic applicability.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- The uniform pointwise well-sensitivity bounds pass to the exact finite
arithmetic mean `H_i` from (A11). The denominator is nonzero by A4 coverage. -/
theorem paper_A12_regional_mean_interval
    {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (h : Fin w → ℝ) (lo hi : ℝ)
    (hwell : ∀ j, lo ≤ h j ∧ h j ≤ hi)
    (i : Fin r) :
    let I := Finset.univ.filter (fun j : Fin w =>
      assignment j = some (Sum.inr i))
    lo ≤ I.sum h / (I.card : ℝ) ∧
      I.sum h / (I.card : ℝ) ≤ hi := by
  classical
  dsimp only
  let I : Finset (Fin w) := Finset.univ.filter
    (fun j => assignment j = some (Sum.inr i))
  have hcard : 0 < (I.card : ℝ) := by
    have hcardNat : 0 < I.card := Finset.card_pos.mpr (by
      obtain ⟨j, hj⟩ := hcovered (Sum.inr i)
      exact ⟨j, by simp [I, hj]⟩)
    exact_mod_cast hcardNat
  have hloSum : (I.card : ℝ) * lo ≤ I.sum h := by
    have hh : I.sum (fun _ : Fin w => lo) ≤ I.sum h := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hwell j).1
    simpa [nsmul_eq_mul] using hh
  have hhiSum : I.sum h ≤ (I.card : ℝ) * hi := by
    have hh : I.sum h ≤ I.sum (fun _ : Fin w => hi) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hwell j).2
    simpa [nsmul_eq_mul] using hh
  constructor
  · exact (le_div_iff₀ hcard).2 (by simpa [mul_comm] using hloSum)
  · exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hhiSum)

/-- For a diagonal *Sum-indexed* physical gain, a uniform bound on every
scalar diagonal error is exactly an induced Euclidean operator-norm bound.
This is an application of the previously verified Sum-space norm bridge. -/
theorem paper_A12_full_diagonal_to_opNorm
    {u r : ℕ}
    (A : Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hoff : ∀ i k, i ≠ k → A i k = 0)
    (hdiag : ∀ i, |A i i - 1| ≤ δ) :
    ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
       EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
       Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r)) A‖ ≤ δ := by
  classical
  apply ReservoirSeismicityControl.paper_sum_matrix_squared_action_to_opNorm A δ hδ
  intro x
  have haction (i : Sum (Fin u) (Fin r)) :
      (A.mulVec x) i = A i i * x i := by
    change (∑ j : Sum (Fin u) (Fin r), A i j * x j) = A i i * x i
    calc
      _ = ∑ j : Sum (Fin u) (Fin r),
          if j = i then A i i * x i else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp
            · simp only [if_neg hji]
              rw [hoff i j (Ne.symm hji), zero_mul]
      _ = A i i * x i := by simp
  have hterm (i : Sum (Fin u) (Fin r)) :
      ((A i i - 1) * x i) ^ 2 ≤ δ ^ 2 * (x i) ^ 2 := by
    have habs := (abs_le.mp (hdiag i))
    have hp : 0 ≤ δ - (A i i - 1) := by linarith [habs.2]
    have hm : 0 ≤ δ + (A i i - 1) := by linarith [habs.1]
    have hsq : (A i i - 1) ^ 2 ≤ δ ^ 2 := by
      nlinarith [mul_nonneg hp hm]
    calc
      _ = (A i i - 1) ^ 2 * (x i) ^ 2 := by ring
      _ ≤ δ ^ 2 * (x i) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  calc
    (∑ i : Sum (Fin u) (Fin r), ((A.mulVec x) i - x i) ^ 2) =
      ∑ i : Sum (Fin u) (Fin r), ((A i i - 1) * x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [haction i]
        ring
    _ ≤ ∑ i : Sum (Fin u) (Fin r), δ ^ 2 * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i
    _ = δ ^ 2 * (∑ i : Sum (Fin u) (Fin r), (x i) ^ 2) := by
        rw [Finset.mul_sum]

/-- Complete physical (A12): the entire gain `B(t) B₀⁺`, not only its SR
block, satisfies the manuscript's *sharp* uncertainty margin. The bounds
on each actual well integral are the physical A.2/A3 interval certificates,
not a postulated gain bound. -/
theorem paper_A12_full_physical_opNorm_from_well_interval
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (lo hi : ℝ) (t : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hlo : 0 < lo) (hle : lo ≤ hi)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hwell : ∀ j, lo ≤ paperPhysicalSRWellMean μ (well j) γ₁ R t ∧
      paperPhysicalSRWellMean μ (well j) γ₁ R t ≤ hi) :
    let a := β₀ / β
    let mid := (lo + hi) / 2
    let normalization := a * mid
    let B := paperA12FullPhysicalMatrix μ well γ₁ R assignment
      β normalization volume t
    let B₀ := paperA12FullNominalMatrix assignment β₀ volume
    let δB := max |a - 1| ((hi - lo) / (lo + hi))
    0 ≤ δB ∧ δB < 1 ∧
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
          (B * paperA12FullNominalRightInverse B₀)‖ ≤ δB := by
  classical
  let a := β₀ / β
  let mid := (lo + hi) / 2
  let normalization := a * mid
  let B := paperA12FullPhysicalMatrix μ well γ₁ R assignment
    β normalization volume t
  let B₀ := paperA12FullNominalMatrix assignment β₀ volume
  let A : Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ :=
    B * paperA12FullNominalRightInverse B₀
  let δB := max |a - 1| ((hi - lo) / (lo + hi))
  change 0 ≤ δB ∧ δB < 1 ∧
    ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r)) A‖ ≤ δB
  have ha : 0 < a := div_pos hβ₀ hβ
  have hmid : 0 < mid := by dsimp [mid]; linarith
  have hnorm : 0 < normalization := mul_pos ha hmid
  have hmargin := ReservoirSeismicityControl.paper_pressure_sr_constructive_margin
    β β₀ lo hi hβ hβ₀ hβupper hlo hle
  have hδ0 : 0 ≤ δB := hmargin.1
  have hδ1 : δB < 1 := hmargin.2.1
  have hoff : ∀ i k, i ≠ k → A i k = 0 := by
    intro i k hik
    exact paper_A12_full_physical_off_diagonal_zero
      μ well γ₁ R assignment β β₀ normalization volume t i k hik
  have hdiag : ∀ i, |A i i - 1| ≤ δB := by
    intro i
    cases i with
    | inl k =>
        have hp := paper_A12_full_physical_pressure_gain
          μ well γ₁ R assignment β β₀ normalization volume t
          (ne_of_gt hβ) hβ₀ hvolume hcovered k
        change |(B * paperA12FullNominalRightInverse B₀)
          (Sum.inl k) (Sum.inl k) - 1| ≤ δB
        rw [hp]
        exact le_max_left _ _
    | inr k =>
        let I : Finset (Fin w) := Finset.univ.filter
          (fun j => assignment j = some (Sum.inr k))
        let H : ℝ := I.sum (fun j =>
          paperPhysicalSRWellMean μ (well j) γ₁ R t) / (I.card : ℝ)
        have hH : lo ≤ H ∧ H ≤ hi :=
          paper_A12_regional_mean_interval assignment hcovered
            (fun j => paperPhysicalSRWellMean μ (well j) γ₁ R t)
            lo hi hwell k
        have hA11 := paper_A11_full_physical_SR_gain_arithmetic_mean
          μ well γ₁ R assignment β β₀ normalization volume t
          (ne_of_gt hβ) hβ₀ (ne_of_gt hnorm)
          hvolume hcovered k
        have hentry : A (Sum.inr k) (Sum.inr k) = H / mid := by
          calc
            A (Sum.inr k) (Sum.inr k) = a * H / normalization := by
              exact hA11
            _ = H / mid := by
              dsimp only [normalization]
              field_simp [ne_of_gt ha, ne_of_gt hmid]
              <;> ring
        change |A (Sum.inr k) (Sum.inr k) - 1| ≤ δB
        rw [hentry]
        exact hmargin.2.2 H hH.1 hH.2
  exact ⟨hδ0, hδ1,
    paper_A12_full_diagonal_to_opNorm A δB hδ0 hoff hdiag⟩

/-- Discharge the well-interval inputs using the actual spatial Lebesgue
averages, Assumption 3 and the positive SR bounds of Appendix A.2. -/
theorem paper_A12_full_physical_opNorm_from_A3
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (γmin γmax Rlower Rmax : ℝ) (t : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγorder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rlower ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ j, IntegrableOn (fun x => γ₁ x * R t x) (well j) μ) :
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let normalization := (β₀ / β) * ((lo + hi) / 2)
    let B := paperA12FullPhysicalMatrix μ well γ₁ R assignment
      β normalization volume t
    let B₀ := paperA12FullNominalMatrix assignment β₀ volume
    let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
    0 ≤ δB ∧ δB < 1 ∧
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
          (B * paperA12FullNominalRightInverse B₀)‖ ≤ δB := by
  have hlo : 0 < γmin * Rlower := mul_pos hγmin hRlower
  have hhi : γmin * Rlower ≤ γmax * Rmax := by
    have hRpos : 0 ≤ Rmax := (le_of_lt hRlower).trans hRorder
    calc
      γmin * Rlower ≤ γmin * Rmax :=
        mul_le_mul_of_nonneg_left hRorder (le_of_lt hγmin)
      _ ≤ γmax * Rmax :=
        mul_le_mul_of_nonneg_right hγorder hRpos
  have hwell (j : Fin w) :
      γmin * Rlower ≤ paperPhysicalSRWellMean μ (well j) γ₁ R t ∧
      paperPhysicalSRWellMean μ (well j) γ₁ R t ≤ γmax * Rmax :=
    ReservoirSeismicityControl.paper_physical_sr_well_mean_interval μ (well j) γ₁ R
      γmin γmax Rlower Rmax t (hfinite j) (hpositive j)
      hγmin hRlower (hγ j) (hR j) (hint j)
  exact paper_A12_full_physical_opNorm_from_well_interval
    μ well γ₁ R assignment β β₀ volume
    (γmin * Rlower) (γmax * Rmax) t
    hβ hβ₀ hβupper hlo hhi hvolume hcovered hwell

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_regional_mean_interval
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_diagonal_to_opNorm
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_well_interval
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_opNorm_from_A3
