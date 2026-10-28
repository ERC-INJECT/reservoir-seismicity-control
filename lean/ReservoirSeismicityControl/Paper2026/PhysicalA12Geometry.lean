import ReservoirSeismicityControl.Paper2026.PhysicalA12Inverse
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: discharge nominal SR Gram nondegeneracy from Assumption 4

The manuscript's Assumption 4 states that each seismicity output region
contains at least one well support. Equation (17) assigns the same strictly
positive nominal coefficient 1/(beta0 * |V_Ri|) to every such well.
Consequently each nominal SR Gram diagonal has a strictly positive term.

The second theorem applies this fact to the existing physical A12 inverse
certificate. It does not reprove the inverse theorem or add a physical
hypothesis: nonempty well support is precisely the geometric premise of A4.
This closes only the SR-block Gram condition, not the full pressure/SR gain.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- Assumption 4 + (17): each nominal SR row has positive Gram diagonal.
The `exists` premise is the well-coverage clause of Assumption 4. -/
theorem paper_A12_nominal_SR_gram_pos
    {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β₀ : ℝ) (volume : Fin r → ℝ)
    (hβ₀ : 0 < β₀) (hvolume : ∀ i, 0 < volume i)
    (hcovered : ∀ i : Fin r, ∃ j : Fin w, wellRegion j = some i)
    (i : Fin r) :
    0 < nominalGramDiag (srNominalMatrix wellRegion β₀ volume) i := by
  classical
  obtain ⟨j, hj⟩ := hcovered i
  have hentry : 0 < srNominalMatrix wellRegion β₀ volume i j := by
    simp only [srNominalMatrix, if_pos hj]
    exact div_pos (by norm_num : (0 : ℝ) < 1)
      (mul_pos hβ₀ (hvolume i))
  have hsingle :
      srNominalMatrix wellRegion β₀ volume i j *
          srNominalMatrix wellRegion β₀ volume i j ≤
        nominalGramDiag (srNominalMatrix wellRegion β₀ volume) i := by
    change srNominalMatrix wellRegion β₀ volume i j *
        srNominalMatrix wellRegion β₀ volume i j ≤
      ∑ k : Fin w,
        srNominalMatrix wellRegion β₀ volume i k *
          srNominalMatrix wellRegion β₀ volume i k
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin w)))
      (f := fun k : Fin w =>
        srNominalMatrix wellRegion β₀ volume i k *
          srNominalMatrix wellRegion β₀ volume i k)
      (by intro k hk; exact mul_self_nonneg _)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos hentry hentry) hsingle

/-- A12 physical SR inverse and quantitative inverse bound, directly from
Assumption 4's well coverage rather than an independent Gram hypothesis.
The spatial-integral and SR bounds are unchanged from the accepted theorem. -/
theorem paper_A12_physical_SR_inverse_from_A4
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : MeasureTheory.Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmax Rlower : ℝ) (Rmin : Fin w → ℝ)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγOrder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hRmin : ∀ j, Rlower ≤ Rmin j)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ τ, 0 ≤ τ → ∀ j,
      ∀ᵐ x ∂(μ.restrict (well j)),
        Rmin j ≤ R τ x ∧ R τ x ≤ Rmax)
    (hint : ∀ τ, 0 ≤ τ → ∀ j,
      MeasureTheory.IntegrableOn (fun x => γ₁ x * R τ x) (well j) μ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (hvolume : ∀ i, 0 < volume i)
    (hcovered : ∀ i : Fin r, ∃ j : Fin w, wellRegion j = some i)
    (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin r)) :
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let mid := (lo + hi) / 2
    let normalization := (β₀ / β) * mid
    let B := srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t
    let G := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin r)
      (paperWellGainMatrix B (srNominalMatrix wellRegion β₀ volume))
    let δSR := (hi - lo) / (lo + hi)
    δSR < 1 ∧ IsUnit G ∧
      ‖Ring.inverse G x‖ ≤ (1 / (1 - δSR)) * ‖x‖ := by
  have hgram :
      ∀ i, nominalGramDiag (srNominalMatrix wellRegion β₀ volume) i ≠ 0 := by
    intro i
    exact ne_of_gt
      (paper_A12_nominal_SR_gram_pos wellRegion β₀ volume
        hβ₀ hvolume hcovered i)
  exact paper_A12_physical_SR_inverse_certificate
    μ well γ₁ R γmin γmax Rmax Rlower Rmin
    hγmin hRlower hγOrder hRorder hRmin hfinite hpositive hγ hR hint
    wellRegion β β₀ volume hβ hβ₀ hvolume hgram t ht x

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_nominal_SR_gram_pos
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_from_A4
