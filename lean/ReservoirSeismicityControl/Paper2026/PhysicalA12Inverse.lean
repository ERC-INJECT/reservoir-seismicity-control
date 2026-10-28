import ReservoirSeismicityControl.Paper2026.PhysicalA12Normalization
import ReservoirSeismicityControl.PaperPhysicalSRMultiwellInverse
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: physical SR inverse certificate for (A12)

This module transports the previously verified multiwell gain inverse
certificate to the ACTUAL well-integral SR coefficient with the correct
beta0/beta factor of (A12). The resulting inverse norm is controlled by
the paper's sharp SR margin (HM-Hm)/(HM+Hm), not by an assumed gain bound.

The well support/nonzero nominal Gram condition and spatial SR bounds are
exactly the applicability conditions of Assumptions 3--5 and A.2.
The pressure block and the final full-output inverse remain to be assembled.
No elliptic, semigroup, or super-twisting theorem is reproved here.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- The interval-form inverse margin of the existing multiwell certificate
is precisely the sharp SR part of the manuscript's margin (A12). -/
theorem paper_A12_SR_interval_margin_eq
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) :
    max |lo / ((lo + hi) / 2) - 1| |hi / ((lo + hi) / 2) - 1| =
      (hi - lo) / (lo + hi) := by
  have hsum : 0 < lo + hi := by linarith
  have hmid : 0 < (lo + hi) / 2 := by linarith
  have hlow : lo / ((lo + hi) / 2) - 1 =
      -((hi - lo) / (lo + hi)) := by
    field_simp [ne_of_gt hsum, ne_of_gt hmid]
    <;> ring
  have hupp : hi / ((lo + hi) / 2) - 1 =
      (hi - lo) / (lo + hi) := by
    field_simp [ne_of_gt hsum, ne_of_gt hmid]
    <;> ring
  have hratio : 0 ≤ (hi - lo) / (lo + hi) :=
    div_nonneg (sub_nonneg.mpr hle) (le_of_lt hsum)
  rw [hlow, hupp, abs_neg, abs_of_nonneg hratio, max_self]

/-- Physical SR part of (A12): from physical gamma1*R well means, obtain
the inverse of the actual well gain, with the paper's exact SR margin.
There is no independently assumed bound on G-I or on its inverse.

The nonzero Gram premise is the geometrical/rank condition in A4; its
instantiation from nonempty well supports is a separate P4 check.
The pressure block beta0/beta is not included in this SR-only statement. -/
theorem paper_A12_physical_SR_inverse_certificate
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
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
      IntegrableOn (fun x => γ₁ x * R τ x) (well j) μ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (hvolume : ∀ i, 0 < volume i)
    (hgram : ∀ i, nominalGramDiag (srNominalMatrix wellRegion β₀ volume) i ≠ 0)
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
  classical
  have hlo : 0 < γmin * Rlower := mul_pos hγmin hRlower
  have hhi : γmin * Rlower ≤ γmax * Rmax := by
    have hRmaxNonneg : 0 ≤ Rmax :=
      (le_of_lt hRlower).trans hRorder
    calc
      γmin * Rlower ≤ γmin * Rmax :=
        mul_le_mul_of_nonneg_left hRorder (le_of_lt hγmin)
      _ ≤ γmax * Rmax :=
        mul_le_mul_of_nonneg_right hγOrder hRmaxNonneg
  have hB₀ : ∀ i j, wellRegion j ≠ some i →
      srNominalMatrix wellRegion β₀ volume i j = 0 := by
    intro i j hj
    simp [srNominalMatrix, hj]
  have hcert := ReservoirSeismicityControl.paper_physical_sr_multiwell_integral_inverse_certificate
    μ well γ₁ R γmin γmax Rmax Rlower Rmin
    hγmin hRlower hγOrder hRorder hRmin hfinite hpositive hγ hR hint
    (srNominalMatrix wellRegion β₀ volume) wellRegion hB₀ hgram
  have hmargin := paper_A12_SR_interval_margin_eq
    (γmin * Rlower) (γmax * Rmax) hlo hhi
  have hphysical := paper_A12_actual_SR_equals_midpoint_matrix
    μ well γ₁ R wellRegion β β₀ (γmin * Rlower) (γmax * Rmax)
    volume t hβ hβ₀ hlo hhi
    (fun i => ne_of_gt (hvolume i)) ht
  dsimp only at hcert
  rcases hcert with ⟨hdelta, hinverse⟩
  have hdirect := hinverse t x
  dsimp only
  rw [hphysical]
  rw [hmargin] at hdelta hdirect
  exact ⟨hdelta, hdirect.1, hdirect.2⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_SR_interval_margin_eq
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_physical_SR_inverse_certificate
