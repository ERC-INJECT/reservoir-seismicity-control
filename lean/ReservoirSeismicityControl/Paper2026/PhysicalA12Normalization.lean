import ReservoirSeismicityControl.Paper2026.SignedPhysicalBridge
import ReservoirSeismicityControl.PaperConstructiveNominalGain
import Mathlib.Tactic

/-!
# P4 / Appendix A.4, exact A12 pressure-ratio normalization

The physical SR gain row is `(beta0 / beta) * H_i / (gamma10 * R0star)`.
Thus its midpoint choice in (A12) is

  gamma10 * R0star = (beta0 / beta) * (Hm + HM) / 2,

not simply `(Hm + HM) / 2` when `beta0 != beta`.

This module reuses the already compiled midpoint estimate but applies it to
exactly the physical row, including the pressure ratio. The old midpoint
lemma remains valid as a separate scalar statement, but is NOT the literal
A12 choice of the latest manuscript. We then identify the *physical SR well
matrix*, containing actual spatial means, with the matrix used in the
accepted multiwell inverse certificates on nonnegative physical time.

No new spatial regularity result, matrix theorem, or stability theorem is
asserted. The geometric nonzero-row rank condition must still be checked
when applying the existing inverse certificate.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- A12 with its essential factor beta0 / beta, including the exact
choice of gamma10 and the strict mismatch bound. -/
theorem paper_A12_pressure_weighted_midpoint
    (β β₀ Hm HM R0star h : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hHm : 0 < Hm) (hHmHM : Hm ≤ HM)
    (hRstar : 0 < R0star) (hhlo : Hm ≤ h) (hhhi : h ≤ HM) :
    let a := β₀ / β
    let mid := (Hm + HM) / 2
    let gamma10 := (a * mid) / R0star
    let δ := max |a - 1| ((HM - Hm) / (Hm + HM))
    0 < gamma10 ∧ gamma10 * R0star = a * mid ∧
      0 ≤ δ ∧ δ < 1 ∧
      |(a * h) / (gamma10 * R0star) - 1| ≤ δ := by
  have ha : 0 < β₀ / β := div_pos hβ₀ hβ
  have hmid : 0 < (Hm + HM) / 2 := by linarith
  have hmargin := ReservoirSeismicityControl.paper_pressure_sr_constructive_margin
    β β₀ Hm HM hβ hβ₀ hβupper hHm hHmHM
  have hchoice : ((β₀ / β * ((Hm + HM) / 2)) / R0star) * R0star =
      (β₀ / β) * ((Hm + HM) / 2) :=
    div_mul_cancel₀ _ (ne_of_gt hRstar)
  have hratio :
      ((β₀ / β) * h) /
          (((β₀ / β * ((Hm + HM) / 2)) / R0star) * R0star) =
        h / ((Hm + HM) / 2) := by
    rw [hchoice]
    field_simp [ne_of_gt ha, ne_of_gt hmid]
    <;> ring
  dsimp
  refine ⟨div_pos (mul_pos ha hmid) hRstar, hchoice,
    hmargin.1, hmargin.2.1, ?_⟩
  rw [hratio]
  exact hmargin.2.2 h hhlo hhhi

/-- Pure algebra: scaling the physical SR row by beta0/beta and scaling
its nominal sensitivity by the SAME factor cancel exactly. This is the
missing bridge between (A12) and the accepted multiwell inverse lemmas. -/
theorem paper_A12_sr_matrix_ratio_cancel
    {m w : ℕ} (B₀ : Matrix (Fin m) (Fin w) ℝ)
    (h : Fin w → ℝ) (a mid : ℝ)
    (ha : a ≠ 0) (hmid : mid ≠ 0) :
    a • ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix B₀ h (a * mid) =
      ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix B₀ h mid := by
  classical
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul,
    ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix]
  field_simp [ha, hmid]
  <;> ring

/-- Exact A12 physical SR matrix (15), with ACTUAL well integrals and
correct beta-ratio scaling, equals the matrix of the previously accepted
unconstrained multiwell inverse certificate. Restriction to t >= 0 is
required to identify the paper's physical trajectory with the legacy
nonnegative-time extension. No sensitivity bounds are assumed here. -/
theorem paper_A12_actual_SR_equals_midpoint_matrix
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ Hm HM : ℝ) (volume : Fin r → ℝ) (t : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (hHm : 0 < Hm) (hHmHM : Hm ≤ HM)
    (hvol : ∀ i, volume i ≠ 0) (ht : 0 ≤ t) :
    let a := β₀ / β
    let mid := (Hm + HM) / 2
    srPhysicalMatrix μ well γ₁ R wellRegion (a * mid) β volume t =
      ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix
        (srNominalMatrix wellRegion β₀ volume)
        (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities μ well γ₁ R t)
        mid := by
  dsimp only
  have ha : 0 < β₀ / β := div_pos hβ₀ hβ
  have hmid : 0 < (Hm + HM) / 2 := by linarith
  let B₀ := srNominalMatrix wellRegion β₀ volume
  let h : Fin w → ℝ := fun j => paperPhysicalSRWellMean μ (well j) γ₁ R t
  have hphysical := sr_physical_eq_normalized_nominal μ well γ₁ R
    wellRegion ((β₀ / β) * ((Hm + HM) / 2)) β β₀ volume t
    (mul_ne_zero (ne_of_gt ha) (ne_of_gt hmid))
    (ne_of_gt hβ) (ne_of_gt hβ₀) hvol
  have hcancel := paper_A12_sr_matrix_ratio_cancel
    B₀ h (β₀ / β) ((Hm + HM) / 2)
    (ne_of_gt ha) (ne_of_gt hmid)
  have htime : h = ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
        μ well γ₁ R t := by
    funext j
    simp [h, ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities,
      max_eq_left ht]
  calc
    srPhysicalMatrix μ well γ₁ R wellRegion
        ((β₀ / β) * ((Hm + HM) / 2)) β volume t =
      (β₀ / β) • ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix
        B₀ h ((β₀ / β) * ((Hm + HM) / 2)) := hphysical
    _ = ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix
        B₀ h ((Hm + HM) / 2) := hcancel
    _ = ReservoirSeismicityControl.paperNormalizedSRMultiwellMatrix B₀
        (ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities μ well γ₁ R t)
        ((Hm + HM) / 2) := by rw [htime]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_pressure_weighted_midpoint
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_sr_matrix_ratio_cancel
#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_actual_SR_equals_midpoint_matrix
