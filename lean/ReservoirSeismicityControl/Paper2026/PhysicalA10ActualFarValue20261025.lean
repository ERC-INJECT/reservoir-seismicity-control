import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteFarToA10_20261025
import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import Mathlib.Tactic

/-!
# A.3: actual finite far-field diffusion VALUE estimate

This fills the previously missing *far-field value* estimate required for
the regional perturbation bound. It does not assume bounded far observations.
The weights are the literal pressure and SR weights from manuscript (14).

This module does not assert that the existing per-region A9 differentiation
premises are closed. No hypothesis on Qdot is added.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- A4/A7 control the actual finite far-field diffusion VALUE, with
no derivative assumptions on Ap or on the well fluxes. -/
theorem paper_A10_physical_far_value_from_A4_A7
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pregions i))
    (hpFin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrMeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ)
    (γ10 R0star Cγ MR : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, 0 ≤ t → ‖R t‖ ≤ MR)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (CAp : ℝ)
    (hAp : ∀ t, 0 ≤ t → ‖Ap t‖ ≤ CAp) :
    let Penv := fun i : Fin u =>
      (|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
        |1 / μ.real (pregions i)| *
          (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp
    let Senv := fun i : Fin r =>
      (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
        ‖cutoff‖ *
          (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * CAp
    ∀ t, 0 ≤ t →
      ‖paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
          Kγ R γ10 R0star cutoff Ap t‖ ≤
        (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Penv i) +
        (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Senv i) := by
  classical
  dsimp only
  let Penv : Fin u → ℝ := fun i =>
    (|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
      |1 / μ.real (pregions i)| *
        (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp
  let Senv : Fin r → ℝ := fun i =>
    (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
      ‖cutoff‖ *
        (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * CAp
  intro t ht
  have hpWeight (i : Fin u) :
      ‖paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ ≤
        |1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
        |1 / μ.real (pregions i)| *
          (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ))) := by
    have hind :
        ‖indicatorConstLp (2 : ENNReal) (hpMeas i) (hpFin i) (1 : ℝ)‖ =
          (μ.real (pregions i)) ^ (1 / (2 : ℝ)) := by
      simpa using (MeasureTheory.norm_indicatorConstLp
        (μ := μ) (p := (2 : ENNReal)) (hs := hpMeas i)
        (hμs := hpFin i) (c := (1 : ℝ)) (by norm_num) (by norm_num))
    change ‖(1 / μ.real (pregions i) : ℝ) •
        indicatorConstLp 2 (hpMeas i) (hpFin i) (1 : ℝ) -
        paperPressureNearWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ ≤ _
    calc
      _ ≤ ‖(1 / μ.real (pregions i) : ℝ) •
          indicatorConstLp 2 (hpMeas i) (hpFin i) (1 : ℝ)‖ +
          ‖paperPressureNearWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ :=
        norm_sub_le _ _
      _ = |1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
          ‖paperPressureNearWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ := by
        rw [norm_smul, Real.norm_eq_abs, hind]
      _ ≤ _ := add_le_add le_rfl
        (paper_pressure_near_weight_bound μ (pregions i) (hpMeas i) (hpFin i) cutoff)
  have hSRfull (i : Fin r) :
      ‖paperSRDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star t‖ ≤
        |1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) := by
    change ‖(1 / (γ10 * R0star * μ.real (rregions i)) : ℝ) •
      ReservoirSeismicityControl.paperFarLpProjection μ (rregions i) (hrMeas i) (Kγ (R t))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      ‖ReservoirSeismicityControl.paperFarLpProjection μ (rregions i) (hrMeas i) (Kγ (R t))‖ ≤
        ‖Kγ (R t)‖ :=
          ReservoirSeismicityControl.paper_far_lp_projection_norm_le μ (rregions i) (hrMeas i)
            (Kγ (R t))
      _ ≤ ‖Kγ‖ * ‖R t‖ := Kγ.le_opNorm _
      _ ≤ Cγ * ‖R t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ Cγ * MR := mul_le_mul_of_nonneg_left (hR t ht) hCγ
  have hsWeight (i : Fin r) :
      ‖paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star cutoff t‖ ≤
        |1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
          ‖cutoff‖ *
            (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR)) := by
    change ‖paperSRDiffusionWeight μ (rregions i) (hrMeas i) Kγ R γ10 R0star t -
      cutoff (paperSRDiffusionWeight μ (rregions i) (hrMeas i) Kγ R γ10 R0star t)‖ ≤ _
    calc
      _ ≤ ‖paperSRDiffusionWeight μ (rregions i) (hrMeas i) Kγ R γ10 R0star t‖ +
        ‖cutoff (paperSRDiffusionWeight μ (rregions i) (hrMeas i) Kγ R γ10 R0star t)‖ :=
          norm_sub_le _ _
      _ ≤ |1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
          ‖cutoff‖ *
            (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR)) := by
          apply add_le_add (hSRfull i)
          exact (cutoff.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hSRfull i) (norm_nonneg cutoff))
  have hpValue (i : Fin u) :
      |-⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
          Ap t⟫_ℝ| ≤ Penv i := by
    rw [abs_neg]
    have hcs := norm_inner_le_norm (𝕜 := ℝ)
      (paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff) (Ap t)
    calc
      |⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
          Ap t⟫_ℝ| ≤
        ‖paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ *
          ‖Ap t‖ := by simpa only [Real.norm_eq_abs] using hcs
      _ ≤ (|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
            |1 / μ.real (pregions i)| *
              (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * ‖Ap t‖ :=
        mul_le_mul_of_nonneg_right (hpWeight i) (norm_nonneg _)
      _ ≤ Penv i := by
        dsimp [Penv]
        apply mul_le_mul_of_nonneg_left (hAp t ht)
        positivity
  have hsValue (i : Fin r) :
      |-⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star cutoff t, Ap t⟫_ℝ| ≤ Senv i := by
    rw [abs_neg]
    have hcs := norm_inner_le_norm (𝕜 := ℝ)
      (paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        γ10 R0star cutoff t) (Ap t)
    calc
      |⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star cutoff t, Ap t⟫_ℝ| ≤
        ‖paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star cutoff t‖ * ‖Ap t‖ := by
        simpa only [Real.norm_eq_abs] using hcs
      _ ≤ (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
          ‖cutoff‖ *
            (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * ‖Ap t‖ :=
        mul_le_mul_of_nonneg_right (hsWeight i) (norm_nonneg _)
      _ ≤ Senv i := by
        dsimp [Senv]
        apply mul_le_mul_of_nonneg_left (hAp t ht)
        have hMR : 0 ≤ MR :=
          (norm_nonneg (R t)).trans (hR t ht)
        have hNonneg :
            0 ≤ |1 / (γ10 * R0star * μ.real (rregions i))| *
              (Cγ * MR) :=
          mul_nonneg (abs_nonneg _) (mul_nonneg hCγ hMR)
        exact add_nonneg hNonneg
          (mul_nonneg (norm_nonneg cutoff) hNonneg)
  change ‖(∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
      (-⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
          Ap t⟫_ℝ)) +
      (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
      (-⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
          γ10 R0star cutoff t, Ap t⟫_ℝ))‖ ≤ _
  calc
    _ ≤ (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
              Ap t⟫_ℝ)‖) +
        (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i
          (-⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
              γ10 R0star cutoff t, Ap t⟫_ℝ)‖) := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Penv i) +
          (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Senv i) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
            |-⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
                Ap t⟫_ℝ| := by
              simpa only [Real.norm_eq_abs] using
                (paperPressureCoordinateEmbed (u := u) (r := r) i).le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpValue i) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
            |-⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
                γ10 R0star cutoff t, Ap t⟫_ℝ| := by
              simpa only [Real.norm_eq_abs] using
                (paperSRCoordinateEmbed (u := u) (r := r) i).le_opNorm _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsValue i) (norm_nonneg _)



end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_physical_far_value_from_A4_A7
