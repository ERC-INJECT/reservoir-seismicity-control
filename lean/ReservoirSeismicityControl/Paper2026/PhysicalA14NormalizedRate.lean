import ReservoirSeismicityControl.Paper2026.PhysicalA14InverseTransport
import ReservoirSeismicityControl.Paper2026.PhysicalA14GainRate
import ReservoirSeismicityControl.PaperGainContraction
import Mathlib.Tactic

/-!
P4, Appendix A.4: the QUANTITATIVE normalized perturbation-rate estimate
for the ACTUAL physical gain (A11)--(A14).

We apply the inverse derivative identity already verified in
PhysicalA14InverseTransport and the a.e. physical gain-rate bound from A7.
The remaining assumptions on psi and its derivative are precisely the P3
regional perturbation bounds, still open for the near/far PDE applicability.
The norm inequality is a.e. in time, with no Qdot assumption.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix
open scoped Matrix.Norms.Elementwise

/-- The A14 rate inequality for the **physical** full-output gain, with its
A12 inverse bound and its physical L² well-sensitivity rate. Neither an
inverse estimate nor a gain-rate bound is an independent hypothesis.

The inputs for `psi` are precisely Appendix A.3's P3 obligations. -/
theorem paper_A14_actual_normalized_rate_bound_from_A3_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) < ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (γmin γmax Rlower Rmax Cγ CR M : ℝ)
    (hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγorder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ s j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rlower ≤ Rphysical s x ∧ Rphysical s x ≤ Rmax)
    (hint : ∀ s j, IntegrableOn
      (fun x => γ₁ x * Rphysical s x) (well j) μ)
    (hCγ : 0 ≤ Cγ) (hM : 0 ≤ M) (hK : ‖Kγ‖ ≤ Cγ)
    (hgeometry : ∀ j : Fin w,
      ((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        μ.real (well j) ≤ M)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lpsi LpsiRate : ℝ)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hpsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psiRate t‖ ≤ LpsiRate)
    (hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t) :
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let normalization := (β₀ / β) * ((lo + hi) / 2)
    let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
    let C := paperA12FullNominalRightInverse
      (paperA12FullNominalMatrix assignment β₀ volume)
    let Lgain := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (fun _ => 1)) * M * ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C
    let gain := paperA14ActualGainCLM μ well γ₁ Rphysical assignment
      β β₀ normalization volume
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖deriv (fun s => Ring.inverse (gain s) (psi s)) t‖ ≤
        (1 / (1 - δB)) * LpsiRate +
          (1 / (1 - δB)) *
            (Lgain * ((1 / (1 - δB)) * Lpsi)) := by
  classical
  let lo := γmin * Rlower
  let hi := γmax * Rmax
  let normalization := (β₀ / β) * ((lo + hi) / 2)
  let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
  let C := paperA12FullNominalRightInverse
    (paperA12FullNominalMatrix assignment β₀ volume)
  let Lgain := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
    (paperA14FullPhysicalRateMatrix assignment β normalization volume
      (fun _ => 1)) * M * ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C
  let rate : ℝ → Fin w → ℝ := fun t j =>
    wellMeanL2 μ (well j) (hs j) (ne_of_lt (hfinite j))
      (Kγ (Rdot t))
  let gain := paperA14ActualGainCLM μ well γ₁ Rphysical assignment
    β β₀ normalization volume
  let gainRate := paperA14ActualGainRateCLM assignment β β₀
    normalization volume rate
  change ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
    ‖deriv (fun s => Ring.inverse (gain s) (psi s)) t‖ ≤
      (1 / (1 - δB)) * LpsiRate +
        (1 / (1 - δB)) *
          (Lgain * ((1 / (1 - δB)) * Lpsi))

  have hA12 (s : ℝ) :
      0 ≤ δB ∧ δB < 1 ∧
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
          (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
            β normalization volume s * C)‖ ≤ δB := by
    exact paper_A12_full_physical_opNorm_from_A3
      μ well γ₁ Rphysical assignment β β₀ volume
      γmin γmax Rlower Rmax s
      hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
      hvolume hcovered hfinite hpositive hγ (hR s) (hint s)
  have hδ : δB < 1 := (hA12 0).2.1
  have hrepr (A : Matrix (Sum (Fin u) (Fin r))
      (Sum (Fin u) (Fin r)) ℝ) :
      ReservoirSeismicityControl.paperMatrixToEuclideanCLM A =
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (n := Sum (Fin u) (Fin r)) A := by
    rfl
  have hclose : ∀ s : ℝ,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) - gain s‖ ≤ δB := by
    intro s
    rw [show gain s = Matrix.toEuclideanCLM (𝕜 := ℝ)
      (n := Sum (Fin u) (Fin r))
        (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
          β normalization volume s * C) from hrepr _]
    exact (hA12 s).2.2
  have hinv (t : ℝ) (x : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) :
      ‖Ring.inverse (gain t) x‖ ≤ (1 / (1 - δB)) * ‖x‖ :=
    ReservoirSeismicityControl.paper_gain_ringInverse_action_bound_of_contraction
      gain δB hδ hclose t x

  have hwell (j : Fin w) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt (fun s => paperPhysicalSRWellMean μ (well j)
        γ₁ Rphysical s) (rate t j) t := by
    exact ReservoirSeismicityControl.paper_physical_well_hasDerivAt_from_sr_L2_ae
      μ (well j) (hs j) (ne_of_lt (hfinite j)) γ₁ Rphysical
      R Rdot Kγ (hrep j) hSRDeriv
  have hrate (j : Fin w) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |rate t j| ≤ M := by
    have hb := ReservoirSeismicityControl.paper_physical_well_mean_rate_from_sr_L2_ae
      μ (well j) (hs j) (ne_of_lt (hfinite j)) (hpositive j)
      γ₁ Rphysical R Rdot Kγ Cγ CR hCγ hK
      (hrep j) hSRDeriv hSRRate
    filter_upwards [hwell j, hb] with t hd ht
    rw [hd.deriv] at ht
    exact ht.trans (hgeometry j)
  have hcommon : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin w, |rate t j| ≤ M :=
    Filter.eventually_all.mpr hrate
  have hgainRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖gainRate t‖ ≤ Lgain := by
    filter_upwards [hcommon] with t ht
    change ‖ReservoirSeismicityControl.paperMatrixToEuclideanCLM
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (rate t) * C)‖ ≤ Lgain
    rw [ReservoirSeismicityControl.paper_matrix_toEuclideanCLM_norm]
    exact paper_A14_full_physical_rate_opNorm_bound
      assignment β normalization volume C (rate t) M hM ht

  have hformula : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      deriv (fun s => Ring.inverse (gain s) (psi s)) t =
        Ring.inverse (gain t) (psiRate t) -
          Ring.inverse (gain t) (gainRate t (Ring.inverse (gain t) (psi t))) := by
    exact paper_A14_actual_normalized_derivative_from_A3_ae
      μ well hs hfinite γ₁ Rphysical R Rdot Kγ hrep hSRDeriv
      assignment β β₀ volume γmin γmax Rlower Rmax
      hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
      hvolume hcovered hpositive hγ hR hint psi psiRate hpsiDeriv

  have hq : 0 ≤ (1 / (1 - δB)) := by
    apply div_nonneg
    · norm_num
    · linarith
  have hLgain : 0 ≤ Lgain := by
    have hfirst : 0 ≤ ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (paperA14FullPhysicalRateMatrix assignment β normalization volume
          (fun _ => 1)) := by
      rw [← ReservoirSeismicityControl.paper_matrix_toEuclideanCLM_norm]
      exact norm_nonneg _
    have hlast : 0 ≤ ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C := by
      rw [← ReservoirSeismicityControl.paper_matrix_toEuclideanCLM_norm]
      exact norm_nonneg _
    exact mul_nonneg (mul_nonneg hfirst hM) hlast
  filter_upwards [hpsi, hpsiRate, hgainRate, hformula] with t hp hpr hgr hf
  rw [hf]
  have hfirst : ‖Ring.inverse (gain t) (psiRate t)‖ ≤
      (1 / (1 - δB)) * LpsiRate := by
    calc
      _ ≤ (1 / (1 - δB)) * ‖psiRate t‖ := hinv t _
      _ ≤ (1 / (1 - δB)) * LpsiRate :=
        mul_le_mul_of_nonneg_left hpr hq
  have hsecond :
      ‖Ring.inverse (gain t) (gainRate t (Ring.inverse (gain t) (psi t)))‖ ≤
        (1 / (1 - δB)) *
          (Lgain * ((1 / (1 - δB)) * Lpsi)) := by
    calc
      _ ≤ (1 / (1 - δB)) *
        ‖gainRate t (Ring.inverse (gain t) (psi t))‖ := hinv t _
      _ ≤ (1 / (1 - δB)) *
          (Lgain * ‖Ring.inverse (gain t) (psi t)‖) := by
        apply mul_le_mul_of_nonneg_left _ hq
        calc
          ‖gainRate t (Ring.inverse (gain t) (psi t))‖ ≤
              ‖gainRate t‖ * ‖Ring.inverse (gain t) (psi t)‖ :=
            (gainRate t).le_opNorm _
          _ ≤ Lgain * ‖Ring.inverse (gain t) (psi t)‖ :=
            mul_le_mul_of_nonneg_right hgr (norm_nonneg _)
      _ ≤ (1 / (1 - δB)) *
          (Lgain * ((1 / (1 - δB)) * ‖psi t‖)) := by
        apply mul_le_mul_of_nonneg_left _ hq
        exact mul_le_mul_of_nonneg_left (hinv t _) hLgain
      _ ≤ (1 / (1 - δB)) *
          (Lgain * ((1 / (1 - δB)) * Lpsi)) := by
        apply mul_le_mul_of_nonneg_left _ hq
        apply mul_le_mul_of_nonneg_left _ hLgain
        exact mul_le_mul_of_nonneg_left hp hq
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_rate_bound_from_A3_ae
