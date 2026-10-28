import ReservoirSeismicityControl.Paper2026.PositiveSRDiffusionWeight
import Mathlib.Tactic

/-!
# P3, Appendix A.3 — near/far splitting of the physical SR diffusion weight

The paper splits the *same* normalized observation weight from (14) into
`ζ w + (1 - ζ) w`, where `ζ` is its smooth spatial cutoff. This file
formalizes the algebraic split on physical L², its strong time derivative,
their value and rate bounds, and the diffusion-observation identity. `cutoff` denotes the
bounded L² multiplier by the paper's time-independent ζ.

The existence/identification of that multiplier, its near-field D(A)
regularity, and the external Davies–Gaffney estimates for its far-field
complement are explicitly separate applicability obligations. We do not
assume A p is time differentiable or differentiate Q, and we do not claim
that the separate near/far diffusion observations have bounded derivatives.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The manuscript's near-well part of the *actual normalized* SR weight.
`cutoff` represents fixed spatial multiplication by the smooth ζ. -/
noncomputable def paperSRNearDiffusionWeight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (t : ℝ) :
    Lp ℝ 2 μ :=
  cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)

/-- The far part is `(1 - ζ) w`. No characteristic-function cutoff is
substituted for the smooth ζ used in Appendix A.3. -/
noncomputable def paperSRFarDiffusionWeight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (t : ℝ) :
    Lp ℝ 2 μ :=
  paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t -
    paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t

/-- Exact A.3 split for the normalized physical signed-SR weight. -/
theorem paper_sr_diffusion_near_far_split
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (t : ℝ) :
    paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t +
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t =
    paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t := by
  -- Expose both occurrences of the *same* near weight before additive cancellation.
  -- Unfolding only once leaves an opaque `paperSRNearDiffusionWeight` in the goal.
  change
    cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t) +
      (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t -
        cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)) =
      paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t
  abel

/-- Both pieces inherit the strong derivative of the *same* actual SR
trajectory. This does not assert a time derivative of the pressure operator. -/
theorem paper_sr_diffusion_near_far_hasDerivAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (t : ℝ)
    (hR : HasDerivAt R (Rdot t) t) :
    HasDerivAt
      (paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff)
      (cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)) t ∧
    HasDerivAt
      (paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff)
      (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)) t := by
  have hw := paper_sr_diffusion_weight_hasDerivAt
    μ region hregion Kγ R Rdot gamma10 R0star t hR
  have hn : HasDerivAt
      (fun τ => cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star τ))
      (cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)) t :=
    cutoff.hasFDerivAt.comp_hasDerivAt t hw
  constructor
  · exact hn
  · change HasDerivAt
      (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star -
        (fun τ => cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star τ)))
      (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)) t
    exact hw.sub hn

/-- Quantitative near/far weight bounds derived from the verified A.3
normalized-weight estimate. No additional bound on a cutoff derivative is
needed, since ζ is fixed in time. -/
theorem paper_sr_diffusion_near_far_norm_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)
    (∀ t, ‖paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t‖ ≤
      ‖cutoff‖ * Lw) ∧
    (∀ t, ‖paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t‖ ≤
      Lw + ‖cutoff‖ * Lw) := by
  have hcert := paper_sr_diffusion_weight_estimates
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    hCγ hK hR hderiv hrate
  rcases hcert with ⟨hW, _hWd, _hWrate⟩
  constructor
  · intro t
    change ‖cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)‖ ≤ _
    exact (cutoff.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hW t) (norm_nonneg cutoff))
  · intro t
    change ‖paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t -
      cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)‖ ≤ _
    calc
      _ ≤ ‖paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t‖ +
        ‖cutoff (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)‖ :=
          norm_sub_le _ _
      _ ≤ |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
          ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)) := by
            apply add_le_add (hW t)
            exact (cutoff.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hW t) (norm_nonneg cutoff))

/-- Strong L² rate bounds for both pieces of the exact normalized
weight. The only time variation comes from the actual Rdot term. -/
theorem paper_sr_diffusion_near_far_rate_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR) :
    let Lwd := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)‖ ≤
        ‖cutoff‖ * Lwd) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)‖ ≤
        Lwd + ‖cutoff‖ * Lwd) := by
  have hcert := paper_sr_diffusion_weight_estimates
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    hCγ hK hR hderiv hrate
  rcases hcert with ⟨_hW, _hWd, hRate⟩
  constructor
  · filter_upwards [hRate] with t ht
    exact (cutoff.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ht (norm_nonneg cutoff))
  · filter_upwards [hRate] with t ht
    calc
      _ ≤ ‖paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t‖ +
        ‖cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)‖ :=
          norm_sub_le _ _
      _ ≤ |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR) +
          ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)) := by
            apply add_le_add ht
            exact (cutoff.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left ht (norm_nonneg cutoff))

/-- The *actual* scalar diffusion observation splits into the two terms
used in Appendix A.3, without differentiating `A p` or `Q`. -/
theorem paper_sr_diffusion_observation_split
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (diffusion : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    ⟪paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t,
      diffusion t⟫_ℝ =
    ⟪paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t,
      diffusion t⟫_ℝ +
    ⟪paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t,
      diffusion t⟫_ℝ := by
  rw [← paper_sr_diffusion_near_far_split μ region hregion Kγ R
    gamma10 R0star cutoff t]
  simp only [inner_add_left]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_split
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_norm_bounds
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_near_far_rate_bounds
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_observation_split
