import ReservoirSeismicityControl.PaperPhysicalSRLocalizedObservationRate
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# P3 / Appendix A.3: literal normalized regional SR diffusion weight

The SR diffusion observation in (14) has the spatial weight
  chi_{V_R} * gamma_1 * R / (gamma10 * R0star * |V_R|).
The existing localized-weight theorem treats chi_{V_R} * gamma_1 * R.
This module supplies exactly the paper's fixed volume/nominal scaling,
its strong L² time derivative and its value/rate estimates.

The SR weight does NOT carry an extra factor s: the signed tracking-error
normalization has already canceled s in the diffusion coefficient.

Only the physical L² differentiability, multiplier norm, and R/Rdot bounds
are inputs. These are A.2/A.3 applicability conditions, not additional PDE
results. Domain membership of the near weight and Davies–Gaffney estimates
for the far kernel remain explicitly open.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- Normalized signed-model SR diffusion observation weight in (14)/(A.3).
The weight has *positive* normalization, independent of the SR sign. -/
noncomputable def paperSRDiffusionWeight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ) (t : ℝ) : Lp ℝ 2 μ :=
  (1 / (gamma10 * R0star * μ.real region) : ℝ) •
    ReservoirSeismicityControl.paperPhysicalSRLocalizedWeight μ region hregion Kγ R t

/-- The time derivative uses Rdot, never a derivative of well flux Q. -/
noncomputable def paperSRDiffusionWeightRate
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ) (t : ℝ) : Lp ℝ 2 μ :=
  (1 / (gamma10 * R0star * μ.real region) : ℝ) •
    ReservoirSeismicityControl.paperPhysicalSRLocalizedWeightRate μ region hregion Kγ Rdot t

/-- Its L² representative is literally the regional weight in Appendix A.3.
In particular, the fixed normalizer contains no residual sign `s`. -/
theorem paper_sr_diffusion_weight_representative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ)
    (hrep : ∀ τ, ∀ᵐ x ∂μ,
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (gamma10 R0star t : ℝ) :
    ∀ᵐ x ∂μ,
      ((paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t) x : ℝ) =
        region.indicator (fun y =>
          (γ₁ y * Rphysical t y) / (gamma10 * R0star * μ.real region)) x := by
  let c : ℝ := 1 / (gamma10 * R0star * μ.real region)
  have hlocal := ReservoirSeismicityControl.paper_physical_sr_localized_weight_representative
    μ region hregion γ₁ Rphysical Kγ R hrep t
  filter_upwards [hlocal,
      Lp.coeFn_smul c
        (ReservoirSeismicityControl.paperPhysicalSRLocalizedWeight μ region hregion Kγ R t)]
    with x hw hc
  change ((c • ReservoirSeismicityControl.paperPhysicalSRLocalizedWeight μ region hregion Kγ R t) x : ℝ) =
    region.indicator (fun y =>
      (γ₁ y * Rphysical t y) / (gamma10 * R0star * μ.real region)) x
  -- First use the L² coercion equality, then evaluate the function smul pointwise.
  rw [hc]
  simp only [Pi.smul_apply]
  rw [hw]
  by_cases hx : x ∈ region
  · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    dsimp [c]
    ring
  · simp only [Set.indicator_of_notMem hx, smul_zero]

/-- The exact strong L² derivative of the manuscript's normalized weight. -/
theorem paper_sr_diffusion_weight_hasDerivAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star t : ℝ)
    (hR : HasDerivAt R (Rdot t) t) :
    HasDerivAt
      (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star)
      (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)
      t := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ region hregion
  have hw : HasDerivAt
      (ReservoirSeismicityControl.paperPhysicalSRLocalizedWeight μ region hregion Kγ R)
      (ReservoirSeismicityControl.paperPhysicalSRLocalizedWeightRate μ region hregion Kγ Rdot t)
      t := by
    change HasDerivAt (fun τ => (P.comp Kγ) (R τ))
      ((P.comp Kγ) (Rdot t)) t
    exact (P.comp Kγ).hasFDerivAt.comp_hasDerivAt t hR
  exact hw.fun_const_smul (1 / (gamma10 * R0star * μ.real region) : ℝ)

/-- Value and rate bounds for the exact normalized SR weight from the
already proved physical localized-weight estimates. -/
theorem paper_sr_diffusion_weight_estimates
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR) :
    (∀ t, ‖paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t‖ ≤
      |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star)
        (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)
        t) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t‖ ≤
        |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)) := by
  have hcert := ReservoirSeismicityControl.paper_physical_sr_localized_observation_certificates
    μ region hregion Kγ R Rdot Cγ CR MR hCγ hK hR hderiv hrate
  -- All three bounds have already been proved for the unnormalized weight.
  -- Scalar normalization is fixed in time, so it commutes with the derivative.
  dsimp only at hcert
  rcases hcert with ⟨_hlocal, hwdot, hRateBound, hValueBound, _hpair⟩
  constructor
  · intro t
    change ‖(1 / (gamma10 * R0star * μ.real region) : ℝ) •
      ReservoirSeismicityControl.paperPhysicalSRLocalizedWeight μ region hregion Kγ R t‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hValueBound t) (abs_nonneg _)
  constructor
  · filter_upwards [hderiv] with t hRt
    exact paper_sr_diffusion_weight_hasDerivAt
      μ region hregion Kγ R Rdot gamma10 R0star t hRt
  · filter_upwards [hRateBound] with t ht
    change ‖(1 / (gamma10 * R0star * μ.real region) : ℝ) •
      ReservoirSeismicityControl.paperPhysicalSRLocalizedWeightRate μ region hregion Kγ Rdot t‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_representative
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_diffusion_weight_estimates
