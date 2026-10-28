import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8Geometry
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (A8): actual smooth SR lag-kernel L¹ estimate

The preceding verified P3 bridge transfers the off-diagonal Neumann-orbit
bounds to the *actual* smooth-complement SR weight `(1 - ζ)w(t)`.
Here we discharge the missing L¹ step of (A8), using Mathlib's standard
integrability comparison rather than reproving semigroup theory.

External applicability inputs, NOT established here:
* the positive-lag projected-orbit estimates for the physical Neumann
  generator and source profiles (Davies–Gaffney / analytic semigroup);
* an integrable positive-lag envelope `B₁ j` (the cited short-time and long-time
  semigroup estimates give such an envelope);
* a.e. strong measurability of the physical kernel's lag derivative
  (analytic-semigroup regularity).

No Qdot, no semigroup reproof. The K(0)=0 limit, the identification of
published semigroup bounds with the specific physical operator, the near
SR weak derivative, and the causal observation identity (A9) are OPEN.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Quantitative L¹ estimate for the actual SR far-kernel lag derivative,
not merely for an abstract weight. The integrated orbit envelope and
measurability are explicit cited-semigroup applicability obligations.
The well-support separation is established by the previous A8 theorem. -/
theorem paper_sr_smooth_far_A8_lag_rate_integrable
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1)
    (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j s)‖ ≤ B₁ j s)
    (hB₁Integrable : ∀ j : Fin n,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hLagRateMeasurable : ∀ (t : ℝ) (j : Fin n),
      AEStronglyMeasurable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j s)
        (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ∀ (t : ℝ) (j : Fin n),
      let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
        ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
      Integrable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j s)
        (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∫ s in Set.Ioi (0 : ℝ),
        |ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j s|) ≤
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s) := by
  have hAll := paper_sr_smooth_far_A8_from_all_well_cutoff
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  have hMR : 0 ≤ MR := (norm_nonneg (R 0)).trans (hR 0)
  have hbase : 0 ≤ |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hCγ hMR)
  have hLw : 0 ≤ Lw := add_nonneg hbase
    (mul_nonneg (norm_nonneg cutoff) hbase)
  intro t j
  change Integrable
      (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t j s)
      (volume.restrict (Set.Ioi (0 : ℝ))) ∧
    (∫ s in Set.Ioi (0 : ℝ),
        |ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j s|) ≤
      Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)
  let rate : ℝ → ℝ := fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
    (paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff) second t j s
  let μpos : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hBound (s : ℝ) (hs : 0 < s) : |rate s| ≤ Lw * B₁ j s := by
    have hb := (hAll.2 t j s hs).2
    change |rate s| ≤ Lw * B₁ j s at hb
    exact hb
  have hBoundAe : ∀ᵐ s ∂μpos, |rate s| ≤ Lw * B₁ j s := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi)] with s hs
    exact hBound s hs
  have hScaled : Integrable (fun s => Lw * B₁ j s) μpos :=
    (hB₁Integrable j).const_mul Lw
  have hInt : Integrable rate μpos := by
    apply hScaled.mono' (hLagRateMeasurable t j)
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi)] with s hs
    have hb := hBound s hs
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hLw,
      abs_of_nonneg (hB₁ j s hs)] using hb
  have hAbsInt : Integrable (fun s => |rate s|) μpos := by
    simpa only [Real.norm_eq_abs] using hInt.norm
  have hIntegralBound :
      (∫ s, |rate s| ∂μpos) ≤ (∫ s, Lw * B₁ j s ∂μpos) :=
    integral_mono_ae hAbsInt hScaled hBoundAe
  constructor
  · exact hInt
  · change (∫ s, |rate s| ∂μpos) ≤ Lw * (∫ s, B₁ j s ∂μpos)
    simpa only [integral_const_mul] using hIntegralBound

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_lag_rate_integrable
