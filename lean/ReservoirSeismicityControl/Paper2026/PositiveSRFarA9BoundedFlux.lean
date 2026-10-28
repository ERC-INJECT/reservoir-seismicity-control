import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9IntegrationByParts
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9Reflection
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (A9): measurable bounded well fluxes

The smooth-input integration by parts is already verified. For a merely
bounded *measurable* well flux, the lag-derivative convolution on the right
side of (A9) must first be a legitimate Lebesgue integral. This module
proves that fact from the actual smooth-kernel A8 L¹ certificate and the
finite-interval reflection lemma. No derivative of Q is used.

This is an applicability step, NOT the missing differentiation theorem for
the mild PDE solution: continuity/approximation of the physical observation
and the weak derivative identification still need justification. In
particular we do not claim that every L∞ input has uniformly convergent
smooth approximations. No new assumptions on the manuscript's dynamics.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- An L¹ kernel can be multiplied by any bounded a.e.-measurable real
flux. Both integrability and the quantitative integral bound follow
without assuming a time derivative of that flux. -/
theorem paper_A9_L1_kernel_times_bounded_flux
    (ν : Measure ℝ) (k Q : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hk : Integrable k ν)
    (hQmeas : AEStronglyMeasurable Q ν)
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M) :
    Integrable (fun s => k s * Q s) ν ∧
    |∫ s, k s * Q s ∂ν| ≤ M * (∫ s, |k s| ∂ν) := by
  have hg : Integrable (fun s => M * |k s|) ν :=
    hk.abs.const_mul M
  have hdom : ∀ᵐ s ∂ν, ‖k s * Q s‖ ≤ M * |k s| := by
    filter_upwards [hQ] with s hs
    calc
      ‖k s * Q s‖ = |k s| * |Q s| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |k s| * M := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = M * |k s| := mul_comm _ _
  have hprod : Integrable (fun s => k s * Q s) ν := by
    apply hg.mono' (hk.aestronglyMeasurable.mul hQmeas)
    filter_upwards [hdom] with s hs
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, abs_abs]
      using hs
  constructor
  · exact hprod
  · have h := norm_integral_le_of_norm_le hg hdom
    simpa only [Real.norm_eq_abs, integral_const_mul] using h

/-- The time-reversed A9 convolution is well-defined for *bounded
measurable* inputs, not only smooth inputs. The right-hand side is
controlled by the original positive-lag A8 L¹ mass. -/
theorem paper_A9_bounded_causal_flux_from_positive_L1
    {n : ℕ} (k Q : Fin n → ℝ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (M : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hk : ∀ j : Fin n,
      Integrable (k j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hQmeas : ∀ j : Fin n,
      AEStronglyMeasurable (Q j) (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hQ : ∀ j : Fin n,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), |Q j s| ≤ M j) :
    ∀ j : Fin n,
      Integrable (fun s => k j (t - s) * Q j s)
        (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
      |∫ s in Set.Ioc (0 : ℝ) t, k j (t - s) * Q j s| ≤
        M j * (∫ s in Set.Ioi (0 : ℝ), |k j s|) := by
  intro j
  have hreflect := paper_A9_lag_reflection (k j) t ht (hk j)
  have h := paper_A9_L1_kernel_times_bounded_flux
    (volume.restrict (Set.Ioc (0 : ℝ) t))
    (fun s => k j (t - s)) (Q j) (M j)
    (hM j) hreflect.1 (hQmeas j) (hQ j)
  refine ⟨h.1, ?_⟩
  calc
    |∫ s in Set.Ioc (0 : ℝ) t, k j (t - s) * Q j s| ≤
        M j * (∫ s in Set.Ioc (0 : ℝ) t, |k j (t - s)|) := h.2
    _ = M j * (∫ s in Set.Ioc (0 : ℝ) t, |k j s|) :=
      congrArg (fun z : ℝ => M j * z) hreflect.2
    _ ≤ M j * (∫ s in Set.Ioi (0 : ℝ), |k j s|) :=
      mul_le_mul_of_nonneg_left
        (paper_A9_lag_mass_le_positive (k j) t (hk j)) (hM j)


/-- Apply the preceding bounded-flux theorem to the ACTUAL signed smooth
SR far kernel, using precisely the previously established A8 L¹ theorem.
The only additional input about fluxes is a.e. measurability and their
A1 L∞ bound; no regularity of Q in time is required. -/
theorem paper_sr_smooth_far_A9_bounded_flux_integrable_from_A8
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ τ, ‖R τ‖ ≤ MR)
    (hderiv : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot τ) τ)
    (hrate : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot τ‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
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
    (hLagRateMeasurable : ∀ (observation : ℝ) (j : Fin n),
      AEStronglyMeasurable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second observation j s)
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (t : ℝ) (ht : 0 ≤ t)
    (Q : Fin n → ℝ → ℝ) (M : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hQmeas : ∀ j : Fin n,
      AEStronglyMeasurable (Q j)
        (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hQ : ∀ j : Fin n,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), |Q j s| ≤ M j) :
    ∀ j : Fin n,
      let lag := fun s : ℝ => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t j s
      let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
        ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
      Integrable (fun s => lag (t - s) * Q j s)
        (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
      |∫ s in Set.Ioc (0 : ℝ) t, lag (t - s) * Q j s| ≤
        M j * (Lw * ∫ s in Set.Ioi (0 : ℝ), B₁ j s) := by
  intro j
  let lag : Fin n → ℝ → ℝ := fun i s =>
    ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff) second t i s
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  have hA8 (i : Fin n) :
      Integrable (lag i) (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∫ s in Set.Ioi (0 : ℝ), |lag i s|) ≤
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ i s) := by
    exact paper_sr_smooth_far_A8_lag_rate_integrable
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
      cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
      V E hsep well dsep hnear orbit second B₀ B₁
      hB₀ hB₁ hProjectedOrbit hProjectedSecond
      hB₁Integrable hLagRateMeasurable t i
  have hbounded := paper_A9_bounded_causal_flux_from_positive_L1
    lag Q t ht M hM (fun i => (hA8 i).1) hQmeas hQ j
  change Integrable (fun s => lag j (t - s) * Q j s)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
    |∫ s in Set.Ioc (0 : ℝ) t, lag j (t - s) * Q j s| ≤
      M j * (Lw * ∫ s in Set.Ioi (0 : ℝ), B₁ j s)
  refine ⟨hbounded.1, ?_⟩
  exact hbounded.2.trans
    (mul_le_mul_of_nonneg_left (hA8 j).2 (hM j))

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_L1_kernel_times_bounded_flux
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_bounded_causal_flux_from_positive_L1

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_bounded_flux_integrable_from_A8
