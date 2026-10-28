import ReservoirSeismicityControl.SeismicityPhysicalL2RateBridge
import ReservoirSeismicityControl.PressureNeumannL2TensorMultiplier
import Mathlib.Tactic

/-!
# Appendix A.2 — physical SR pressure multiplier on L²

This module builds the ACTUAL L² multiplication operator by
`γ₁(x) R(x,t)` from measurable coefficients and the physical SR box.
It replaces the abstract operator-norm hypothesis `hKpressure` in the
existing `sr_rate_L2_from_pressure_ae` bridge.

The a.e. strong-L² SR evolution and local spatial H² estimates are
separate obligations. This module does not postulate them or claim to
finish Appendix A.2. No assumption on Qdot occurs.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The scalar bounded linear map represented by SR pressure sensitivity. -/
noncomputable def srPhysicalPointwiseCLM
    {X : Type*} (γ₁ : X → ℝ) (R : ℝ → X → ℝ) (t : ℝ)
    (x : X) : ℝ →L[ℝ] ℝ :=
  (γ₁ x * R t x) • ContinuousLinearMap.id ℝ ℝ

/-- The true physical multiplier exists on L² and has exactly the
bound following from the uniform physical bounds on γ₁ and R. -/
theorem sr_physical_L2_multiplier_exists
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (t γmax Rmax : ℝ)
    (hγmeas : Measurable γ₁)
    (hRmeas : Measurable (R t))
    (hγmax : 0 ≤ γmax) (hRmax : 0 ≤ Rmax)
    (hγ : ∀ᵐ x ∂μ, |γ₁ x| ≤ γmax)
    (hR : ∀ᵐ x ∂μ, 0 ≤ R t x ∧ R t x ≤ Rmax) :
    ∃ K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ‖K‖ ≤ γmax * Rmax ∧
      ∀ f : Lp ℝ 2 μ,
        (K f : X → ℝ) =ᵐ[μ]
          fun x => (γ₁ x * R t x) * f x := by
  let C : X → ℝ →L[ℝ] ℝ := srPhysicalPointwiseCLM γ₁ R t
  have hC : AEStronglyMeasurable C μ := by
    have hM : Measurable C := by
      dsimp [C, srPhysicalPointwiseCLM]
      exact (hγmeas.mul hRmeas).smul measurable_const
    exact hM.aestronglyMeasurable
  have hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ γmax * Rmax := by
    filter_upwards [hγ, hR] with x hx hr
    have hPt : |γ₁ x * R t x| ≤ γmax * Rmax :=
      sr_pressure_multiplier_pointwise_bound
        (γ₁ x) (R t x) γmax Rmax hx hr.1 hr.2
    simpa [C, srPhysicalPointwiseCLM, norm_smul, Real.norm_eq_abs]
      using hPt
  have hnonneg : 0 ≤ γmax * Rmax := mul_nonneg hγmax hRmax
  let K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    pressureNeumannL2Multiplier μ C hC (γmax * Rmax) hnonneg hBound
  refine ⟨K, ?_, ?_⟩
  · exact pressure_neumann_l2_multiplier_norm_le
      μ C hC (γmax * Rmax) hnonneg hBound
  · intro f
    have hPointwise := pressure_neumann_l2_multiplier_apply_ae
      μ C hC (γmax * Rmax) hnonneg hBound f
    filter_upwards [hPointwise] with x hx
    change (K f : X → ℝ) x = C x (f x) at hx
    simpa [C, srPhysicalPointwiseCLM, smul_eq_mul] using hx

#print axioms ReservoirSeismicityControl.sr_physical_L2_multiplier_exists

end ReservoirSeismicityControl
