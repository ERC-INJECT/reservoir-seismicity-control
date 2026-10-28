import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8ZeroLimit
import ReservoirSeismicityControl.PaperFarCausalConvolutionBridge
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (A9): physical SR causal bound using (A8)

This transports the *proved physical* positive-lag bound in (A8) to the
value term of the causal estimate (A9), at the actual observation lag `t`.
The kernel is the smooth far weight `(1-ζ)w(t)` paired with the physical
weak Neumann orbit. There is no abstract hypothesis bounding `K(t)`.

The time-reversed L¹ integrability and mass bounds on `K'(t-s)` remain
explicit obligations: they must be obtained from the verified (A8) positive-
lag L¹ estimate by the usual finite-interval reflection/change of variables.
The physical observation derivative identity (A9) is NOT asserted here.
No time derivative of the well inputs Q is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Insert the actual (A8) smooth SR-kernel amplitude certificate in the
causal (A9) estimate. The two remaining `hk` premises are the time-reversed
integrability / mass statements; no independent kernel amplitude assumption
is required. -/
theorem paper_sr_smooth_far_A9_causal_bound_from_A8_value
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
    (C₀ : Fin n → ℝ)
    (hB₀Bound : ∀ j : Fin n, ∀ s : ℝ, 0 < s → B₀ j s ≤ C₀ j)
    (t initial : ℝ) (ht : 0 < t)
    (Q : Fin n → ℝ → ℝ) (M K₁ : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hk : ∀ j : Fin n,
      Integrable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hkMass : ∀ j : Fin n,
      (∫ s in Set.Ioc (0 : ℝ) t,
        |ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second t j (t - s)|) ≤ K₁ j) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
      ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
    |ReservoirSeismicityControl.paperFarCausalKernelRate t initial
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| ≤
      |initial| + ∑ j : Fin n, M j * (Lw * C₀ j + K₁ j) := by
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  have hMR : 0 ≤ MR := (norm_nonneg (R 0)).trans (hR 0)
  have hbase : 0 ≤ |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hCγ hMR)
  have hLw : 0 ≤ Lw := add_nonneg hbase
    (mul_nonneg (norm_nonneg cutoff) hbase)
  have hC₀ (j : Fin n) : 0 ≤ C₀ j := by
    exact (hB₀ j 1 (by norm_num)).trans (hB₀Bound j 1 (by norm_num))
  have hK₀ (j : Fin n) : 0 ≤ Lw * C₀ j :=
    mul_nonneg hLw (hC₀ j)
  have hKNow (j : Fin n) :
      |paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
        cutoff V E hsep orbit t j t| ≤ Lw * C₀ j := by
    have hb := paper_sr_smooth_far_A8_value_uniform
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
      cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
      V E hsep well dsep hnear orbit second B₀ B₁
      hB₀ hB₁ hProjectedOrbit hProjectedSecond C₀ hB₀Bound
      t j t ht
    exact hb
  change |ReservoirSeismicityControl.paperFarCausalKernelRate t initial
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| ≤
      |initial| + ∑ j : Fin n, M j * (Lw * C₀ j + K₁ j)
  exact ReservoirSeismicityControl.paper_far_causal_kernel_rate_bound
    t initial
    (paperSRFarSmoothKernel μ region hregion Kγ R
      gamma10 R0star cutoff V E hsep orbit t)
    (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff) second t)
    Q M (fun j => Lw * C₀ j) K₁ hM hK₀ hQ hKNow hk hkMass

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_value
