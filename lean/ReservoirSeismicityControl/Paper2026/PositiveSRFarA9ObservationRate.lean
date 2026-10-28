import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9Reflection
import Mathlib.Tactic

/-!
# P3 / (A9): actual far-observation a.e. rate bound from physical A8 envelopes

This removes the *independent* kernel amplitude and causal L¹ hypotheses
from the a.e. far-observation rate estimate. Both are derived from the
verified physical smooth-complement A8 estimates and Mathlib reflection.

The physical far-observation derivative identity in (A9) is still an explicit
PDE applicability obligation, represented by `hFarDerivative`. It is NOT
presented as a published result or proved in this patch. In particular,
this theorem does not assume Qdot and does not complete P3.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Actual smooth physical far kernel: a.e. bound on the derivative of the
far observation, conditional only on the (still-open) *identification* of
that derivative with the causal A9 expression. Its kernel norms are no
longer hypotheses: they follow from the A8/Davies--Gaffney interface. -/
theorem paper_sr_smooth_far_A9_observation_rate_from_A8_ae
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
    (far initial : ℝ → ℝ)
    (Q : Fin n → ℝ → ℝ) (M : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hB₁Integrable : ∀ j : Fin n,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hLagRateMeasurable : ∀ (observation : ℝ) (j : Fin n),
      AEStronglyMeasurable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second observation j s)
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (Linit : ℝ)
    (hinit : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), |initial t| ≤ Linit)
    (hFarDerivative : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt far
        (ReservoirSeismicityControl.paperFarCausalKernelRate t (initial t)
          (paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t)
          (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
            (paperSRFarDiffusionWeight μ region hregion Kγ R
              gamma10 R0star cutoff) second t) Q) t) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
      ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖deriv far t‖ ≤ Linit + ∑ j : Fin n,
        M j * (Lw * C₀ j +
          Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) := by
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  change ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
    ‖deriv far t‖ ≤ Linit + ∑ j : Fin n,
      M j * (Lw * C₀ j +
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s))
  have hpositive : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), 0 < t := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), 0 < t
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi)] with t ht
    exact ht
  filter_upwards [hpositive, hinit, hFarDerivative] with t ht hi hd
  have hBound := paper_sr_smooth_far_A9_causal_bound_from_A8_L1
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond C₀ hB₀Bound
    t (initial t) ht Q M hM hQ hB₁Integrable hLagRateMeasurable
  change |ReservoirSeismicityControl.paperFarCausalKernelRate t (initial t)
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| ≤
      |initial t| + ∑ j : Fin n,
        M j * (Lw * C₀ j +
          Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) at hBound
  calc
    ‖deriv far t‖ = |ReservoirSeismicityControl.paperFarCausalKernelRate t (initial t)
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| := by
          rw [hd.deriv, Real.norm_eq_abs]
    _ ≤ |initial t| + ∑ j : Fin n,
      M j * (Lw * C₀ j +
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) := hBound
    _ ≤ Linit + ∑ j : Fin n,
      M j * (Lw * C₀ j +
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) :=
          add_le_add_left hi _

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_A8_ae
