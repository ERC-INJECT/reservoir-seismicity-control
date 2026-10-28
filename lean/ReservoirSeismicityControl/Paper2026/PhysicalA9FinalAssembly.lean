import ReservoirSeismicityControl.Paper2026.PhysicalA9LagDerivativeIdentification
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ProjectedDerivative
import ReservoirSeismicityControl.Paper2026.PhysicalA9ScalarKernelIdentification
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl 2026: complete A9 moving-observation assembly

This is an APPLICATION theorem, not a new kernel construction. It uses
* the already verified smooth far-weight projection and product rule,
* the already verified scalarization of Bochner causal integrals, and
* the already verified physical kernel / A8 estimates, imported above.

The TWO differentiability inputs below describe the initial homogeneous
semigroup orbit and the projected causal *vector* convolution. They must
come from the standard analytic-semigroup and W^{1,1} convolution calculus
cited in the paper, not from assuming the final A9 scalar derivative.
Neither input asks for a derivative of the well flux Q.

IMPORTANT: compilation of this theorem DOES NOT discharge those two
external analytic applicability premises, nor prove that the actual
Neumann solution has the decomposition hPhysicalDecomposition; the preceding
PhysicalA9DGToCausal theorem supplies the latter at individual times.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped NNReal InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- A9's *complete finite-well moving scalar observation rate* from its
physical projected mild decomposition and standard positive-lag semigroup
convolution differentiation. The scalar rate has no `Qdot` term.

The vector-valued causal rate `forcingRate` is the one provided by the
standard separated-kernel convolution differentiation theorem. It is
specified by `hForcingRepresentation`, independently of differentiating
the SR observation weight. -/
theorem paper_A9_final_physical_moving_SR_far_derivative_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
    {m : ℕ} (Q : Fin m → ℝ → ℝ)
    (Ap homogeneous forcing homogeneousRate forcingRate : ℝ → Lp ℝ 2 μ)
    (lagRate : ℝ → Fin m → ℝ → Lp ℝ 2 μ)
    (hPhysicalDecomposition : ∀ τ : ℝ,
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap τ) =
        homogeneous τ + forcing τ)
    (hHomogeneousRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt homogeneous (homogeneousRate t) t)
    (hForcingRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing (forcingRate t) t)
    (hForcingRepresentation : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      forcingRate t = ∑ j : Fin m,
        ∫ s in (0 : ℝ)..t, (Q j s) • lagRate t j s)
    (hBochner : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        Integrable (fun s : ℝ => (Q j s) • lagRate t j s)
          (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hR : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t -
           cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t),
           ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
             (Ap t)⟫_ℝ +
         ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff t, homogeneousRate t⟫_ℝ +
         ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
           Q j s * ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
             gamma10 R0star cutoff t, lagRate t j s⟫_ℝ) t := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ
  have hDecomposition :
      (fun τ : ℝ => P (Ap τ)) =
        (fun τ => homogeneous τ + forcing τ) := by
    funext τ
    exact hPhysicalDecomposition τ
  have hProjectedRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt (fun τ => P (Ap τ))
        (homogeneousRate t + forcingRate t) t := by
    filter_upwards [hHomogeneousRate, hForcingRate] with t hI hC
    rw [hDecomposition]
    exact hI.add hC
  have hMoving := paper_sr_far_A9_moving_weight_from_projected_pressure_ae
    μ region hregion Kγ R Rdot gamma10 R0star cutoff
    ζ hfar hcutoff Ap (fun t => homogeneousRate t + forcingRate t)
    hR hProjectedRate
  have hPositive : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), 0 ≤ t := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), 0 ≤ t
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_of_lt ht
  filter_upwards [hMoving, hForcingRepresentation, hBochner, hPositive]
    with t hDerivative hForceEq hIntegrable ht
  -- The coercion of the nonnegative-time subtype is DEFINITIONALLY
  -- equal to the underlying real `t`.  `simpa [rfl-lemma]` does not unfold
  -- subtype coercions in this elaboration context; `change` does.
  have hScalar := paper_A9_physical_causal_scalar_kernel
    μ m (⟨t, ht⟩ : NNReal) (w t) (homogeneousRate t)
    Q (lagRate t) (by
      intro j
      change Integrable (fun s : ℝ => Q j s • lagRate t j s)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t))
      exact hIntegrable j)
  have hInnerRate :
      ⟪w t, homogeneousRate t + forcingRate t⟫_ℝ =
        ⟪w t, homogeneousRate t⟫_ℝ +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          Q j s * ⟪w t, lagRate t j s⟫_ℝ := by
    rw [hForceEq]
    exact hScalar
  change HasDerivAt
    (fun τ => ⟪w τ, Ap τ⟫_ℝ)
    (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
        gamma10 R0star t -
      cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
        gamma10 R0star t), P (Ap t)⟫_ℝ +
     ⟪w t, homogeneousRate t + forcingRate t⟫_ℝ) t at hDerivative
  rw [hInnerRate] at hDerivative
  simpa only [add_assoc] using hDerivative

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_final_physical_moving_SR_far_derivative_ae
