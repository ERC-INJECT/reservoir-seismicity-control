import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ObservationRate
import Mathlib.Tactic

/-!
# P3/A9 — Physical initial term and moving SR observation contribution

The `initial` in `paperFarCausalKernelRate` is not an independent free
quantity in Appendix A.3.  It is exactly the sum of
  ⟪((1 - ζ) w)_t, A p(t)⟫ + ⟪(1 - ζ) w(t), A e^{-At} p_t(0)⟫.
We derive its a.e. quantitative bound from the already compiled normalized
SR near/far value/rate estimates and the manuscript's A.3/A.5 bounds.
The second term uses the standard cited Neumann semigroup initial-data
bound, expressed only as an explicit applicability input.

This does not claim the physical far observation satisfies A9's causal
derivative formula; that PDE-to-convolution identity remains open.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The literal two noncausal terms in (A9) for the signed SR output. -/
noncomputable def paperSRFarA9PhysicalInitial
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap initialOrbit : ℝ → Lp ℝ 2 μ) (t : ℝ) : ℝ :=
  ⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
       cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t),
    Ap t⟫_ℝ +
  ⟪paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t,
    initialOrbit t⟫_ℝ

/-- A.3/A.5 bound on the *actual* initial contribution to (A9).
No independent bound on `initial` and no derivative of well rates Q. -/
theorem paper_sr_far_A9_physical_initial_bound_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
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
    (Ap initialOrbit : ℝ → Lp ℝ 2 μ) (CAp Cinit : ℝ)
    (hAp : ∀ τ, 0 ≤ τ → ‖Ap τ‖ ≤ CAp)
    (hSemigroupInitial : ∀ τ, 0 ≤ τ → ‖initialOrbit τ‖ ≤ Cinit) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)
    let Lwd := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |paperSRFarA9PhysicalInitial μ region hregion Kγ R Rdot
        gamma10 R0star cutoff Ap initialOrbit t| ≤
        (Lwd + ‖cutoff‖ * Lwd) * CAp +
        (Lw + ‖cutoff‖ * Lw) * Cinit := by
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)
  let Lwd : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)
  have hValues := paper_sr_diffusion_near_far_norm_bounds
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR cutoff
    hCγ hK hR hderiv hrate
  have hRates := paper_sr_diffusion_near_far_rate_bounds
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR cutoff
    hCγ hK hR hderiv hrate
  have hValue : ∀ t,
      ‖paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t‖ ≤
        Lw + ‖cutoff‖ * Lw := hValues.2
  have hRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)‖ ≤
          Lwd + ‖cutoff‖ * Lwd := hRates.2
  change ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
    |paperSRFarA9PhysicalInitial μ region hregion Kγ R Rdot
      gamma10 R0star cutoff Ap initialOrbit t| ≤
      (Lwd + ‖cutoff‖ * Lwd) * CAp +
      (Lw + ‖cutoff‖ * Lw) * Cinit
  have hpositive : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), 0 ≤ t := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), 0 ≤ t
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi)] with t ht
    exact le_of_lt ht
  filter_upwards [hpositive, hRate] with t ht hdot
  let v : Lp ℝ 2 μ :=
    paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t -
      cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star t)
  let z : Lp ℝ 2 μ :=
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t
  have hv : ‖v‖ ≤ Lwd + ‖cutoff‖ * Lwd := hdot
  have hz : ‖z‖ ≤ Lw + ‖cutoff‖ * Lw := hValue t
  have hfirst : |⟪v, Ap t⟫_ℝ| ≤ ‖v‖ * ‖Ap t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) v (Ap t))
  have hsecond : |⟪z, initialOrbit t⟫_ℝ| ≤ ‖z‖ * ‖initialOrbit t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) z (initialOrbit t))
  have hb1 : ‖v‖ * ‖Ap t‖ ≤ (Lwd + ‖cutoff‖ * Lwd) * CAp := by
    calc
      _ ≤ (Lwd + ‖cutoff‖ * Lwd) * ‖Ap t‖ :=
        mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hAp t ht)
        ((norm_nonneg _).trans hv)
  have hb2 : ‖z‖ * ‖initialOrbit t‖ ≤ (Lw + ‖cutoff‖ * Lw) * Cinit := by
    calc
      _ ≤ (Lw + ‖cutoff‖ * Lw) * ‖initialOrbit t‖ :=
        mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hSemigroupInitial t ht)
        ((norm_nonneg _).trans hz)
  change |⟪v, Ap t⟫_ℝ + ⟪z, initialOrbit t⟫_ℝ| ≤ _
  calc
    _ ≤ |⟪v, Ap t⟫_ℝ| + |⟪z, initialOrbit t⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖v‖ * ‖Ap t‖ + ‖z‖ * ‖initialOrbit t‖ :=
      add_le_add hfirst hsecond
    _ ≤ _ := add_le_add hb1 hb2

/-- The already verified A8→A9 a.e. certificate, but with *no*
independent A9 initial-value bound: both initial terms are the physical
moving SR weight/Neumann initial orbit and are bounded from A3/A5.
The PDE-to-causal derivative identity remains explicit and open. -/
theorem paper_sr_smooth_far_A9_observation_rate_from_physical_initial_ae
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
    (far : ℝ → ℝ)
    (Ap initialOrbit : ℝ → Lp ℝ 2 μ) (CAp Cinit : ℝ)
    (hAp : ∀ τ, 0 ≤ τ → ‖Ap τ‖ ≤ CAp)
    (hSemigroupInitial : ∀ τ, 0 ≤ τ → ‖initialOrbit τ‖ ≤ Cinit)
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
    (hFarDerivative : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt far
        (ReservoirSeismicityControl.paperFarCausalKernelRate t (paperSRFarA9PhysicalInitial μ region hregion Kγ R Rdot
          gamma10 R0star cutoff Ap initialOrbit t)
          (paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t)
          (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
            (paperSRFarDiffusionWeight μ region hregion Kγ R
              gamma10 R0star cutoff) second t) Q) t) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
      ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
    let Lwd := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)
    let Linit := (Lwd + ‖cutoff‖ * Lwd) * CAp + Lw * Cinit
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖deriv far t‖ ≤ Linit + ∑ j : Fin n,
        M j * (Lw * C₀ j +
          Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) := by
  let initial : ℝ → ℝ := fun t =>
    paperSRFarA9PhysicalInitial μ region hregion Kγ R Rdot
      gamma10 R0star cutoff Ap initialOrbit t
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  let Lwd : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)
  let Linit : ℝ := (Lwd + ‖cutoff‖ * Lwd) * CAp + Lw * Cinit
  have hinit : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), |initial t| ≤ Linit := by
    exact paper_sr_far_A9_physical_initial_bound_ae
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
      cutoff hCγ hK hR hderiv hrate Ap initialOrbit CAp Cinit
      hAp hSemigroupInitial
  change ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
    ‖deriv far t‖ ≤ Linit + ∑ j : Fin n,
      M j * (Lw * C₀ j +
        Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s))
  exact paper_sr_smooth_far_A9_observation_rate_from_A8_ae
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond C₀ hB₀Bound
    far initial Q M hM hQ hB₁Integrable hLagRateMeasurable
    Linit hinit hFarDerivative

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_physical_initial_bound_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_observation_rate_from_physical_initial_ae
