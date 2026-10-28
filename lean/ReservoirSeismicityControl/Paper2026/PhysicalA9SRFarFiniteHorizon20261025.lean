import ReservoirSeismicityControl.Paper2026.PhysicalA9PressureFarFiniteHorizon20261025
import ReservoirSeismicityControl.SeismicityPhysicalIntegratedAEEvolution
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.Tactic

/-!
# Physical A9 moving SR far-field derivative on a finite horizon

This discharges the two scalar SR-channel derivative/rate premises of the
finite-output A10 bridge *locally on (0,T)*.  The projected pressure
rate is derived by differentiating the previously proved canonical A5
homogeneous + W¹,¹ forcing representation.  The SR-weight derivative
is derived from the actual Bochner-integral SR evolution, rather than
postulated.  The quantitative estimate uses only bounds on the physical
vector components and weights, not a bound on the scalar observation rate.

No derivative of Q or extension to negative physical time is required.
The existing 3D Neumann/DG realization and its applicability conditions
remain external; this result is not yet a global A9/A10 theorem.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- Physical moving-SR far observation on a finite horizon.  The same
canonical A5 pressure solution and projected W¹,¹ kernel feed the moving
SR weight.  The SR rate follows from the integrated L² ODE, a.e.

`hHomDerivative` and `hForcingDerivative` are the ALREADY established
vector semigroup/convolution certificates to instantiate, not a scalar
observation derivative or its bound.  The norms `Cw,Cwd,Cp,Ch,Cf` are
physical A8-type component envelopes and can be instantiated using the
existing local weight and DG estimates. -/
theorem paper_A9_actual_SR_far_rate_on_finite_horizon
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
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ)
    (Tfar : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hPhysicalKernel : ∀ i : Fin m, ∀ lag : ℝ, 0 < lag →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i lag)) =
          -(Tfar lag (f i)))
    (Ap : ℝ → Lp ℝ 2 μ)
    (hA5Causal : ∀ t : NNReal, t ≤ T →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (Ap (t : ℝ)) =
          -(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
            (S t (S.generator p₀)) +
              ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
                (Q i s) • Tfar ((t : ℝ) - s) (f i)))
    (hRate fRate : ℝ → Lp ℝ 2 μ)
    (hHomDerivative : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      HasDerivAt
        (fun τ : ℝ =>
          if hτ : 0 ≤ τ then
            -(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
              (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀)))
          else 0)
        (hRate t) t)
    (hForcingDerivative : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      HasDerivAt
        (fun τ : ℝ => ∑ i : Fin m,
          ∫ s in (0 : ℝ)..τ, (Q i s) •
            ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i (τ - s))))
        (fRate t) t)
    (hRInt : IntervalIntegrable Rdot volume (0 : ℝ) (T : ℝ))
    (hRIntegrated : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    (Cw Cwd Cp Ch Cf : ℝ)
    (hWBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      ‖paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t‖ ≤ Cw)
    (hWdBound : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        ‖paperSRDiffusionWeightRate μ region hregion Kγ Rdot
          gamma10 R0star t -
            cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
              gamma10 R0star t)‖ ≤ Cwd)
    (hApBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (Ap t)‖ ≤ Cp)
    (hHBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      ‖hRate t‖ ≤ Ch)
    (hFBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      ‖fRate t‖ ≤ Cf) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
    let w := paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff
    let wd := fun t => paperSRDiffusionWeightRate μ region hregion Kγ Rdot
      gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
          gamma10 R0star t)
    let rate := fun t : ℝ =>
      ⟪wd t, P (Ap t)⟫_ℝ + ⟪w t, hRate t + fRate t⟫_ℝ
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt (fun τ => ⟪w τ, Ap τ⟫_ℝ) (rate t) t ∧
          |rate t| ≤ Cwd * Cp + Cw * (Ch + Cf) := by
  classical
  dsimp only
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let w := paperSRFarDiffusionWeight μ region hregion Kγ R
    gamma10 R0star cutoff
  let wd := fun t => paperSRDiffusionWeightRate μ region hregion Kγ Rdot
      gamma10 R0star t -
        cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
          gamma10 R0star t)
  let rate := fun t : ℝ =>
    ⟪wd t, P (Ap t)⟫_ℝ + ⟪w t, hRate t + fRate t⟫_ℝ
  let homogeneous : ℝ → Lp ℝ 2 μ := fun τ =>
    if hτ : 0 ≤ τ then -(P (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀)))
    else 0
  let forcing : ℝ → Lp ℝ 2 μ := fun τ =>
    ∑ i : Fin m, ∫ s in (0 : ℝ)..τ, (Q i s) • P
      (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i (τ - s)))
  have hValue := paper_A9_finite_horizon_causal_value_in_canonical_W11_orbit
    μ {x : X | ζ x ≠ 1} hfar V E hsep S T p₀ m f Q Tfar
      orbit hPhysicalKernel Ap hA5Causal
  have hLocal (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T : ℝ)) :
      (fun τ : ℝ => P (Ap τ)) =ᶠ[𝓝 t]
        (fun τ : ℝ => homogeneous τ + forcing τ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have hτT : (⟨τ, hτ.1.le⟩ : NNReal) ≤ T := by
      exact_mod_cast hτ.2.le
    have hAt := hValue (⟨τ, hτ.1.le⟩ : NNReal) hτT
    change P (Ap τ) =
        -(P (S (⟨τ, hτ.1.le⟩ : NNReal) (S.generator p₀))) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..τ, (Q i s) • P
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i (τ - s))) at hAt
    simpa only [homogeneous, forcing, dif_pos hτ.1.le] using hAt
  have hWfixed : ∀ τ : ℝ, P (w τ) = w τ := by
    intro τ
    exact paper_sr_smooth_far_projection_nonunit_set
      μ region hregion Kγ R gamma10 R0star cutoff ζ hfar hcutoff τ
  have hObs : (fun τ : ℝ => ⟪w τ, Ap τ⟫_ℝ) =
      (fun τ : ℝ => ⟪w τ, P (Ap τ)⟫_ℝ) := by
    funext τ
    exact ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
        μ {x : X | ζ x ≠ 1} hfar)
      (w τ) (Ap τ) (hWfixed τ)
  have hRAE := ReservoirSeismicityControl.sr_integrated_L2_evolution_hasDerivAt_ae
    μ T R Rdot hRInt hRIntegrated
  filter_upwards [hRAE, hWdBound] with t hRt hWd
  intro ht
  have hSR : HasDerivAt R (Rdot t) t := hRt ht
  have hProj : HasDerivAt (fun τ : ℝ => P (Ap τ))
      (hRate t + fRate t) t := by
    have hsum : HasDerivAt (fun τ : ℝ => homogeneous τ + forcing τ)
        (hRate t + fRate t) t :=
      (hHomDerivative t ht).add (hForcingDerivative t ht)
    exact hsum.congr_of_eventuallyEq (hLocal t ht)
  have hWderiv : HasDerivAt w (wd t) t :=
    (paper_sr_diffusion_near_far_hasDerivAt
      μ region hregion Kγ R Rdot gamma10 R0star cutoff t hSR).2
  have hprod : HasDerivAt
      (fun τ => ⟪w τ, Ap τ⟫_ℝ)
      (rate t) t := by
    have hpair := hWderiv.inner ℝ hProj
    change HasDerivAt (fun τ => ⟪w τ, Ap τ⟫_ℝ)
      (⟪wd t, P (Ap t)⟫_ℝ + ⟪w t, hRate t + fRate t⟫_ℝ) t
    rw [hObs]
    convert hpair using 1
    exact add_comm _ _
  have hHf : ‖hRate t + fRate t‖ ≤ Ch + Cf :=
    (norm_add_le _ _).trans
      (add_le_add (hHBound t ht) (hFBound t ht))
  have hCW : 0 ≤ Cw := (norm_nonneg (w t)).trans (hWBound t ht)
  have hCWD : 0 ≤ Cwd := (norm_nonneg (wd t)).trans (hWd ht)
  have hfirst : |⟪wd t, P (Ap t)⟫_ℝ| ≤ Cwd * Cp := by
    calc
      |⟪wd t, P (Ap t)⟫_ℝ| = ‖⟪wd t, P (Ap t)⟫_ℝ‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖wd t‖ * ‖P (Ap t)‖ :=
        norm_inner_le_norm (𝕜 := ℝ) (wd t) (P (Ap t))
      _ ≤ Cwd * ‖P (Ap t)‖ :=
        mul_le_mul_of_nonneg_right (hWd ht) (norm_nonneg _)
      _ ≤ Cwd * Cp :=
        mul_le_mul_of_nonneg_left (hApBound t ht) hCWD
  have hsecond : |⟪w t, hRate t + fRate t⟫_ℝ| ≤
      Cw * (Ch + Cf) := by
    calc
      |⟪w t, hRate t + fRate t⟫_ℝ| =
          ‖⟪w t, hRate t + fRate t⟫_ℝ‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖w t‖ * ‖hRate t + fRate t‖ :=
        norm_inner_le_norm (𝕜 := ℝ) (w t) (hRate t + fRate t)
      _ ≤ Cw * ‖hRate t + fRate t‖ :=
        mul_le_mul_of_nonneg_right (hWBound t ht) (norm_nonneg _)
      _ ≤ Cw * (Ch + Cf) :=
        mul_le_mul_of_nonneg_left hHf hCW
  have hbound : |rate t| ≤ Cwd * Cp + Cw * (Ch + Cf) := by
    change |⟪wd t, P (Ap t)⟫_ℝ + ⟪w t, hRate t + fRate t⟫_ℝ| ≤ _
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  exact ⟨hprod, hbound⟩

#print axioms paper_A9_actual_SR_far_rate_on_finite_horizon

end ReservoirSeismicityControl.Paper2026
