import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteHorizonKernelMatch20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteFarToA10_20261025
import Mathlib.Tactic

/-!
# Appendix A.3: finite-horizon pressure FAR observation derivative

This is the first direct regional observation application of the passing
canonical 3D A5 -> analytic DG -> physical W11 Neumann-kernel value theorem.
It does NOT accept a scalar pressure-far A9 derivative or scalar far-rate bound.
It proves both by differentiating the homogeneous and causal vector pieces
(whose derivatives are already available from the semigroup and W11 results),
using the actual physical pressure far weight in A10.

The projection-fixed geometric property of the far pressure weight and the
vector-rate bounds are explicit applicability inputs, not A9 conclusions.
The conclusion is local to 0<t<T: the finite A5 horizon is not extended
silently to all positive times. In particular no assumption on Qdot is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- Physical finite-horizon pressure far rate from A5 and the already
verified strictly-positive-lag kernel identification. This eliminates both
scalar hypotheses `hPressureA9` and `hPressureA8Bound` of the finite A10
bridge, once the PREVIOUSLY proved vector semigroup and W11 derivative
certificates are applied to `homogeneous` and `forcing`.

`hHomRate` and `hForcingRate` concern the two independent vector terms,
not a derivative of the pressure observation or of the full pressure path.
-/
theorem paper_A9_actual_pressure_far_rate_on_finite_horizon
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (region : Set X) (hregion : MeasurableSet region)
    (hFin : μ region ≠ ⊤)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
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
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i lag)) =
        -(Tfar lag (f i)))
    (Ap : ℝ → Lp ℝ 2 μ)
    (hA5Causal : ∀ t : NNReal, t ≤ T →
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar (Ap (t : ℝ)) =
        -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S t (S.generator p₀)) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (Q i s) • Tfar ((t : ℝ) - s) (f i)))
    (hWeightFar :
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (paperA10PressureFarWeight μ region hregion hFin cutoff) =
        paperA10PressureFarWeight μ region hregion hFin cutoff)
    (hRate fRate : ℝ → Lp ℝ 2 μ)
    (hHomDerivative : ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ =>
          if hτ : 0 ≤ τ then
            -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar
              (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀)))
          else 0)
        (hRate t) t)
    (hForcingDerivative : ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => ∑ i : Fin m,
          ∫ s in (0 : ℝ)..τ, (Q i s) •
            ReservoirSeismicityControl.paperFarLpProjection μ far hfar
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i (τ - s))))
        (fRate t) t)
    (Cw Ch Cf : ℝ)
    (hWNorm : ‖paperA10PressureFarWeight μ region hregion hFin cutoff‖ ≤ Cw)
    (hHBound : ∀ t : ℝ, 0 < t → ‖hRate t‖ ≤ Ch)
    (hFBound : ∀ t : ℝ, 0 < t → ‖fRate t‖ ≤ Cf) :
    let w := paperA10PressureFarWeight μ region hregion hFin cutoff
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      HasDerivAt (fun τ : ℝ => ⟪w, Ap τ⟫_ℝ)
        (⟪w, hRate t + fRate t⟫_ℝ) t ∧
      |⟪w, hRate t + fRate t⟫_ℝ| ≤ Cw * (Ch + Cf) := by
  classical
  intro w t ht
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let homogeneous : ℝ → Lp ℝ 2 μ := fun τ =>
    if hτ : 0 ≤ τ then -(P (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀)))
    else 0
  let forcing : ℝ → Lp ℝ 2 μ := fun τ =>
    ∑ i : Fin m, ∫ s in (0 : ℝ)..τ, (Q i s) • P
      (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i (τ - s)))
  have hValue := paper_A9_finite_horizon_causal_value_in_canonical_W11_orbit
    μ far hfar V E hsep S T p₀ m f Q Tfar orbit hPhysicalKernel Ap hA5Causal
  have hLocal : (fun τ : ℝ => ⟪w, Ap τ⟫_ℝ) =ᶠ[𝓝 t]
      (fun τ : ℝ => ⟪w, homogeneous τ + forcing τ⟫_ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have hτT : (⟨τ, hτ.1.le⟩ : NNReal) ≤ T := by
      exact_mod_cast hτ.2.le
    have hAt := hValue (⟨τ, hτ.1.le⟩ : NNReal) hτT
    have hPair := ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint μ far hfar)
      w (Ap τ) hWeightFar
    change P (Ap τ) =
        -(P (S (⟨τ, hτ.1.le⟩ : NNReal) (S.generator p₀))) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..τ, (Q i s) • P
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i (τ - s))) at hAt
    have hVec : P (Ap τ) = homogeneous τ + forcing τ := by
      simpa only [homogeneous, forcing, dif_pos hτ.1.le] using hAt
    exact hPair.trans
      (congrArg (fun x : Lp ℝ 2 μ => ⟪w, x⟫_ℝ) hVec)
  have hH : HasDerivAt homogeneous (hRate t) t :=
    hHomDerivative t ht.1
  have hF : HasDerivAt forcing (fRate t) t :=
    hForcingDerivative t ht.1
  have hSum : HasDerivAt (fun τ => homogeneous τ + forcing τ)
      (hRate t + fRate t) t := hH.add hF
  have hPairRate : HasDerivAt
      (fun τ => ⟪w, homogeneous τ + forcing τ⟫_ℝ)
      (⟪w, hRate t + fRate t⟫_ℝ) t := by
    simpa only [Function.comp_def, innerSL_apply_apply] using
      ((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hSum)
  have hScalar := hPairRate.congr_of_eventuallyEq hLocal
  have hBound : ‖hRate t + fRate t‖ ≤ Ch + Cf := by
    have htri := norm_add_le (hRate t) (fRate t)
    have hh := hHBound t ht.1
    have hf := hFBound t ht.1
    linarith
  have hCw : 0 ≤ Cw := (norm_nonneg w).trans hWNorm
  have hScalarBound : |⟪w, hRate t + fRate t⟫_ℝ| ≤ Cw * (Ch + Cf) := by
    calc
      |⟪w, hRate t + fRate t⟫_ℝ| = ‖⟪w, hRate t + fRate t⟫_ℝ‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖w‖ * ‖hRate t + fRate t‖ :=
        norm_inner_le_norm (𝕜 := ℝ) w (hRate t + fRate t)
      _ ≤ Cw * ‖hRate t + fRate t‖ :=
        mul_le_mul_of_nonneg_right hWNorm (norm_nonneg _)
      _ ≤ Cw * (Ch + Cf) :=
        mul_le_mul_of_nonneg_left hBound hCw
  exact ⟨hScalar, hScalarBound⟩

#print axioms paper_A9_actual_pressure_far_rate_on_finite_horizon

end ReservoirSeismicityControl.Paper2026
