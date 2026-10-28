import ReservoirSeismicityControl.Paper2026.PositiveSRNearFarSplit
import ReservoirSeismicityControl.PaperNearWeakNeumannMovingDerivative
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl A.2 → A.3: actual signed-SR moving near observation

This applies the ALREADY PASSED moving weak-Neumann product rule to the
actual localized normalized SR weight.  The A7 input is only local H² on
a well neighborhood, represented by an `H2` certificate and an L²
restriction map.  The separate cited local elliptic/cutoff theorem is
encoded as a map from the local Sobolev space into the *actual* global
weak-generator domain, with a quantitative graph bound.

In particular, neither global H² regularity of R, differentiability of
A p or A w, nor a derivative of Q is assumed.  The pressure generator
image continuity comes from the existing canonical physical A5 path;
the strong derivatives of R and p come from the existing SR and
pressure time-evolution results.

This module does not claim the Sobolev/cutoff lift itself has been
formalized: this is explicitly the manuscript-cited elliptic result.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter TopologicalSpace
open scoped InnerProductSpace Topology

set_option maxHeartbeats 2000000

/-- Actual regional SR near-field derivative from A7 local H² and the
previously verified Neumann moving-observation product rule.

`H2` is local H²(U_j), `localRestriction` is restriction of the physical
SR from L²(V) to L²(U_j), and `lift` is the smooth-cutoff/elliptic map
of the cited standard local H² calculus. `hLiftRep` is a universal
representative identity for that *fixed* map, not a premise on the
actual observation derivative or on the desired A.3 rate bound.

The theorem proves existence of the physical weak-domain weight, its
generator bound, and the exact near-field derivative whenever the
physical p and R have their established a.e. strong derivatives.
-/
theorem paper_A7_actual_H2_gives_SR_near_moving_derivative
    {X U H2 : Type*}
    [MeasurableSpace X] [MeasurableSpace U]
    [NormedAddCommGroup H2] [NormedSpace ℝ H2]
    (μ : Measure X) (μU : Measure U)
    (embedU : H2 →L[ℝ] Lp ℝ 2 μU)
    (localRestriction : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μU)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ a b : V, E a b = E b a)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (pdot : ℝ → Lp ℝ 2 μ)
    (CH2 CA : ℝ) (hCA : 0 ≤ CA)
    (hRH2 : ∀ τ : ℝ, 0 ≤ τ → ∃ y : H2,
      embedU y = localRestriction (R τ) ∧ ‖y‖ ≤ CH2)
    (lift : H2 → pressureWeakNeumannDomain V E)
    (hLiftRep : ∀ (y : H2) (r : Lp ℝ 2 μ),
      embedU y = localRestriction r →
        (((lift y : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ) =
          cutoff ((1 / (gamma10 * R0star * μ.real region) : ℝ) •
            paperFarLpProjection μ region hregion (Kγ r)))
    (hLiftBound : ∀ y : H2,
      ‖pressureWeakNeumannOperator V E hsep (lift y)‖ ≤ CA * ‖y‖) :
    ∃ w : ℝ → pressureWeakNeumannDomain V E,
      (∀ τ : ℝ, 0 < τ →
        (((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ) =
          paperSRNearDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff τ) ∧
      (∀ τ : ℝ, 0 ≤ τ →
        ‖pressureWeakNeumannOperator V E hsep (w τ)‖ ≤ CA * CH2) ∧
      (∀ t : ℝ, 0 < t →
        HasDerivAt R (Rdot t) t →
        HasDerivAt
          (fun τ : ℝ => (((p τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ))
          (pdot t) t →
        ContinuousAt
          (fun τ : ℝ => pressureWeakNeumannOperator V E hsep (p τ)) t →
        HasDerivAt
          (fun τ : ℝ =>
            ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
                gamma10 R0star cutoff τ,
              pressureWeakNeumannOperator V E hsep (p τ)⟫_ℝ)
          (⟪cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
                gamma10 R0star t),
              pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ +
            ⟪pressureWeakNeumannOperator V E hsep (w t), pdot t⟫_ℝ) t) := by
  classical
  let w : ℝ → pressureWeakNeumannDomain V E := fun τ =>
    if hτ : 0 ≤ τ then lift (Classical.choose (hRH2 τ hτ)) else 0
  have hwRep (τ : ℝ) (hτ : 0 < τ) :
      (((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ) =
        paperSRNearDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ := by
    have hτ0 : 0 ≤ τ := le_of_lt hτ
    have hy : embedU (Classical.choose (hRH2 τ hτ0)) =
        localRestriction (R τ) := (Classical.choose_spec (hRH2 τ hτ0)).1
    have hrep := hLiftRep (Classical.choose (hRH2 τ hτ0)) (R τ) hy
    change (((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ) =
      cutoff ((1 / (gamma10 * R0star * μ.real region) : ℝ) •
        paperFarLpProjection μ region hregion (Kγ (R τ)))
    simpa only [w, dif_pos hτ0] using hrep
  have hwBound (τ : ℝ) (hτ : 0 ≤ τ) :
      ‖pressureWeakNeumannOperator V E hsep (w τ)‖ ≤ CA * CH2 := by
    let y : H2 := Classical.choose (hRH2 τ hτ)
    have hy : ‖y‖ ≤ CH2 := (Classical.choose_spec (hRH2 τ hτ)).2
    have hbound := (hLiftBound y).trans
      (mul_le_mul_of_nonneg_left hy hCA)
    simpa only [w, dif_pos hτ, y] using hbound
  refine ⟨w, hwRep, hwBound, ?_⟩
  intro t ht hR hp hpGraph
  have hNearRate := (paper_sr_diffusion_near_far_hasDerivAt
    μ region hregion Kγ R Rdot gamma10 R0star cutoff t hR).1
  have hLocal :
      (fun τ : ℝ => (((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ)) =ᶠ[𝓝 t]
        (paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
    exact hwRep τ hτ
  have hwDeriv : HasDerivAt
      (fun τ : ℝ => (((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ))
      (cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
        gamma10 R0star t)) t :=
    hNearRate.congr_of_eventuallyEq hLocal
  have hMoving := paper_near_weak_neumann_moving_hasDerivAt
    V E hsep hEsym w p
    (cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
      gamma10 R0star t)) (pdot t) t hwDeriv hp hpGraph
  have hObsLocal :
      (paperNearWeakNeumannMovingObservation V E hsep w p) =ᶠ[𝓝 t]
        (fun τ : ℝ =>
          ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
              gamma10 R0star cutoff τ,
            pressureWeakNeumannOperator V E hsep (p τ)⟫_ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
    change ⟪(((w τ : pressureWeakNeumannDomain V E) : V) : Lp ℝ 2 μ),
      pressureWeakNeumannOperator V E hsep (p τ)⟫_ℝ = _
    rw [hwRep τ hτ]
  exact hMoving.congr_of_eventuallyEq hObsLocal.symm

#print axioms paper_A7_actual_H2_gives_SR_near_moving_derivative

end ReservoirSeismicityControl.Paper2026
