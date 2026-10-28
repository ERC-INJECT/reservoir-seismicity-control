import ReservoirSeismicityControl.Paper2026.PhysicalA9StrictLag3DCausal20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9CanonicalOperatorCompatibility20261025
import Mathlib.Tactic

/-!
# A9: finite-horizon identification of the canonical physical far forcing

This identifies the strictly positive-lag analytic kernel in the PASSING
3D A5/DG causal-value theorem with the weak-Neumann well orbit in the
PASSING W¹,¹ convolution theorem.  No bounded generator at zero lag is used:
the single source-time endpoint is null in the Bochner integral.

This is a VALUE identification on [0,T], NOT a global derivative theorem.
It removes the independent PDE mild-value representation required by the
four-term regional A9 theorem after localizing that result to finite T.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- The causal generator representation from A5/DG, expressed using the
*same* canonical weak-Neumann orbit used in the W¹,¹ derivative theorem.
The analytic kernel is replaced inside the actual time integral, with the
potentially undefined zero-lag generator confined to a null endpoint. -/
theorem paper_A9_finite_horizon_causal_value_in_canonical_W11_orbit
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
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
            (Q i s) • Tfar ((t : ℝ) - s) (f i))) :
    ∀ t : NNReal, t ≤ T →
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar (Ap (t : ℝ)) =
        -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S t (S.generator p₀))) +
        ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (Q i s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i ((t : ℝ) - s))) := by
  classical
  intro t ht
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  have hEach (i : Fin m) :
      (∫ s in (0 : ℝ)..(t : ℝ),
          (Q i s) • Tfar ((t : ℝ) - s) (f i)) =
        -(∫ s in (0 : ℝ)..(t : ℝ),
          (Q i s) • P
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i ((t : ℝ) - s)))) := by
    let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))
    have hne : ∀ᵐ s : ℝ ∂ν, s ≠ (t : ℝ) := ν.ae_ne (t : ℝ)
    have hpoint : ∀ᵐ s : ℝ ∂ν,
        (Q i s) • Tfar ((t : ℝ) - s) (f i) =
          -((Q i s) • P
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i ((t : ℝ) - s)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with s hs hsne
      have hlag : 0 < (t : ℝ) - s := by
        apply sub_pos.mpr
        exact lt_of_le_of_ne hs.2 hsne
      have hKernel := hPhysicalKernel i ((t : ℝ) - s) hlag
      have hT : Tfar ((t : ℝ) - s) (f i) =
          -(P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
            (orbit i ((t : ℝ) - s)))) := by
        have hx := congrArg Neg.neg hKernel
        simpa only [neg_neg] using hx.symm
      rw [hT, smul_neg]
    calc
      (∫ s in (0 : ℝ)..(t : ℝ),
          (Q i s) • Tfar ((t : ℝ) - s) (f i)) =
          ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
            (Q i s) • Tfar ((t : ℝ) - s) (f i) := by
              rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
      _ = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
            -((Q i s) • P
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i ((t : ℝ) - s)))) := by
              exact integral_congr_ae hpoint
      _ = -(∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
            (Q i s) • P
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i ((t : ℝ) - s)))) := by
              rw [integral_neg]
      _ = -(∫ s in (0 : ℝ)..(t : ℝ),
            (Q i s) • P
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i ((t : ℝ) - s)))) := by
              rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  have hSum :
      (∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
        (Q i s) • Tfar ((t : ℝ) - s) (f i)) =
      -(∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
        (Q i s) • P
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
            (orbit i ((t : ℝ) - s)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact hEach i
  calc
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar (Ap (t : ℝ)) =
        -(P (S t (S.generator p₀)) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (Q i s) • Tfar ((t : ℝ) - s) (f i)) := hA5Causal t ht
    _ = -(P (S t (S.generator p₀))) +
        ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (Q i s) • P
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit i ((t : ℝ) - s))) := by
          rw [hSum]
          abel

#print axioms paper_A9_finite_horizon_causal_value_in_canonical_W11_orbit

end ReservoirSeismicityControl.Paper2026
