import ReservoirSeismicityControl.Paper2026.PhysicalA9SRFarObservation
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): compatibility of the initial-orbit and flux endpoint

The physical pressure equation (A1) at the initial time reads
    p_t(0) = -A p(0) + ∑_j f_j Q_j(0).
The far-field initial-orbit term in (A9) is paired with A e^{-At} p_t(0)
and then subtracts the kernel endpoint ∑ K_j(t) Q_j(0). These two
contributions cancel the initial-flux component exactly, leaving the
corresponding derivative of the homogeneous mild-pressure term.

This is a **physical algebraic identification**, not the derivative of the
bounded-input causal convolution. The latter needs the previously cited
W¹,¹ / L¹ off-diagonal kernel differentiation. No derivative of Q is used.

`L` represents the positive-time bounded operator P_far A e^{-At}; the
analytic-semigroup theorem providing that bounded operator remains the
standard external analytic input, rather than a fictitious bounded A at t=0.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The exact initial-orbit/initial-flux cancellation in manuscript (A9)
for the *actual signed SR far weight*. This uses the initial pressure
compatibility from (A1); it does not assume a differentiable well flux.
The operator `L` is to be instantiated by the positive-lag far-projected
Neumann generator `P_far A e^{-At}`. -/
theorem paper_A9_physical_SR_initial_flux_cancellation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ) (Q0 : Fin m → ℝ)
    (Ap0 pt0 : Lp ℝ 2 μ)
    (hInitial : pt0 = -Ap0 + ∑ j : Fin m, (Q0 j) • f j)
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (t : ℝ) :
    (fun w : Lp ℝ 2 μ =>
      (-⟪w, L Ap0⟫_ℝ) =
        (⟪w, L pt0⟫_ℝ - ∑ j : Fin m, ⟪w, L (f j)⟫_ℝ * Q0 j))
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) := by
  let w : Lp ℝ 2 μ := paperSRFarDiffusionWeight μ region hregion Kγ R
    gamma10 R0star cutoff t
  let T : Lp ℝ 2 μ →L[ℝ] ℝ := (innerSL ℝ w).comp L
  have hT : T pt0 = -T Ap0 + ∑ j : Fin m, Q0 j * T (f j) := by
    calc
      T pt0 = T (-Ap0 + ∑ j : Fin m, Q0 j • f j) :=
        congrArg T hInitial
      _ = -T Ap0 + ∑ j : Fin m, Q0 j * T (f j) := by
        simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul]
  have hComm : (∑ j : Fin m, Q0 j * T (f j)) =
      ∑ j : Fin m, T (f j) * Q0 j := by
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hComm] at hT
  have hRes : -T Ap0 = T pt0 - ∑ j : Fin m, T (f j) * Q0 j := by
    linarith only [hT]
  change -⟪w, L Ap0⟫_ℝ =
    ⟪w, L pt0⟫_ℝ - ∑ j : Fin m, ⟪w, L (f j)⟫_ℝ * Q0 j
  exact hRes

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_SR_initial_flux_cancellation
