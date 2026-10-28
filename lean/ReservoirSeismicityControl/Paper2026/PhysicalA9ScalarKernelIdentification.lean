import ReservoirSeismicityControl.Paper2026.PhysicalA9InitialFluxCancellation
import ReservoirSeismicityControl.Paper2026.PhysicalA9SRFarObservation
import Mathlib.Tactic

/-!
# Appendix A.3: scalarize the physical far-field Bochner convolution

The passing physical DG-to-causal theorem yields a finite sum of L²-valued
Bochner integrals. Equation (A9), and the archived convolution-derivative
results, instead use scalar kernels frozen at the SR observation time.

This file identifies these two representations **exactly**, by commuting
only the bounded scalar observation functional with the Bochner integral.
It never commutes an unbounded generator with an integral, and it never
uses a derivative of the well rates.

Integrability of the vector integrand is explicit here. In the ReservoirSeismicityControl
application it follows from the same analytic-semigroup/Davies--Gaffney
majorant used in the passing physical causal-identification theorem.
The derivative in observation time is a distinct subsequent obligation.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped NNReal InnerProductSpace BigOperators

/-- Bochner-to-scalar kernel bridge at a fixed time. The semigroup orbit
`v j s` is already the far-projected positive-lag generator orbit.
`w` is frozen during the causal integration; in the manuscript it is the
signed SR far weight at the *observation time*. The assumption is ordinary
Bochner integrability, not differentiability of the well input. -/
theorem paper_A9_physical_causal_scalar_kernel
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : ℕ) (t : NNReal) (w p : Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ) (v : Fin m → ℝ → Lp ℝ 2 μ)
    (hIntegrable : ∀ j : Fin m,
      Integrable (fun s : ℝ => (Q j s) • v j s)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t : ℝ)))) :
    ⟪w, p + ∑ j : Fin m,
       ∫ s in (0 : ℝ)..(t : ℝ), (Q j s) • v j s⟫_ℝ =
      ⟪w, p⟫_ℝ + ∑ j : Fin m,
        ∫ s in (0 : ℝ)..(t : ℝ), Q j s * ⟪w, v j s⟫_ℝ := by
  let F : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ w
  have hEach (j : Fin m) :
      F (∫ s in (0 : ℝ)..(t : ℝ), (Q j s) • v j s) =
        ∫ s in (0 : ℝ)..(t : ℝ), Q j s * ⟪w, v j s⟫_ℝ := by
    have hComm := F.integral_comp_comm (hIntegrable j)
    calc
      F (∫ s in (0 : ℝ)..(t : ℝ), (Q j s) • v j s) =
          F (∫ s in Set.Ioc (0 : ℝ) (t : ℝ), (Q j s) • v j s) := by
            rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
      _ = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), F ((Q j s) • v j s) := by
          exact hComm.symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ), Q j s * ⟪w, v j s⟫_ℝ := by
          rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
          congr 1
          funext s
          change F ((Q j s) • v j s) = Q j s * F (v j s)
          simp only [map_smul, smul_eq_mul]
  change F (p + ∑ j : Fin m,
    ∫ s in (0 : ℝ)..(t : ℝ), (Q j s) • v j s) =
      F p + ∑ j : Fin m,
        ∫ s in (0 : ℝ)..(t : ℝ), Q j s * ⟪w, v j s⟫_ℝ
  rw [map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hEach j

/-- The preceding scalarization written with the actual Neumann generator
positive-lag kernel operator. No assumption that the generator is a bounded
operator at lag zero is made: only the bounded positive-lag operator `T s`
is supplied, and the zero-lag endpoint has Lebesgue measure zero. -/
theorem paper_A9_positive_lag_scalar_kernel
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : ℕ) (t : NNReal) (w p : Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ) (f : Fin m → Lp ℝ 2 μ)
    (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hIntegrable : ∀ j : Fin m,
      Integrable (fun s : ℝ => (Q j s) • T s (f j))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t : ℝ)))) :
    ⟪w, p + ∑ j : Fin m,
        ∫ s in (0 : ℝ)..(t : ℝ), (Q j s) • T s (f j)⟫_ℝ =
      ⟪w, p⟫_ℝ + ∑ j : Fin m,
        ∫ s in (0 : ℝ)..(t : ℝ), Q j s * ⟪w, T s (f j)⟫_ℝ := by
  exact paper_A9_physical_causal_scalar_kernel μ m t w p Q
    (fun j s => T s (f j)) hIntegrable

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_causal_scalar_kernel
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_positive_lag_scalar_kernel
