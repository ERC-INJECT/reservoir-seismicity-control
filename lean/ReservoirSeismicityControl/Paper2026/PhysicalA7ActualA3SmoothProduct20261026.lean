import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3ProductJets20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalKernelDerivativeBridge
import Mathlib.Tactic

/-!
# A7: exact spatial derivatives of the physical A3 product on smooth approximants

The physical damping coefficient is a(x,t) = gamma2(x,t) * Rstar(x).
The preceding passing module established the Lp integrability of the A3
product-rule candidates. This module verifies that the candidates are
ACTUAL first and ordered mixed-second coordinate derivatives for smooth
representatives, rather than independently assuming product derivatives.

This is the smooth part of the standard H2 Sobolev Leibniz approximation
argument. Passing to nonsmooth H2 coefficients still requires spatial H2
mollification/weak closure and cannot be inferred from this theorem alone.
No sorry, custom axioms or changes to the passing project.
-/

namespace ReservoirSeismicityControl.Paper2026

open ReservoirSeismicityControl.SeismicitySignedPhysicalThreeDimensionalKernel
open ReservoirSeismicityControl.SeismicitySignedPhysicalKernelDerivativeBridge

private abbrev Spatial3 := Fin 3 → ℝ

private theorem update_at_same (x : Spatial3) (i : Fin 3) :
    Function.update x i (x i) = x := by
  funext j
  by_cases hij : j = i
  · subst j
    simp
  · simp [hij]

/-- For each physical time `t`, the 3 first and 9 ordered mixed-second
coordinate derivatives of `gamma2(·,t) * Rstar` are exactly the A3
Leibniz jets. No derivatives of the *product* are assumed; only the
first/second coordinate derivatives of its smooth factor approximants.
The second formula needs all four H2 terms, including the two mixed
first-order products that are only L6 × L6 in dimension three. -/
theorem physical_A7_actual_A3_smooth_product_derivatives
    (gamma2 : Spatial3 → ℝ → ℝ) (Rstar : Spatial3 → ℝ) (t : ℝ)
    (Dgamma2 : Fin 3 → Spatial3 → ℝ)
    (DDgamma2 : Fin 3 → Fin 3 → Spatial3 → ℝ)
    (DRstar : Fin 3 → Spatial3 → ℝ)
    (DDRstar : Fin 3 → Fin 3 → Spatial3 → ℝ)
    (hg : ∀ i x, HasDerivAt
      (section3 (fun y => gamma2 y t) i x) (Dgamma2 i x) (x i))
    (hr : ∀ i x, HasDerivAt
      (section3 Rstar i x) (DRstar i x) (x i))
    (hDg : ∀ i j x, HasDerivAt
      (section3 (Dgamma2 i) j x) (DDgamma2 i j x) (x j))
    (hDr : ∀ i j x, HasDerivAt
      (section3 (DRstar i) j x) (DDRstar i j x) (x j)) :
    (∀ i x, HasDerivAt
      (section3 (fun y => gamma2 y t * Rstar y) i x)
      (Dgamma2 i x * Rstar x + gamma2 x t * DRstar i x) (x i)) ∧
    (∀ i j x, HasDerivAt
      (section3 (fun y =>
        Dgamma2 i y * Rstar y + gamma2 y t * DRstar i y) j x)
      (DDgamma2 i j x * Rstar x +
       Dgamma2 i x * DRstar j x +
       Dgamma2 j x * DRstar i x +
       gamma2 x t * DDRstar i j x) (x j)) := by
  constructor
  · intro i x
    have h := (hg i x).mul (hr i x)
    convert h using 1
    all_goals
      first
      | rfl
      | simp only [section3, update_at_same] <;> ring
  · intro i j x
    have hleft := (hDg i j x).mul (hr j x)
    have hright := (hg j x).mul (hDr i j x)
    have h := hleft.add hright
    convert h using 1
    all_goals
      first
      | rfl
      | simp only [section3, update_at_same] <;> ring

#print axioms physical_A7_actual_A3_smooth_product_derivatives

end ReservoirSeismicityControl.Paper2026
