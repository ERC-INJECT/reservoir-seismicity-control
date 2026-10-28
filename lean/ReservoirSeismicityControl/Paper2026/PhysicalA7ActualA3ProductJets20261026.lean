import ReservoirSeismicityControl.SeismicitySignedSpatialHessianLpCrossTerms
import Mathlib.Tactic

/-!
# Appendix A.2: actual spatial product coefficient jets from A3

The damping coefficient is `a(x,t) = gamma2(x,t) * Rstar(x)`.
Assumption 3 gives uniform local H² for each factor on every bounded
Lipschitz near-well neighborhood in spatial dimension <= 3.  Standard
H²-to-L∞ and H²-to-W¹,⁶ embeddings produce the input Lp representatives.

This file proves, in the ACTUAL local Lp spaces, that the value, every
first product-rule jet, and every second product-rule jet of `a` have the
required integrability. In particular the mixed second jet uses only
L⁶ * L⁶, not an unjustified L∞ bound on a first spatial derivative.

It does NOT assert that the candidate jets have yet been identified as
weak derivatives. The cited weak Sobolev Leibniz rule and construction of
H² smoothing approximants are still external dependencies. No new axiom,
sorry, or changes to passing files.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The actual `gamma2 * Rstar` coefficient from A3, with its first and
mixed-second product-rule candidate jets, belongs to the precise L²/L⁶
spaces needed for the existing time-primitive and propagator results.
All spatial derivative factors enter as Sobolev Lp representatives of
`gamma2` and `Rstar`, never as pre-assumed jets of the product. -/
theorem physical_A7_actual_A3_product_jets_memLp
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (gamma2 Rstar : Lp ℝ (⊤ : ENNReal) μ)
    (Dgamma2 DRstar : Fin 3 → Lp ℝ (6 : ENNReal) μ)
    (DDgamma2 DDRstar : Fin 3 → Fin 3 → Lp ℝ (2 : ENNReal) μ) :
    MemLp (fun x : X => (gamma2 x : ℝ) * (Rstar x : ℝ)) 2 μ ∧
    (∀ i : Fin 3, MemLp (fun x : X =>
      (Dgamma2 i x : ℝ) * (Rstar x : ℝ) +
      (gamma2 x : ℝ) * (DRstar i x : ℝ)) 6 μ) ∧
    (∀ i j : Fin 3, MemLp (fun x : X =>
      (DDgamma2 i j x : ℝ) * (Rstar x : ℝ) +
      (Dgamma2 i x : ℝ) * (DRstar j x : ℝ) +
      (Dgamma2 j x : ℝ) * (DRstar i x : ℝ) +
      (gamma2 x : ℝ) * (DDRstar i j x : ℝ)) 2 μ) := by
  constructor
  · exact ((Lp.memLp gamma2).fun_mul (Lp.memLp Rstar)).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ ⊤)
  constructor
  · intro i
    have hleft : MemLp (fun x : X =>
        (Dgamma2 i x : ℝ) * (Rstar x : ℝ)) 6 μ :=
      (Lp.memLp (Dgamma2 i)).fun_mul (Lp.memLp Rstar)
    have hright : MemLp (fun x : X =>
        (gamma2 x : ℝ) * (DRstar i x : ℝ)) 6 μ :=
      (Lp.memLp gamma2).fun_mul (Lp.memLp (DRstar i))
    exact hleft.add hright
  · intro i j
    have h0 : MemLp (fun x : X =>
        (DDgamma2 i j x : ℝ) * (Rstar x : ℝ)) 2 μ :=
      (Lp.memLp (DDgamma2 i j)).fun_mul (Lp.memLp Rstar)
    have h1 : MemLp (fun x : X =>
        (Dgamma2 i x : ℝ) * (DRstar j x : ℝ)) 2 μ :=
      ReservoirSeismicityControl.sr_signed_spatial_L6_times_L6_memLp2 μ
        (Dgamma2 i) (DRstar j)
    have h2 : MemLp (fun x : X =>
        (Dgamma2 j x : ℝ) * (DRstar i x : ℝ)) 2 μ :=
      ReservoirSeismicityControl.sr_signed_spatial_L6_times_L6_memLp2 μ
        (Dgamma2 j) (DRstar i)
    have h3 : MemLp (fun x : X =>
        (gamma2 x : ℝ) * (DDRstar i j x : ℝ)) 2 μ :=
      (Lp.memLp gamma2).fun_mul (Lp.memLp (DDRstar i j))
    exact ((h0.add h1).add h2).add h3

#print axioms physical_A7_actual_A3_product_jets_memLp

end ReservoirSeismicityControl.Paper2026
