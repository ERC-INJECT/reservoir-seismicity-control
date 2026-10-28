import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-!
# Physical A7 — damping of the ACTUAL coefficient, with a.e.-time hypotheses

This is the manuscript coefficient `a(x,q)=gamma2(x,q)*Rstar(x)`.
The positivity assumption is almost everywhere in time, NOT for every time.
The proof obtains the damping of its actual causal propagator by interval
integral monotonicity. It is an applicability step toward the H² exponential
kernel estimate, not an assumption about H² regularity of R.

This target deliberately does not import the expensive 3D kernel modules.
No sorry, custom axiom, or derivative of Q.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- A3 time-a.e. positivity yields the physical propagator's exponential
    damping, and its half-damped form used in Appendix A.2. In particular,
    the temporal coefficient bounds need not hold at every time. -/
theorem physical_A7_actual_coefficient_damping_ae
    {X : Type*}
    (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (x : X) (v t amin m : ℝ)
    (hvt : v ≤ t)
    (hInt : IntervalIntegrable
      (fun q => gamma2 x q * Rstar x) volume v t)
    (hA3 : ∀ᵐ q ∂(volume : Measure ℝ),
      amin ≤ gamma2 x q * Rstar x) :
    (Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x)) ≤
      Real.exp (-(amin * (t - v)))) ∧
    (Real.exp (m * (t - v)) *
        Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x)) ≤
      Real.exp (-((amin - m) * (t - v)))) := by
  have hLower :
      amin * (t - v) ≤
        ∫ q in v..t, gamma2 x q * Rstar x := by
    have hmono := intervalIntegral.integral_mono_ae
      hvt (intervalIntegrable_const) hInt hA3
    simpa [mul_comm] using hmono
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_neg hLower)
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

#print axioms physical_A7_actual_coefficient_damping_ae

end ReservoirSeismicityControl.Paper2026
