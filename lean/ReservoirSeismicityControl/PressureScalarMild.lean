import ReservoirSeismicityControl.PressureConcreteKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Appendix A.1: variation of constants for a scalar diffusion mode

Suppose the modal trajectory is continuous on [a,b] and satisfies
p'(s) = -lam * p(s) + forcing(s) at interior times a < s < b.
Assume only that the forcing is interval-integrable, not differentiable.
Then the fundamental theorem of calculus gives the exact exponential mild
formula, including its lam-scaled form used in Stage 24.

This formulation is useful for ZOH inputs: the ODE need not hold at the
switching instants a and b, and derivatives of the input are never used.
Joining all switching intervals and proving the scalar ODE from the
Neumann PDE remain separate proof obligations.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The integrating-factor derivative cancels the homogeneous decay.
No derivative of the forcing is used. -/
theorem pressure_scalar_weighted_hasDerivAt
    (lam s : ℝ) (mode forcing : ℝ → ℝ)
    (hode : HasDerivAt mode (-lam * mode s + forcing s) s) :
    HasDerivAt (fun z : ℝ => Real.exp (lam * z) * mode z)
      (Real.exp (lam * s) * forcing s) s := by
  have hinner : HasDerivAt (fun z : ℝ => lam * z) lam s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul lam
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (lam * z))
      (Real.exp (lam * s) * lam) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (lam * s)).comp s hinner
  convert hexp.mul hode using 1
  ring

/-- An interval-integrable force remains integrable after multiplication
by the smooth exponential integrating factor. -/
theorem pressure_scalar_weighted_integrable
    (lam a b : ℝ) (forcing : ℝ → ℝ)
    (hforcing : IntervalIntegrable forcing volume a b) :
    IntervalIntegrable
      (fun s : ℝ => Real.exp (lam * s) * forcing s) volume a b := by
  have hexp : ContinuousOn (fun s : ℝ => Real.exp (lam * s))
      (Set.uIcc a b) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (lam * s))).continuousOn
  exact hforcing.continuousOn_mul hexp

/-- The integrating-factor identity on a closed time interval. The mode
is continuous at the endpoints; the ODE is needed only in the interior.
In particular, the forcing may jump at either endpoint. -/
theorem pressure_scalar_integrating_factor
    (lam a b : ℝ) (mode forcing : ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn mode (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ioo a b,
      HasDerivAt mode (-lam * mode s + forcing s) s)
    (hforcing : IntervalIntegrable forcing volume a b) :
    Real.exp (lam * b) * mode b - Real.exp (lam * a) * mode a =
      ∫ s in a..b, Real.exp (lam * s) * forcing s := by
  have hcontw : ContinuousOn
      (fun s : ℝ => Real.exp (lam * s) * mode s) (Set.Icc a b) := by
    have hexp : ContinuousOn (fun s : ℝ => Real.exp (lam * s))
        (Set.Icc a b) :=
      (by fun_prop : Continuous (fun s : ℝ => Real.exp (lam * s))).continuousOn
    exact hexp.mul hcont
  have hderiv : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => Real.exp (lam * z) * mode z)
        (Real.exp (lam * s) * forcing s) s := by
    intro s hs
    exact pressure_scalar_weighted_hasDerivAt lam s mode forcing
      (hode s hs)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s : ℝ => Real.exp (lam * s) * mode s)
    (f' := fun s : ℝ => Real.exp (lam * s) * forcing s)
    (a := a) (b := b) hab hcontw hderiv
    (pressure_scalar_weighted_integrable lam a b forcing hforcing)
  exact h.symm

/-- Scalar variation of constants on any interval [a,b]. Only the
scalar ODE at interior times and interval integrability are assumed. -/
theorem pressure_scalar_mild_from_ode
    (lam a b : ℝ) (mode forcing : ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn mode (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ioo a b,
      HasDerivAt mode (-lam * mode s + forcing s) s)
    (hforcing : IntervalIntegrable forcing volume a b) :
    mode b = Real.exp (-(lam * (b - a))) * mode a +
      ∫ s in a..b,
        Real.exp (-(lam * (b - s))) * forcing s := by
  have hfactor := pressure_scalar_integrating_factor
    lam a b mode forcing hab hcont hode hforcing
  have hexp : Real.exp (-(lam * b)) * Real.exp (lam * b) = 1 := by
    rw [← Real.exp_add]
    have hzero : -(lam * b) + lam * b = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hhom : Real.exp (-(lam * b)) * Real.exp (lam * a) =
      Real.exp (-(lam * (b - a))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hweighted_eq : Real.exp (lam * b) * mode b =
      Real.exp (lam * a) * mode a +
        (∫ s in a..b, Real.exp (lam * s) * forcing s) := by
    linarith [hfactor]
  have hkernel : ∀ s : ℝ,
      Real.exp (-(lam * (b - s))) =
        Real.exp (-(lam * b)) * Real.exp (lam * s) := by
    intro s
    rw [← Real.exp_add]
    congr 1
    ring
  have hconv :
      (∫ s in a..b,
        Real.exp (-(lam * (b - s))) * forcing s) =
      Real.exp (-(lam * b)) *
        (∫ s in a..b,
          Real.exp (lam * s) * forcing s) := by
    have heq :
        (fun s : ℝ => Real.exp (-(lam * (b - s))) * forcing s) =
        (fun s : ℝ => Real.exp (-(lam * b)) *
          (Real.exp (lam * s) * forcing s)) := by
      funext s
      rw [hkernel s]
      ring
    rw [heq, intervalIntegral.integral_const_mul]
  calc
    mode b = Real.exp (-(lam * b)) *
        (Real.exp (lam * b) * mode b) := by
      rw [← mul_assoc, hexp, one_mul]
    _ = Real.exp (-(lam * b)) *
        (Real.exp (lam * a) * mode a +
          (∫ s in a..b, Real.exp (lam * s) * forcing s)) := by
      rw [hweighted_eq]
    _ = Real.exp (-(lam * (b - a))) * mode a +
        (∫ s in a..b,
          Real.exp (-(lam * (b - s))) * forcing s) := by
      rw [mul_add, ← mul_assoc, hhom, hconv]

/-- Multiply variation of constants by the eigenvalue. The convolution
kernel is precisely `lam * exp (-lam * (b-s))`, as in Stage 24. -/
theorem pressure_scalar_scaled_mild_from_ode
    (lam a b : ℝ) (mode forcing : ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn mode (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ioo a b,
      HasDerivAt mode (-lam * mode s + forcing s) s)
    (hforcing : IntervalIntegrable forcing volume a b) :
    lam * mode b =
      Real.exp (-(lam * (b - a))) * (lam * mode a) +
      (∫ s in a..b,
        (lam * Real.exp (-(lam * (b - s)))) * forcing s) := by
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  rw [pressure_scalar_mild_from_ode lam a b mode forcing hab hcont hode hforcing]
  ring

end ReservoirSeismicityControl
