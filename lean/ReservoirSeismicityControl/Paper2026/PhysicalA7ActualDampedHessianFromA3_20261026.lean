import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualPropagatorL2FromA3_20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalDampedKernelHessian
import Mathlib.Tactic

/-!
# Actual A3-controlled exponentially damped spatial Hessian bracket

Prior test established that the *undamped* physical five-term Hessian bracket
is L², using only the positivity of the physical time integral.

This step supplies the missing CAUSAL DECAY of the real coefficient
  a(x,q) = gamma2(x,q) * Rstar(x)
without upgrading A3's a.e. space-time bounds to all-time bounds.

For lag = t-v >= 0, define amin = gamma2m * Rstarm. Then
  A(x,t,v) >= amin * lag for a.e. x,
and consequently
  exp(amin * lag) * exp(-A(x,t,v)) = exp(-(A-amin*lag)) <= 1.

We apply the existing verified five-term L² product theorem to this *shifted*
nonnegative primitive, so that the complete physical Hessian expression
has an L² envelope AFTER removing its true exponential damping.

This does NOT claim that this bracket is yet the actual WEAK spatial Hessian;
that requires the following physical Sobolev identification step.
No sorry, axioms, or changes to frozen modules.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalDampedKernelHessian

/-- The genuinely physical causal primitive factors because `Rstar` is
constant in time. This reduces its spatial Sobolev calculation to the
H² product of `Rstar` with the time integral of `gamma2`, rather than
requiring any extra time regularity of `Rstar`. -/
theorem physical_A7_actual_causal_primitive_factors
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (x : X) (v t : ℝ) :
    (∫ q in v..t, gamma2 x q * Rstar x) =
      (∫ q in v..t, gamma2 x q) * Rstar x := by
  calc
    (∫ q in v..t, gamma2 x q * Rstar x) =
        ∫ q in v..t, Rstar x * gamma2 x q := by
      apply intervalIntegral.integral_congr
      intro q hq
      ring
    _ = Rstar x * (∫ q in v..t, gamma2 x q) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (∫ q in v..t, gamma2 x q) * Rstar x := by ring

/-- A3 yields the *sharp positive slope* of the actual causal time integral
on one full-measure spatial set, simultaneously for every causal interval. -/
theorem physical_A7_actual_primitive_lower_linear_from_A3
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm : ℝ)
    (hg2m : 0 < gamma2m) (hRstarm : 0 < Rstarm)
    (hA3 : ∀ᵐ z ∂(μ.prod (volume : Measure ℝ)),
      0 ≤ z.2 → gamma2m ≤ gamma2 z.1 z.2)
    (hRstar : ∀ᵐ x ∂μ, Rstarm ≤ Rstar x)
    (hInt : ∀ᵐ x ∂μ, ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      IntervalIntegrable
        (physicalA7CausalCoefficient gamma2 Rstar
          (gamma2m * Rstarm) x)
        volume v t) :
    ∀ᵐ x ∂μ, ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      gamma2m * Rstarm * (t - v) ≤
        ∫ q in v..t, gamma2 x q * Rstar x := by
  have hDamping := physical_A7_actual_propagator_damping_from_spacetime_A3
    μ gamma2 Rstar gamma2m Rstarm 0
    hg2m hRstarm hA3 hRstar hInt
  filter_upwards [hDamping] with x hx
  intro v t hv hvt
  have hexp := (hx v t hv hvt).1
  have hlog := Real.exp_le_exp.mp hexp
  linarith

/-- The complete five-term physical Hessian bracket, multiplied by the
ACTUAL propagator after removing exp(-amin*(t-v)), is L²-bounded by the
same five Sobolev product terms. This is the precise time-decaying estimate
needed before Bochner integration of the physical weak Hessian.

All L²/L⁶/L∞ jets remain explicit *input fields*, not asserted derivatives
of the nonsmooth physical kernel. Their identification is the next gate. -/
theorem physical_A7_actual_decay_normalized_five_term_L2_from_A3
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm : ℝ)
    (hg2m : 0 < gamma2m) (hRstarm : 0 < Rstarm)
    (hA3 : ∀ᵐ z ∂(μ.prod (volume : Measure ℝ)),
      0 ≤ z.2 → gamma2m ≤ gamma2 z.1 z.2)
    (hRstar : ∀ᵐ x ∂μ, Rstarm ≤ Rstar x)
    (hInt : ∀ᵐ x ∂μ, ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      IntervalIntegrable
        (physicalA7CausalCoefficient gamma2 Rstar
          (gamma2m * Rstarm) x)
        volume v t)
    (v t : ℝ) (hv : 0 ≤ v) (hvt : v ≤ t)
    (bij Aij : Lp ℝ (2 : ENNReal) μ)
    (Ai Aj bi bj : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ)
    (hShiftMeas : AEStronglyMeasurable
      (fun x => Real.exp (-((∫ q in v..t, gamma2 x q * Rstar x) -
        gamma2m * Rstarm * (t - v)))) μ) :
    MemLp (fun x : X =>
      Real.exp (-((∫ q in v..t, gamma2 x q * Rstar x) -
        gamma2m * Rstarm * (t - v))) *
      ((bij x : ℝ) - (Ai x : ℝ) * (bj x : ℝ) -
        (Aj x : ℝ) * (bi x : ℝ) -
        (Aij x : ℝ) * (b x : ℝ) +
        ((Ai x : ℝ) * (Aj x : ℝ)) * (b x : ℝ))) 2 μ ∧
    eLpNorm (fun x : X =>
      Real.exp (-((∫ q in v..t, gamma2 x q * Rstar x) -
        gamma2m * Rstarm * (t - v))) *
      ((bij x : ℝ) - (Ai x : ℝ) * (bj x : ℝ) -
        (Aj x : ℝ) * (bi x : ℝ) -
        (Aij x : ℝ) * (b x : ℝ) +
        ((Ai x : ℝ) * (Aj x : ℝ)) * (b x : ℝ))) 2 μ ≤
      (((eLpNorm (bij : X → ℝ) 2 μ +
        (eLpNorm (Ai : X → ℝ) 6 μ *
          eLpNorm (bj : X → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        (eLpNorm (Aj : X → ℝ) 6 μ *
          eLpNorm (bi : X → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        eLpNorm (Aij : X → ℝ) 2 μ *
          eLpNorm (b : X → ℝ) ⊤ μ) +
      (((eLpNorm (Ai : X → ℝ) 6 μ *
          eLpNorm (Aj : X → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) *
          eLpNorm (b : X → ℝ) ⊤ μ) := by
  have hLower := physical_A7_actual_primitive_lower_linear_from_A3
    μ gamma2 Rstar gamma2m Rstarm hg2m hRstarm hA3 hRstar hInt
  have hShiftNonnegative : ∀ᵐ x ∂μ,
      0 ≤ (∫ q in v..t, gamma2 x q * Rstar x) -
        gamma2m * Rstarm * (t - v) := by
    filter_upwards [hLower] with x hx
    exact sub_nonneg.mpr (hx v t hv hvt)
  exact physical_damped_kernel_hessian_L2_and_bound
    μ (fun x => (∫ q in v..t, gamma2 x q * Rstar x) -
      gamma2m * Rstarm * (t - v))
    bij Aij Ai Aj bi bj b hShiftNonnegative hShiftMeas

#print axioms physical_A7_actual_causal_primitive_factors
#print axioms physical_A7_actual_primitive_lower_linear_from_A3
#print axioms physical_A7_actual_decay_normalized_five_term_L2_from_A3

end ReservoirSeismicityControl.Paper2026
