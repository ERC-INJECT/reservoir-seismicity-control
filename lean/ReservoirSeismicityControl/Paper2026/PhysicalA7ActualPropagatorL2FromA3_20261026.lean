import ReservoirSeismicityControl.Paper2026.PhysicalA7PhysicalDampingAE20261026
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# A7: actual physical causal propagator, from the a.e. A3 cylinder bound

This theorem is for the genuine coefficient `a(x,q)=gamma2(x,q)*Rstar(x)`
on the physical time axis. For negative time we extend it by the positive
constant `gamma2m*Rstarm`; this does not modify any physical causal integral
with `0 <= v <= t`.

The key quantifier order is one spatial full-measure set on which the
propagator estimate holds on EVERY causal interval. It follows from
Fubini plus interval integral monotonicity, not from falsely strengthening
space-time a.e. bounds to everywhere-in-time bounds.

The first theorem also derives the actual propagator's L² membership on
a finite-volume near-well region. Spatial measurability and local time
integrability are explicitly supplied; they do not assert H² regularity.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The physical coefficient on nonnegative time, with an irrelevant
constant continuation on negative time. -/
noncomputable def physicalA7CausalCoefficient
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (amin : ℝ) (x : X) (q : ℝ) : ℝ :=
  if 0 ≤ q then gamma2 x q * Rstar x else amin

/-- Physical coefficient agrees with the original model for positive time. -/
theorem physical_A7_causal_coefficient_agrees
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (amin : ℝ) (x : X) (q : ℝ) (hq : 0 ≤ q) :
    physicalA7CausalCoefficient gamma2 Rstar amin x q =
      gamma2 x q * Rstar x := by
  simp [physicalA7CausalCoefficient, hq]

/-- The harmless off-axis continuation gives exactly the original
physical coefficient primitive on every causal interval. -/
theorem physical_A7_causal_integral_is_actual
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (amin : ℝ) (x : X) (v t : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t) :
    (∫ q in v..t, physicalA7CausalCoefficient gamma2 Rstar amin x q) =
      ∫ q in v..t, gamma2 x q * Rstar x := by
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le hvt] at hq
  exact physical_A7_causal_coefficient_agrees gamma2 Rstar amin
    x q (hv.trans hq.1)

/-- The actual causal propagator inherits its uniform time-decay estimate
from A3's a.e. cylinder bounds. There is one exceptional spatial null set,
independent of `v` and `t`. In particular, no everywhere-in-time A3 premise
is used. -/
theorem physical_A7_actual_propagator_damping_from_spacetime_A3
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm m : ℝ)
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
      (Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x)) ≤
        Real.exp (-(gamma2m * Rstarm * (t - v)))) ∧
      (Real.exp (m * (t - v)) *
        Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x)) ≤
        Real.exp (-((gamma2m * Rstarm - m) * (t - v)))) := by
  have hSections := Measure.ae_ae_of_ae_prod hA3
  filter_upwards [hSections, hRstar, hInt] with x hx hr hIntegrable
  have hRpos : 0 ≤ Rstar x :=
    (le_of_lt hRstarm).trans hr
  have hCoeff : ∀ᵐ q ∂(volume : Measure ℝ),
      gamma2m * Rstarm ≤
        physicalA7CausalCoefficient gamma2 Rstar
          (gamma2m * Rstarm) x q := by
    filter_upwards [hx] with q hq
    by_cases hq0 : 0 ≤ q
    · rw [physical_A7_causal_coefficient_agrees gamma2 Rstar
        (gamma2m * Rstarm) x q hq0]
      calc
        gamma2m * Rstarm ≤ gamma2m * Rstar x :=
          mul_le_mul_of_nonneg_left hr (le_of_lt hg2m)
        _ ≤ gamma2 x q * Rstar x :=
          mul_le_mul_of_nonneg_right (hq hq0) hRpos
    · simp [physicalA7CausalCoefficient, hq0]
  intro v t hv hvt
  have hApply := physical_A7_actual_coefficient_damping_ae
    (fun (_ : Unit) q =>
      physicalA7CausalCoefficient gamma2 Rstar
        (gamma2m * Rstarm) x q)
    (fun (_ : Unit) => (1 : ℝ)) () v t
    (gamma2m * Rstarm) m hvt
    (by simpa using (hIntegrable v t hv hvt))
    (by simpa using hCoeff)
  simp only [mul_one] at hApply
  rw [physical_A7_causal_integral_is_actual gamma2 Rstar
    (gamma2m * Rstarm) x v t hv hvt] at hApply
  exact hApply

/-- The *actual physical propagator*, not an arbitrary L² field, belongs
uniformly in time to L² on a finite-volume near-well region. There is no
spatial derivative or H² premise. -/
theorem physical_A7_actual_propagator_memLp_from_A3
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
    (hMeas : ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      AEStronglyMeasurable (fun x =>
        Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x))) μ) :
    ∀ v t : ℝ, 0 ≤ v → v ≤ t →
      MemLp (fun x => Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x))) (2 : ENNReal) μ := by
  have hDamping := physical_A7_actual_propagator_damping_from_spacetime_A3
    μ gamma2 Rstar gamma2m Rstarm 0
    hg2m hRstarm hA3 hRstar hInt
  intro v t hv hvt
  have hTop : MemLp (fun x => Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x))) (⊤ : ENNReal) μ := by
    apply memLp_top_of_bound (hMeas v t hv hvt)
      (Real.exp (-(gamma2m * Rstarm * (t - v))))
    filter_upwards [hDamping] with x hx
    have hBound := (hx v t hv hvt).1
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hBound
  exact hTop.mono_exponent (by norm_num : (2 : ENNReal) ≤ ⊤)

#print axioms physical_A7_actual_propagator_damping_from_spacetime_A3
#print axioms physical_A7_actual_propagator_memLp_from_A3

end ReservoirSeismicityControl.Paper2026
