import ReservoirSeismicityControl.Paper2026.PhysicalA7KernelIntegrability
import ReservoirSeismicityControl.SeismicitySignedPhysicalLocalH2
import ReservoirSeismicityControl.PressureConcreteKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Physical A7: exact normalization of the EXISTING scalar Duhamel identity

The polynomial H² lifting theorem uses the exponentially weighted finite
measure ν_{m,t}(dv) = 1_(0,t](v) m exp(-m(t-v)) dv. The physical reciprocal
ODE, however, has the Lebesgue-time Duhamel kernel exp(-∫_v^t a).

This module establishes their exact equivalence in the real-valued spatial
fiber. It reuses the *already proved* physical scalar Duhamel theorem; it
is not another proof of the reciprocal equation and does not assume Q-dot.

To close A7 as an L²/H² assertion, one still has to identify this pointwise
formula a.e. with the embedded H²-valued Bochner integral. That is a
separate standard Sobolev/Fubini applicability step, not proved here.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The half-damping residual kernel is exactly the physical scalar
    propagator with one factor exp(m(t-v)) restored. -/
private noncomputable def physicalA7Residual (a : ℝ → ℝ) (m t v : ℝ) : ℝ :=
  Real.exp (m * (t - v)) * ReservoirSeismicityControl.srSignedDuhamelFactor a t v

/-- Conversion from the finite half-damping convolution measure to the
    physical Lebesgue-time kernel. The only integrability assumption here
    is on the normalized integrand, as supplied by the preceding A7
    Bochner theorem upon taking a scalar evaluation/representative. -/
theorem physical_A7_weighted_scalar_kernel_exact
    (a b : ℝ → ℝ) (m t : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) :
    m⁻¹ *
      (∫ v, physicalA7Residual a m t v * b v
        ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
      (∫ v in (0 : ℝ)..t,
        ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc 0 t)
  let k : ℝ → ℝ := fun v => m * Real.exp (-(m * (t - v)))
  let F : ℝ → ℝ := fun v => physicalA7Residual a m t v * b v
  have hν : ReservoirSeismicityControl.pressureExponentialKernelMeasure m t =
      μ.withDensity (fun v => ENNReal.ofReal (k v)) := by
    rfl
  have hkpos (v : ℝ) : 0 ≤ k v :=
    mul_nonneg hm.le (Real.exp_pos _).le
  have hkmeas : AEMeasurable (fun v => ENNReal.ofReal (k v)) μ := by
    have hh : Measurable (fun v : ℝ => ENNReal.ofReal (k v)) := by
      dsimp [k]
      fun_prop
    exact hh.aemeasurable
  have hkfinite : ∀ᵐ v ∂μ, ENNReal.ofReal (k v) < ⊤ :=
    Filter.Eventually.of_forall (fun v => ENNReal.ofReal_lt_top)
  have hchange :
      (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
        ∫ v, k v * F v ∂μ := by
    rw [hν]
    calc
      (∫ v, F v ∂μ.withDensity (fun v => ENNReal.ofReal (k v))) =
          ∫ v, (ENNReal.ofReal (k v)).toReal • F v ∂μ := by
            exact integral_withDensity_eq_integral_toReal_smul₀
              hkmeas hkfinite F
      _ = ∫ v, k v * F v ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with v
        rw [ENNReal.toReal_ofReal (hkpos v), smul_eq_mul]
  have hpoint (v : ℝ) :
      k v * F v = m * (ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v) := by
    dsimp [k, F, physicalA7Residual]
    have he :
        Real.exp (-(m * (t - v))) * Real.exp (m * (t - v)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (m * Real.exp (-(m * (t - v)))) *
          (Real.exp (m * (t - v)) *
            ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v) =
          m * (Real.exp (-(m * (t - v))) *
            Real.exp (m * (t - v))) *
            (ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v) := by ring
      _ = m * (ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v) := by
        rw [he]
        ring
  have hmeasure :
      (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
        m * ∫ v, ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v ∂μ := by
    rw [hchange]
    have heq : (fun v : ℝ => k v * F v) =
        (fun v : ℝ => m * (ReservoirSeismicityControl.srSignedDuhamelFactor a t v * b v)) := by
      funext v
      exact hpoint v
    rw [heq, integral_const_mul]
  rw [show (∫ v, physicalA7Residual a m t v * b v
      ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
      (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) from rfl]
  rw [hmeasure]
  rw [intervalIntegral.integral_of_le ht]
  have hmne : m ≠ 0 := ne_of_gt hm
  field_simp [hmne]
  rfl

/-- In particular the *existing* explicit scalar signed reciprocal is
    represented by precisely the same normalized causal measure used in
    the recovered H² lifting theorem. No Duhamel equality is postulated. -/
theorem physical_A7_signed_scalar_solution_normalized
    (a b : ℝ → ℝ) (y0 m t : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) :
    ReservoirSeismicityControl.srReciprocalExplicit a b y0 t =
      Real.exp (-ReservoirSeismicityControl.srReciprocalPrimitive a t) * y0 +
      m⁻¹ * (∫ v, physicalA7Residual a m t v * b v
        ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) := by
  rw [ReservoirSeismicityControl.sr_signed_reciprocal_explicit_duhamel]
  rw [physical_A7_weighted_scalar_kernel_exact a b m t hm ht]

#print axioms physical_A7_weighted_scalar_kernel_exact
#print axioms physical_A7_signed_scalar_solution_normalized

end ReservoirSeismicityControl.Paper2026
