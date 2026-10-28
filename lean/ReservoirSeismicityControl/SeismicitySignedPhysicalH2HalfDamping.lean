import ReservoirSeismicityControl.SeismicitySignedH2BochnerLift
import Mathlib.Tactic

/-!
# M1: polynomial spatial Sobolev kernels, without an artificial uniform residual bound

The direct spatial H² differentiation of the signed physical reciprocal's
Duhamel propagator creates the terms (t-v), (t-v)^2. These are not bounded
by an arbitrary constant independent of t-v after naive normalization by
the *full* aMin exponential kernel. A rigorous lifting theorem instead uses
half the physical damping and the inequalities

  tau * exp(-m*tau) <= 1/m,
  tau^2 * exp(-m*tau) <= (1/(m/2))^2,

for m>0, tau>=0. This module verifies those inequalities and then obtains
an actual time-uniform H² Bochner bound from a quadratic-polynomial kernel
envelope, also treating the homogeneous term.

The `H` below is intended to be the weak H²(U_j) graph space; the kernel
estimate itself (from the physical 3D weak Sobolev product/chain rules) and
its L² identification with the explicit signed physical reciprocal remain
outstanding. Thus this is a NONCIRCULAR kernel-estimate gate, NOT a complete
formal proof of Appendix A.2 (A7).
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The exponentially damped linear time moment needs no control on the
spatial coefficients beyond the lower damping `m>0`. -/
theorem sr_signed_half_damping_linear_moment
    (m tau : ℝ) (hm : 0 < m) (htau : 0 ≤ tau) :
    tau * Real.exp (-(m * tau)) ≤ m⁻¹ := by
  have hExp : m * tau ≤ Real.exp (m * tau) := by
    have he := Real.add_one_le_exp (m * tau)
    linarith
  have hScaled : (m * tau) * Real.exp (-(m * tau)) ≤ 1 := by
    calc
      (m * tau) * Real.exp (-(m * tau)) ≤
          Real.exp (m * tau) * Real.exp (-(m * tau)) :=
        mul_le_mul_of_nonneg_right hExp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [← one_div]
  apply (le_div_iff₀ hm).2
  calc
    (tau * Real.exp (-(m * tau))) * m =
      (m * tau) * Real.exp (-(m * tau)) := by ring
    _ ≤ 1 := hScaled

/-- The quadratic moment is bounded by applying the linear inequality at
half the exponent and squaring two nonnegative reals. -/
theorem sr_signed_half_damping_quadratic_moment
    (m tau : ℝ) (hm : 0 < m) (htau : 0 ≤ tau) :
    tau ^ 2 * Real.exp (-(m * tau)) ≤ ((m / 2)⁻¹) ^ 2 := by
  have hmHalf : 0 < m / 2 := by positivity
  have hLinear :=
    sr_signed_half_damping_linear_moment (m / 2) tau hmHalf htau
  have hLower : 0 ≤ tau * Real.exp (-((m / 2) * tau)) :=
    mul_nonneg htau (Real.exp_pos _).le
  have hUpper : 0 ≤ (m / 2)⁻¹ := (inv_pos.mpr hmHalf).le
  have hSquare :
      (tau * Real.exp (-((m / 2) * tau))) ^ 2 ≤ ((m / 2)⁻¹) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLinear) (add_nonneg hLower hUpper)]
  calc
    tau ^ 2 * Real.exp (-(m * tau)) =
        tau ^ 2 *
          (Real.exp (-((m / 2) * tau)) *
            Real.exp (-((m / 2) * tau))) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
    _ = (tau * Real.exp (-((m / 2) * tau))) ^ 2 := by ring
    _ ≤ ((m / 2)⁻¹) ^ 2 := hSquare

/-- A polynomial of degree two multiplied by exponential damping admits
an explicit uniform envelope. No assumptions about the signs of first or
second spatial derivatives are introduced. -/
theorem sr_signed_half_damping_quadratic_envelope
    (m tau C0 C1 C2 : ℝ)
    (hm : 0 < m) (htau : 0 ≤ tau)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    (C0 + C1 * tau + C2 * tau ^ 2) * Real.exp (-(m * tau)) ≤
      C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2 := by
  have hExp : Real.exp (-(m * tau)) ≤ 1 := by
    calc
      Real.exp (-(m * tau)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hm.le htau])
      _ = 1 := Real.exp_zero
  have h0 : C0 * Real.exp (-(m * tau)) ≤ C0 := by
    simpa using mul_le_mul_of_nonneg_left hExp hC0
  have h1 : C1 * (tau * Real.exp (-(m * tau))) ≤ C1 * m⁻¹ :=
    mul_le_mul_of_nonneg_left
      (sr_signed_half_damping_linear_moment m tau hm htau) hC1
  have h2 : C2 * (tau ^ 2 * Real.exp (-(m * tau))) ≤
      C2 * ((m / 2)⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_left
      (sr_signed_half_damping_quadratic_moment m tau hm htau) hC2
  calc
    (C0 + C1 * tau + C2 * tau ^ 2) * Real.exp (-(m * tau)) =
      C0 * Real.exp (-(m * tau)) +
        C1 * (tau * Real.exp (-(m * tau))) +
        C2 * (tau ^ 2 * Real.exp (-(m * tau))) := by ring
    _ ≤ C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2 := by
      exact add_le_add (add_le_add h0 h1) h2

/-- The physically relevant lag is nonnegative even outside the causal
interval. On the support of the causal measure it equals `t-v`. -/
private def srSignedCausalLag (t v : ℝ) : ℝ := max (t - v) 0

private theorem sr_signed_causal_lag_nonneg (t v : ℝ) :
    0 ≤ srSignedCausalLag t v := by
  exact le_max_right _ _

/-- Consolidated time-uniform H² Bochner theorem with the *correct*
quadratic spatial kernel envelope, including the homogeneous part. The
previous lifting theorem demanded an unduly strong uniform bound on a
residual kernel. This theorem derives that bound from the polynomial
spatial derivative estimate after allocating half of the damping to the
positive convolution measure.

For physical instantiation: take `m = aMin/2`, build `hom` and `kernel`
from the signed reciprocal's explicit spatial propagator on H²(U_j),
and prove `hHomPolynomial`, `hKernelPolynomial` with the weak-Sobolev
chain/product rules. `Yphysical` is the preexisting L² constructed solution,
not a postulated H² solution. -/
theorem sr_signed_physical_reciprocal_H2_from_polynomial_kernel
    {H L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (embed : H →L[ℝ] L)
    (m D0 D1 D2 C0 C1 C2 : ℝ)
    (hm : 0 < m)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (Yphysical : ℝ → L)
    (hom : ℝ → H) (kernel : ℝ → ℝ → H)
    (hHomPolynomial : ∀ t, 0 ≤ t →
      ‖hom t‖ ≤ (D0 + D1 * t + D2 * t ^ 2) * Real.exp (-(m * t)))
    (hKernelPolynomial : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure m t,
        ‖kernel t v‖ ≤
          (C0 + C1 * srSignedCausalLag t v +
            C2 * (srSignedCausalLag t v) ^ 2) *
              Real.exp (-(m * srSignedCausalLag t v)))
    (hInt : ∀ t, 0 ≤ t →
      Integrable (kernel t) (pressureExponentialKernelMeasure m t))
    (hPhysical : ∀ t, 0 ≤ t →
      Yphysical t = embed (hom t) + m⁻¹ •
        (∫ v, embed (kernel t v)
          ∂pressureExponentialKernelMeasure m t)) :
    ∀ t : ℝ, 0 ≤ t → ∃ y : H,
      embed y = Yphysical t ∧
      ‖y‖ ≤
        (D0 + D1 * m⁻¹ + D2 * ((m / 2)⁻¹) ^ 2) +
        (C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2) / m := by
  let H0 : ℝ := D0 + D1 * m⁻¹ + D2 * ((m / 2)⁻¹) ^ 2
  let Fmax : ℝ := C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2
  have hFmax : 0 ≤ Fmax := by
    dsimp [Fmax]
    positivity
  have hHom : ∀ t : ℝ, 0 ≤ t → ‖hom t‖ ≤ H0 := by
    intro t ht
    exact (hHomPolynomial t ht).trans
      (sr_signed_half_damping_quadratic_envelope m t D0 D1 D2
        hm ht hD0 hD1 hD2)
  have hKernel : ∀ t : ℝ, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure m t,
        ‖kernel t v‖ ≤ Fmax := by
    intro t ht
    filter_upwards [hKernelPolynomial t ht] with v hv
    exact hv.trans
      (sr_signed_half_damping_quadratic_envelope m
        (srSignedCausalLag t v) C0 C1 C2
        hm (sr_signed_causal_lag_nonneg t v) hC0 hC1 hC2)
  exact sr_signed_physical_reciprocal_exists_uniform_H2_lift
    embed m H0 Fmax hm hFmax Yphysical hom kernel
    hHom hKernel hInt hPhysical

#print axioms ReservoirSeismicityControl.sr_signed_half_damping_linear_moment
#print axioms ReservoirSeismicityControl.sr_signed_half_damping_quadratic_moment
#print axioms ReservoirSeismicityControl.sr_signed_half_damping_quadratic_envelope
#print axioms ReservoirSeismicityControl.sr_signed_physical_reciprocal_H2_from_polynomial_kernel

end ReservoirSeismicityControl
