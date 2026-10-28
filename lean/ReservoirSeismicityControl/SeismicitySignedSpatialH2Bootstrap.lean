import ReservoirSeismicityControl.SeismicitySignedReciprocalUniformBox
import ReservoirSeismicityControl.PressureConcreteKernel
import Mathlib.Tactic

/-!
# M1 — Time-uniform local H² bootstrap for the signed reciprocal SR equation

For `s ∈ {-1,1}`, the variable `Y = exp(s*gamma1*u)/R` solves
`Y_t = -aY+b` with `a=gamma2*Rstar` and `b=gamma2*exp(s*gamma1*u)`.

The physical local-H² proof uses the following weak spatial equations:
  (∇Y)_t = -a∇Y + (∇b - Y∇a),
  (D²Y)_t = -aD²Y - 2 sym(∇a ⊗ ∇Y) - Y D²a + D²b.

The abstract theorem below proves the quantitative *uniform* derivative bounds
from the exact damped variation-of-constants estimates. Unlike a hypothesis
`sup_t ‖∇Y(t)‖ < ∞`, it only needs time-independent forcing estimates provided
by Assumptions 3 and 5 and the already-verified reciprocal box.

The Hilbert/Banach spaces `E₁` and `E₂` will be instantiated with the
appropriate first-derivative L⁶ and second-derivative L² spaces on U_j.
The representations here are written with the finite positive time-kernel
measure `ν(t) = aMin * exp(-aMin*(t-v)) 1_(0,t)(v) dv`; a spatially varying
damping coefficient is handled by absorbing the ratio of its actual
propagator to this majorizing exponential into the forcing terms.

THIS IS AN ANALYTIC BOOTSTRAP, NOT YET THE FINAL PHYSICAL H² THEOREM:
it remains to construct the weak spatial derivatives and prove their
variation-of-constants identities from the actual H² coefficients.  No
additional regularity on Qdot is assumed or used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Every exponentially damped Bochner convolution with a uniformly bounded
forcing has a *time-independent* bound. The kernel and its mass have already
been proved in the pressure branch; here we reuse them on arbitrary Banach
spaces.  The factor `aMin⁻¹` undoes the normalization of the measure. -/
theorem sr_damped_bochner_convolution_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (aMin t M : ℝ) (haMin : 0 < aMin) (ht : 0 ≤ t)
    (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
      ‖f v‖ ≤ M) :
    ‖aMin⁻¹ • (∫ v, f v ∂pressureExponentialKernelMeasure aMin t)‖ ≤
      M / aMin := by
  let ν := pressureExponentialKernelMeasure aMin t
  letI : IsFiniteMeasure ν :=
    pressure_exponential_kernel_measure_finite aMin t haMin.le ht
  have hMass : ν.real Set.univ ≤ 1 := by
    have hmassEq := pressure_exponential_kernel_measure_mass
      aMin t haMin.le ht
    have hExp : 0 ≤ Real.exp (-(aMin * t)) := (Real.exp_pos _).le
    dsimp only [ν]
    rw [hmassEq]
    linarith
  have hInt : ‖∫ v, f v ∂ν‖ ≤ M * ν.real Set.univ :=
    norm_integral_le_of_norm_le_const (μ := ν) hf
  have hBound : ‖∫ v, f v ∂ν‖ ≤ M :=
    hInt.trans (by nlinarith [mul_nonneg hM (sub_nonneg.mpr hMass)])
  calc
    ‖aMin⁻¹ • (∫ v, f v ∂ν)‖ = |aMin⁻¹| * ‖∫ v, f v ∂ν‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |aMin⁻¹| * M :=
      mul_le_mul_of_nonneg_left hBound (abs_nonneg _)
    _ = M / aMin := by
      rw [abs_of_pos (inv_pos.mpr haMin)]
      ring

/-- The uniform gradient and Hessian estimates in Appendix A.2.

Here `grad` and `hess` represent ∇Y and D²Y in L⁶ and L² respectively.
The right-hand sides reflect the *actual* spatial forcing terms:
  `‖∇b - Y∇a‖₆ ≤ B1 + Ymax*A1`, and
  `‖D²b - YD²a - 2 sym(∇a⊗∇Y)‖₂
     ≤ B2 + Ymax*A2 + 2*Cembed*A1*‖∇Y‖₆`.

`Cembed` is the L³-to-L² volume embedding factor `|U_j|^(1/6)`.
The time-dependent propagator has contraction bound `exp(-aMin*(t-v))`.
All such bounds can be obtained from the assumptions in Appendix A.2;
instantiating them with actual weak spatial derivatives is the next gate.
-/
theorem sr_signed_reciprocal_spatial_derivative_uniform_bounds
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    (aMin Ymax A1 B1 A2 B2 Cembed G0 H0 : ℝ)
    (haMin : 0 < aMin)
    (hYmax : 0 ≤ Ymax) (hA1 : 0 ≤ A1) (hB1 : 0 ≤ B1)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) (hC : 0 ≤ Cembed)
    (hG0 : 0 ≤ G0) (hH0 : 0 ≤ H0)
    (grad : ℝ → E₁) (hess : ℝ → E₂)
    (gradHom : ℝ → E₁) (hessHom : ℝ → E₂)
    (gradForcing : ℝ → ℝ → E₁) (hessForcing : ℝ → ℝ → E₂)
    (hgradHom : ∀ t, 0 ≤ t → ‖gradHom t‖ ≤ G0)
    (hhessHom : ∀ t, 0 ≤ t → ‖hessHom t‖ ≤ H0)
    (hgradDuhamel : ∀ t, 0 ≤ t →
      grad t = gradHom t + aMin⁻¹ •
        (∫ v, gradForcing t v ∂pressureExponentialKernelMeasure aMin t))
    (hhessDuhamel : ∀ t, 0 ≤ t →
      hess t = hessHom t + aMin⁻¹ •
        (∫ v, hessForcing t v ∂pressureExponentialKernelMeasure aMin t))
    (hgradForcing : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        ‖gradForcing t v‖ ≤ B1 + Ymax * A1)
    (hhessForcing : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        ‖hessForcing t v‖ ≤
          B2 + Ymax * A2 + 2 * Cembed * A1 * ‖grad v‖)
    /- The Hessian forcing at time v depends on `grad v`, not `grad t`.
       We therefore need the pointwise-in-time gradient bound in the
       integration window [0,t]. -/
    (hgradWindow : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        0 ≤ v) :
    let Gstar := G0 + (B1 + Ymax * A1) / aMin
    let Hstar := H0 +
      (B2 + Ymax * A2 + 2 * Cembed * A1 * Gstar) / aMin
    ∀ t, 0 ≤ t → ‖grad t‖ ≤ Gstar ∧ ‖hess t‖ ≤ Hstar := by
  dsimp
  let Gstar := G0 + (B1 + Ymax * A1) / aMin
  let Hforce := B2 + Ymax * A2 + 2 * Cembed * A1 * Gstar
  have hGforceNonneg : 0 ≤ B1 + Ymax * A1 := by positivity
  have hHforceNonneg : 0 ≤ Hforce := by
    dsimp [Hforce, Gstar]
    positivity
  have hGradBound : ∀ t, 0 ≤ t → ‖grad t‖ ≤ Gstar := by
    intro t ht
    have hInt := sr_damped_bochner_convolution_norm_le
      aMin t (B1 + Ymax * A1) haMin ht hGforceNonneg
      (gradForcing t) (hgradForcing t ht)
    calc
      ‖grad t‖ =
          ‖gradHom t + aMin⁻¹ •
            (∫ v, gradForcing t v ∂pressureExponentialKernelMeasure aMin t)‖ := by
            rw [hgradDuhamel t ht]
      _ ≤ ‖gradHom t‖ +
          ‖aMin⁻¹ •
            (∫ v, gradForcing t v ∂pressureExponentialKernelMeasure aMin t)‖ :=
          norm_add_le _ _
      _ ≤ G0 + (B1 + Ymax * A1) / aMin :=
          add_le_add (hgradHom t ht) hInt
  intro t ht
  constructor
  · exact hGradBound t ht
  · have hForcingBound :
        ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
          ‖hessForcing t v‖ ≤ Hforce := by
        filter_upwards [hhessForcing t ht, hgradWindow t ht]
          with v hv hvpos
        have hgradv : ‖grad v‖ ≤ Gstar := hGradBound v hvpos
        have hcoefficient : 0 ≤ 2 * Cembed * A1 := by positivity
        have hprod := mul_le_mul_of_nonneg_left hgradv hcoefficient
        dsimp only [Hforce]
        linarith
    have hInt := sr_damped_bochner_convolution_norm_le
      aMin t Hforce haMin ht hHforceNonneg
      (hessForcing t) hForcingBound
    calc
      ‖hess t‖ =
          ‖hessHom t + aMin⁻¹ •
            (∫ v, hessForcing t v ∂pressureExponentialKernelMeasure aMin t)‖ := by
            rw [hhessDuhamel t ht]
      _ ≤ ‖hessHom t‖ +
          ‖aMin⁻¹ •
            (∫ v, hessForcing t v ∂pressureExponentialKernelMeasure aMin t)‖ :=
          norm_add_le _ _
      _ ≤ H0 + Hforce / aMin :=
          add_le_add (hhessHom t ht) hInt

#print axioms ReservoirSeismicityControl.sr_damped_bochner_convolution_norm_le
#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_spatial_derivative_uniform_bounds

end ReservoirSeismicityControl
