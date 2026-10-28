import ReservoirSeismicityControl.PressureExponentialMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Appendix A.1: the concrete exponential convolution measure

For `lam ≥ 0` and `t ≥ 0`, define the positive measure

  ν_{lam,t}(ds) = 1_{(0,t]}(s) lam * exp (-lam * (t-s)) ds.

The results below calculate the mass by the fundamental theorem of calculus,
prove that the measure is finite, and use the result in the Stage 23 modal
rate estimate. No bounded time derivative of a well rate is needed.

IMPORTANT: the eigenbasis/Neumann diffusion representation and the scalar
mild and ODE identities are still hypotheses, not consequences of this file.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The real density of the scalar modal exponential convolution. -/
private noncomputable def pressureKernel (lam t s : ℝ) : ℝ :=
  lam * Real.exp (-(lam * (t - s)))

private theorem pressureKernel_nonneg (lam t s : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ pressureKernel lam t s := by
  unfold pressureKernel
  exact mul_nonneg hlam (le_of_lt (Real.exp_pos _))

private theorem pressureKernel_continuous (lam t : ℝ) :
    Continuous (pressureKernel lam t) := by
  unfold pressureKernel
  fun_prop

/-- The weighted exponential is the time derivative of its antiderivative. -/
private theorem pressureKernel_hasDerivAt (lam t s : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (-(lam * (t - z))))
      (pressureKernel lam t s) s := by
  have hinner : HasDerivAt (fun z : ℝ => -(lam * (t - z))) lam s := by
    convert ((hasDerivAt_id s).const_sub t).const_mul (-lam) using 1
    · funext z
      dsimp [Function.comp_def]
      ring
    · ring
  have hcomp : HasDerivAt
      (fun z : ℝ => Real.exp (-(lam * (t - z))))
      (Real.exp (-(lam * (t - s))) * lam) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp _).comp s hinner
  convert hcomp using 1
  unfold pressureKernel
  ring

/-- Exact integral of the actual exponential convolution kernel. -/
theorem pressure_kernel_integral_mass
    (lam t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s)))) =
      1 - Real.exp (-(lam * t)) := by
  have hint : IntervalIntegrable (pressureKernel lam t) volume 0 t :=
    (pressureKernel_continuous lam t).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun z : ℝ => Real.exp (-(lam * (t - z))))
    (f' := pressureKernel lam t)
    (a := (0 : ℝ)) (b := t)
    (fun s _ => pressureKernel_hasDerivAt lam t s) hint
  change (∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s)))) =
    Real.exp (-(lam * (t - t))) - Real.exp (-(lam * (t - 0))) at h
  simpa only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero] using h

/-- The positive measure obtained by restricting Lebesgue measure to the past
interval and weighting it with the actual exponential kernel. -/
noncomputable def pressureExponentialKernelMeasure (lam t : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 t)).withDensity
    (fun s => ENNReal.ofReal (pressureKernel lam t s))

/-- Exact total mass as an extended nonnegative real number. This form is
used before finiteness is established, avoiding `toReal ∞ = 0` issues. -/
theorem pressure_exponential_kernel_measure_mass_ennreal
    (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    pressureExponentialKernelMeasure lam t Set.univ =
      ENNReal.ofReal (1 - Real.exp (-(lam * t))) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc 0 t)
  have hint : Integrable (pressureKernel lam t) μ := by
    exact ((pressureKernel_continuous lam t).intervalIntegrable (0 : ℝ) t).1
  have hnonneg : ∀ᵐ s ∂μ, 0 ≤ pressureKernel lam t s :=
    Filter.Eventually.of_forall (fun s => pressureKernel_nonneg lam t s hlam)
  have hlin :
      (∫⁻ s, ENNReal.ofReal (pressureKernel lam t s) ∂μ) =
        ENNReal.ofReal (∫ s, pressureKernel lam t s ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  calc
    pressureExponentialKernelMeasure lam t Set.univ =
        ∫⁻ s, ENNReal.ofReal (pressureKernel lam t s) ∂μ := by
      simp only [pressureExponentialKernelMeasure, μ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ENNReal.ofReal (∫ s, pressureKernel lam t s ∂μ) := hlin
    _ = ENNReal.ofReal (∫ s in (0 : ℝ)..t, pressureKernel lam t s) := by
      rw [intervalIntegral.integral_of_le ht]
    _ = ENNReal.ofReal (1 - Real.exp (-(lam * t))) := by
      congr 1
      exact pressure_kernel_integral_mass lam t ht

/-- The concrete convolution measure is finite, including for zero modes. -/
theorem pressure_exponential_kernel_measure_finite
    (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    IsFiniteMeasure (pressureExponentialKernelMeasure lam t) := by
  refine ⟨?_⟩
  rw [pressure_exponential_kernel_measure_mass_ennreal lam t hlam ht]
  exact ENNReal.ofReal_lt_top

/-- Exact finite real mass of the concrete convolution measure. -/
theorem pressure_exponential_kernel_measure_mass
    (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (pressureExponentialKernelMeasure lam t).real Set.univ =
      1 - Real.exp (-(lam * t)) := by
  rw [measureReal_def,
    pressure_exponential_kernel_measure_mass_ennreal lam t hlam ht]
  exact ENNReal.toReal_ofReal (pressure_exponential_mass_interval lam t hlam ht).1

/-- Stage 23's modal estimate, now using the genuine exponential-density
measure and its proved mass. The mild and ODE identities remain assumptions. -/
theorem pressure_mode_rate_from_concrete_kernel
    {m : ℕ} (source qNow M : Fin m → ℝ)
    (Q : Fin m → ℝ → ℝ)
    (lam t mode init rate : ℝ)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hQ : ∀ j : Fin m, ∀ s : ℝ, |Q j s| ≤ M j)
    (hNow : ∀ j : Fin m, |qNow j| ≤ M j)
    (hmild : lam * mode = Real.exp (-(lam * t)) * init +
      ∑ j : Fin m, source j *
        (∫ s, Q j s ∂pressureExponentialKernelMeasure lam t))
    (hode : rate = -(lam * mode) +
      ∑ j : Fin m, source j * qNow j) :
    |rate| ≤ |init| + 2 * ∑ j : Fin m, M j * |source j| := by
  letI : IsFiniteMeasure (pressureExponentialKernelMeasure lam t) :=
    pressure_exponential_kernel_measure_finite lam t hlam ht
  apply pressure_mode_rate_from_exponential_measure
    source qNow M Q (pressureExponentialKernelMeasure lam t)
    lam t mode init rate hlam ht hM
    (pressure_exponential_kernel_measure_mass lam t hlam ht)
    (fun j => Filter.Eventually.of_forall (hQ j))
    hNow hmild hode

end ReservoirSeismicityControl
