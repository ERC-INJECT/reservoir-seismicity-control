import ReservoirSeismicityControl.PressureMildModalBridge
import ReservoirSeismicityControl.PressureSpectralL2

/-!
# Appendix A.1: exponential modal convolution, positive measure version

For each nonnegative eigenvalue `lam` and nonnegative time `t`, the
convolution kernel `lam * exp (-lam * (t-s))` on `[0,t]` has the formal mass
`1 - exp (-lam*t)`, a number in `[0,1]`. We verify the scalar inequalities
for that mass and for the homogeneous exponential factor.

If a finite positive convolution measure has this mass, Stage 15's
subprobability lemma yields a bound on the averaged bounded well rates.
Combining this with Stage 22 gives a modal pressure-rate bound without
postulating separate estimates on the homogeneous part or averages.

The construction of the convolution measure from the exponential density,
its exact mass identity, and the mild/ODE identities for the physical Neumann
PDE are still assumptions. This is not yet a formal proof of the PDE.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- For nonnegative spectral eigenvalue and time, the mass of the stable
exponential kernel is between zero and one. The zero mode is allowed. -/
theorem pressure_exponential_mass_interval
    (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(lam * t)) ∧
      1 - Real.exp (-(lam * t)) ≤ 1 := by
  have harg : -(lam * t) ≤ 0 := by
    have hprod : 0 ≤ lam * t := mul_nonneg hlam ht
    linarith
  have hexp_le : Real.exp (-(lam * t)) ≤ 1 := by
    calc
      Real.exp (-(lam * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
      _ = 1 := Real.exp_zero
  have hexp_pos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  constructor <;> linarith

/-- The homogeneous spectral contribution is a contraction, for any
nonnegative eigenvalue including the Neumann zero eigenvalue. -/
theorem pressure_exponential_homogeneous_bound
    (lam t init : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    |Real.exp (-(lam * t)) * init| ≤ |init| := by
  have hexp_le : Real.exp (-(lam * t)) ≤ 1 := by
    have hmass := pressure_exponential_mass_interval lam t hlam ht
    linarith [hmass.1]
  calc
    |Real.exp (-(lam * t)) * init| =
        Real.exp (-(lam * t)) * |init| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * |init| := mul_le_mul_of_nonneg_right hexp_le (abs_nonneg init)
    _ = |init| := one_mul _

/-- A positive finite convolution measure whose total mass equals the
stable exponential-kernel mass maps essentially bounded inputs to outputs
with the same absolute bound. No time derivative of the input is assumed.
The mass identity for a concrete exponential-density measure is not proved
in this theorem. -/
theorem pressure_exponential_measure_average_bound
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (Q : ℝ → ℝ) (lam t M : ℝ)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (hM : 0 ≤ M)
    (hmass : ν.real Set.univ = 1 - Real.exp (-(lam * t)))
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M) :
    |∫ s, Q s ∂ν| ≤ M := by
  have hmass_le : ν.real Set.univ ≤ 1 := by
    rw [hmass]
    exact (pressure_exponential_mass_interval lam t hlam ht).2
  exact pressure_subprobability_integral_bound ν Q M hQ hM hmass_le

/-- For one fixed spectral mode, derive the pressure-rate bound from the
actual current well values, a positive modal averaging measure with the
exponential mass, and the mild/ODE identities. There is no standalone
hypothesis bounding the average or the homogeneous factor. -/
theorem pressure_mode_rate_from_exponential_measure
    {m : ℕ}
    (source qNow M : Fin m → ℝ)
    (Q : Fin m → ℝ → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (lam t mode init rate : ℝ)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hmass : ν.real Set.univ = 1 - Real.exp (-(lam * t)))
    (hQ : ∀ j : Fin m, ∀ᵐ s ∂ν, |Q j s| ≤ M j)
    (hNow : ∀ j : Fin m, |qNow j| ≤ M j)
    (hmild : lam * mode = Real.exp (-(lam * t)) * init +
      ∑ j : Fin m, source j * (∫ s, Q j s ∂ν))
    (hode : rate = -(lam * mode) +
      ∑ j : Fin m, source j * qNow j) :
    |rate| ≤ |init| + 2 * ∑ j : Fin m, M j * |source j| := by
  classical
  have hAverage : ∀ j : Fin m, |∫ s, Q j s ∂ν| ≤ M j := by
    intro j
    exact pressure_exponential_measure_average_bound
      ν (Q j) lam t (M j) hlam ht (hM j) hmass (hQ j)
  have hHom : |-(Real.exp (-(lam * t)) * init)| ≤ |init| := by
    rw [abs_neg]
    exact pressure_exponential_homogeneous_bound lam t init hlam ht
  have hMild' : lam * mode =
      -(-(Real.exp (-(lam * t)) * init)) +
        ∑ j : Fin m, source j * (∫ s, Q j s ∂ν) := by
    simpa only [neg_neg] using hmild
  exact pressure_mode_bound_from_mild_and_ode
    source qNow (fun j => ∫ s, Q j s ∂ν) M
    lam mode (-(Real.exp (-(lam * t)) * init)) init rate
    hNow hAverage hHom hMild' hode

end ReservoirSeismicityControl
