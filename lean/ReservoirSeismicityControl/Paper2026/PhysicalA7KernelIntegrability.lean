import ReservoirSeismicityControl.Paper2026.PhysicalA7SobolevKernelApplication
import Mathlib.Tactic

/-!
# A7 physical H² kernel: discharge the Bochner-integrability gate

The already checked physical A7 application required `hInt` as a separate
hypothesis. But the actual forcing kernel is a product of the physical
H² coefficient representatives, and its polynomial-exponential bound was
proved in PhysicalA7SobolevKernelApplication. Since the time kernel measure
is finite, A7's `hInt` follows from *strong measurability* and that bound.

This does not assume H² regularity of the physical SR field. It also does
not silently assume weak-H² representatives of the *physical* coefficients,
the standard H² exponential calculus, or the L² Duhamel identification.
Those remain the explicit externally-cited applicability obligations.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- On each physical causal window, the uniform H² product and propagator
bounds imply Bochner integrability of the *actual product-form kernel*.
No extra `hInt` assumption is required.

`hKernelMeas` is the standard time-measurability input for the physical H²
representatives. `hWindow` is the support statement for the already-defined
exponential-kernel measure (not a new PDE assumption). -/
theorem physical_A7_actual_product_kernel_integrable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (prod : H → H → H)
    (gamma2H signedExpH : ℝ → H)
    (E : ℝ → ℝ → H)
    (m Cprod M2 Mexp E0 E1 E2 : ℝ)
    (hm : 0 < m) (hCprod : 0 ≤ Cprod)
    (hM2 : 0 ≤ M2) (hMexp : 0 ≤ Mexp)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hProd : ∀ a b, ‖prod a b‖ ≤ Cprod * ‖a‖ * ‖b‖)
    (hGamma2 : ∀ v, 0 ≤ v → ‖gamma2H v‖ ≤ M2)
    (hSignedExp : ∀ v, 0 ≤ v → ‖signedExpH v‖ ≤ Mexp)
    (hE : ∀ t v, 0 ≤ v → v ≤ t →
      ‖E t v‖ ≤
        (E0 + E1 * (t - v) + E2 * (t - v) ^ 2) *
          Real.exp (-(m * (t - v))))
    (hWindow : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t),
        0 ≤ v ∧ v ≤ t)
    (hKernelMeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable
        (fun v => prod (E t v)
          (prod (gamma2H v) (signedExpH v)))
        (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) :
    ∀ t, 0 ≤ t →
      Integrable
        (fun v => prod (E t v)
          (prod (gamma2H v) (signedExpH v)))
        (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t) := by
  intro t ht
  let MB : ℝ := Cprod * M2 * Mexp
  let C0 : ℝ := Cprod * MB * E0
  let C1 : ℝ := Cprod * MB * E1
  let C2 : ℝ := Cprod * MB * E2
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0, MB]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1, MB]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2, MB]; positivity
  have hB : ∀ v, 0 ≤ v →
      ‖prod (gamma2H v) (signedExpH v)‖ ≤ MB := by
    intro v hv
    calc
      ‖prod (gamma2H v) (signedExpH v)‖ ≤
          Cprod * ‖gamma2H v‖ * ‖signedExpH v‖ := hProd _ _
      _ ≤ Cprod * M2 * Mexp := by
        have hfirst : Cprod * ‖gamma2H v‖ ≤ Cprod * M2 :=
          mul_le_mul_of_nonneg_left (hGamma2 v hv) hCprod
        have hsecond : 0 ≤ Cprod * ‖gamma2H v‖ :=
          mul_nonneg hCprod (norm_nonneg _)
        calc
          Cprod * ‖gamma2H v‖ * ‖signedExpH v‖ ≤
              Cprod * ‖gamma2H v‖ * Mexp :=
            mul_le_mul_of_nonneg_left (hSignedExp v hv) hsecond
          _ ≤ Cprod * M2 * Mexp :=
            mul_le_mul_of_nonneg_right hfirst hMexp
      _ = MB := rfl
  letI : IsFiniteMeasure (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t) :=
    ReservoirSeismicityControl.pressure_exponential_kernel_measure_finite m t hm.le ht
  apply Integrable.of_bound (hKernelMeas t ht)
    (C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2)
  filter_upwards [hWindow t ht] with v hv
  have hlag : 0 ≤ t - v := sub_nonneg.mpr hv.2
  have hPoly :=
    physical_A7_product_kernel_polynomial_bound
      prod (E t v) (prod (gamma2H v) (signedExpH v))
      Cprod MB E0 E1 E2 m (t - v)
      hCprod hMB hE0 hE1 hE2 hlag hProd
      (hB v hv.1) (hE t v hv.1 hv.2)
  have hEnvelope := ReservoirSeismicityControl.sr_signed_half_damping_quadratic_envelope
    m (t - v) C0 C1 C2 hm hlag hC0 hC1 hC2
  exact hPoly.trans (by simpa only [C0, C1, C2] using hEnvelope)

#print axioms physical_A7_actual_product_kernel_integrable

end ReservoirSeismicityControl.Paper2026
