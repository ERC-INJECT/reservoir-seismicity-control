import ReservoirSeismicityControl.Paper2026.PhysicalA7Closure
import ReservoirSeismicityControl.Paper2026.PhysicalA7CoefficientDamping
import Mathlib.Tactic

/-!
# A.2 (A7): physical Sobolev multiplier -> reciprocal kernel -> SR bounds

This specializes the **existing** reciprocal H² and L²-rate theorems.  It
constructs the homogeneous term and the causal kernel by multiplying the
H²-representative of the **half-damped residual** propagator by the H²
forcing. The homogeneous term includes the removed half-damping factor. Their polynomial/exponential estimates are derived
from the standard bounded-domain Sobolev product bound and the standard
H² exponential-composition estimate; they are NOT separate kernel premises.

The external analysis still needed to instantiate the statement is precise:
  * H is the actual H²(U_j) with its standard product map `prod`;
  * `E t v` is the H² class of
      exp(m*(t-v)) * exp(-∫_v^t gamma2 Rstar), with m=a_min/2.
    The positive convolution measure already contains exp(-m*(t-v));
    using the unmodified propagator here would double-count damping.
    The bound `hE` follows from cited H² composition/chain calculus;
  * gamma2 and exp(s gamma1 u) have the uniform H² representatives
    `gamma2H`, `signedExpH` from A3/A4 and cited standard H² calculus;
  * `hInt` is the H²-valued Bochner measurability/integrability of the
    actual kernel, and `hPhysicalDuhamel` identifies the L² representative
    with the physically constructed solution of (A6);
  * `hQuotientRep` and `hQuotientBound` are the cited positive H² inverse
    and product rules applied to the physical initial SR box.

In particular the final theorem is STILL CONDITIONAL until these exact
physical applications of external Sobolev facts are certified.  It does not
assume (A7), nor create new generic diffusion or Sobolev lemmas.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- For a fixed causal lag, the H² product bound and the standard H²
exponential-propagator estimate imply the correct *quadratic* kernel
estimate, including its decaying exponential. -/
theorem physical_A7_product_kernel_polynomial_bound
    {H : Type*} [NormedAddCommGroup H]
    (prod : H → H → H) (E B : H)
    (Cprod M_B E0 E1 E2 m tau : ℝ)
    (hCprod : 0 ≤ Cprod) (hMB : 0 ≤ M_B)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (htau : 0 ≤ tau)
    (hProd : ∀ a b, ‖prod a b‖ ≤ Cprod * ‖a‖ * ‖b‖)
    (hB : ‖B‖ ≤ M_B)
    (hE : ‖E‖ ≤ (E0 + E1 * tau + E2 * tau ^ 2) *
      Real.exp (-(m * tau))) :
    ‖prod E B‖ ≤
      (Cprod * M_B * E0 + Cprod * M_B * E1 * tau +
        Cprod * M_B * E2 * tau ^ 2) * Real.exp (-(m * tau)) := by
  have hCEnonneg : 0 ≤ Cprod * ‖E‖ :=
    mul_nonneg hCprod (norm_nonneg _)
  calc
    ‖prod E B‖ ≤ Cprod * ‖E‖ * ‖B‖ := hProd E B
    _ ≤ Cprod * ‖E‖ * M_B :=
      mul_le_mul_of_nonneg_left hB hCEnonneg
    _ ≤ Cprod * ((E0 + E1 * tau + E2 * tau ^ 2) *
        Real.exp (-(m * tau))) * M_B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE hCprod) hMB
    _ = (Cprod * M_B * E0 + Cprod * M_B * E1 * tau +
        Cprod * M_B * E2 * tau ^ 2) * Real.exp (-(m * tau)) := by ring

/-- **Physical A7 application certificate.** Unlike the earlier generic
closure, neither the homogeneous nor the inhomogeneous polynomial H²
kernel bounds are supplied as hypotheses: both follow from the external
standard *exponential* H² estimate and the H² product inequality.

`gamma2H` and `signedExpH` are the actual H² coefficient representatives
in Appendix A.2. Their uniform H² bounds and the H² exponential estimate
are the remaining cited-Sobolev applicability conditions. -/
theorem physical_A7_from_actual_H2_coefficient_multipliers
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X)
    (embed : H →L[ℝ] Lp ℝ 2 μ)
    (prod : H → H → H)
    (gamma2H signedExpH : ℝ → H)
    (E : ℝ → ℝ → H) (Y0 : H)
    (Yphysical Rphysical : ℝ → Lp ℝ 2 μ)
    (m Cprod M2 Mexp MY0 E0 E1 E2 : ℝ)
    (hm : 0 < m) (hCprod : 0 ≤ Cprod)
    (hM2 : 0 ≤ M2) (hMexp : 0 ≤ Mexp) (hMY0 : 0 ≤ MY0)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    /- The H² Banach-algebra multiplication is standard external theory,
       not a new PDE hypothesis or a bound on the conclusion R. -/
    (hProd : ∀ a b, ‖prod a b‖ ≤ Cprod * ‖a‖ * ‖b‖)
    (hGamma2 : ∀ v, 0 ≤ v → ‖gamma2H v‖ ≤ M2)
    (hSignedExp : ∀ v, 0 ≤ v → ‖signedExpH v‖ ≤ Mexp)
    (hY0 : ‖Y0‖ ≤ MY0)
    /- E represents exp(m*(t-v))*exp(-∫_v^t a), a=gamma2*Rstar.
       The convolution measure supplies the complementary exp(-m*lag).
       Thus the true exponential propagator is recovered, rather than
       incorrectly multiplying it by another damping factor.
       The bound follows from standard weak H² calculus and a≥2m. -/
    (hE : ∀ t v, 0 ≤ v → v ≤ t →
      ‖E t v‖ ≤
        (E0 + E1 * (t - v) + E2 * (t - v) ^ 2) *
          Real.exp (-(m * (t - v))))
    (hWindow : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t),
        0 ≤ v ∧ v ≤ t)
    /- Bochner measurability and the pointwise/L² physical Duhamel
       identification are not automatic from coefficient norm bounds. -/
    (hInt : ∀ t, 0 ≤ t →
      Integrable (fun v => prod (E t v)
        (prod (gamma2H v) (signedExpH v)))
        (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t))
    (hPhysicalDuhamel : ∀ t, 0 ≤ t →
      Yphysical t = embed (Real.exp (-(m * t)) • prod (E t 0) Y0) + m⁻¹ •
        (∫ v, embed (prod (E t v)
          (prod (gamma2H v) (signedExpH v)))
          ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)))
    /- Standard external positive H² quotient calculus, not an H²(R)
       assumption; see PhysicalA7Closure.lean. -/
    (sobolevQuotient : ℝ → H → H)
    (Cquot : ℝ) (hCquot : 0 ≤ Cquot)
    (hQuotientRep : ∀ t, 0 ≤ t → ∀ y : H,
      embed y = Yphysical t →
        embed (sobolevQuotient t y) = Rphysical t)
    (hQuotientBound : ∀ t, 0 ≤ t → ∀ y : H,
      embed y = Yphysical t →
        ‖sobolevQuotient t y‖ ≤ Cquot * (1 + ‖y‖ + ‖y‖ ^ 2))
    /- Reuse the existing, independently proved physical L² SR rate. -/
    (Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (Kpressure : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cmult CU Creact : ℝ)
    (hK : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Kpressure t‖ ≤ Cmult)
    (hU : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Udot t‖ ≤ CU)
    (hreaction : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖reaction t‖ ≤ Creact)
    (hPhysicalODE : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Rdot t = -(Kpressure t (Udot t)) - reaction t) :
    let D0 := Cprod * MY0 * E0
    let D1 := Cprod * MY0 * E1
    let D2 := Cprod * MY0 * E2
    let MB := Cprod * M2 * Mexp
    let C0 := Cprod * MB * E0
    let C1 := Cprod * MB * E1
    let C2 := Cprod * MB * E2
    let Ybound :=
      (D0 + D1 * m⁻¹ + D2 * ((m / 2)⁻¹) ^ 2) +
      (C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2) / m
    (∀ t : ℝ, 0 ≤ t → ∃ R_H2 : H,
      embed R_H2 = Rphysical t ∧
      ‖R_H2‖ ≤ Cquot * (1 + Ybound + Ybound ^ 2)) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ Cmult * CU + Creact) := by
  dsimp
  let MB : ℝ := Cprod * M2 * Mexp
  let D0 : ℝ := Cprod * MY0 * E0
  let D1 : ℝ := Cprod * MY0 * E1
  let D2 : ℝ := Cprod * MY0 * E2
  let C0 : ℝ := Cprod * MB * E0
  let C1 : ℝ := Cprod * MB * E1
  let C2 : ℝ := Cprod * MB * E2
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hD0 : 0 ≤ D0 := by dsimp [D0]; positivity
  have hD1 : 0 ≤ D1 := by dsimp [D1]; positivity
  have hD2 : 0 ≤ D2 := by dsimp [D2]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
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
  have hHom : ∀ t, 0 ≤ t →
      ‖Real.exp (-(m * t)) • prod (E t 0) Y0‖ ≤
        (D0 + D1 * t + D2 * t ^ 2) * Real.exp (-(m * t)) := by
    intro t ht
    have h := physical_A7_product_kernel_polynomial_bound
      prod (E t 0) Y0 Cprod MY0 E0 E1 E2 m t
      hCprod hMY0 hE0 hE1 hE2 ht hProd hY0
      (by simpa using hE t 0 (le_refl 0) ht)
    have hDecay : Real.exp (-(m * t)) ≤ 1 := by
      calc
        Real.exp (-(m * t)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (le_of_lt hm) ht])
        _ = 1 := Real.exp_zero
    have hSmulNorm :
        ‖Real.exp (-(m * t)) • prod (E t 0) Y0‖ =
          Real.exp (-(m * t)) * ‖prod (E t 0) Y0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ‖Real.exp (-(m * t)) • prod (E t 0) Y0‖ =
          Real.exp (-(m * t)) * ‖prod (E t 0) Y0‖ := hSmulNorm
      _ ≤ 1 * ‖prod (E t 0) Y0‖ :=
        mul_le_mul_of_nonneg_right hDecay (norm_nonneg _)
      _ = ‖prod (E t 0) Y0‖ := one_mul _
      _ ≤ (D0 + D1 * t + D2 * t ^ 2) * Real.exp (-(m * t)) := by
        simpa only [D0, D1, D2] using h
  have hKernel : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t),
      ‖prod (E t v) (prod (gamma2H v) (signedExpH v))‖ ≤
        (C0 + C1 * max (t - v) 0 + C2 * (max (t - v) 0) ^ 2) *
          Real.exp (-(m * max (t - v) 0)) := by
    intro t ht
    filter_upwards [hWindow t ht] with v hv
    have htv : 0 ≤ t - v := sub_nonneg.mpr hv.2
    have h := physical_A7_product_kernel_polynomial_bound
      prod (E t v) (prod (gamma2H v) (signedExpH v))
      Cprod MB E0 E1 E2 m (t - v)
      hCprod hMB hE0 hE1 hE2 htv hProd (hB v hv.1)
      (hE t v hv.1 hv.2)
    simpa only [C0, C1, C2, max_eq_left htv] using h
  exact ReservoirSeismicityControl.paper_A7_signed_physical_H2_and_L2_rate_from_existing_kernel
    μ embed m D0 D1 D2 C0 C1 C2 hm
    hD0 hD1 hD2 hC0 hC1 hC2
    Yphysical Rphysical
    (fun t => Real.exp (-(m * t)) • prod (E t 0) Y0)
    (fun t v => prod (E t v)
      (prod (gamma2H v) (signedExpH v)))
    hHom hKernel hInt hPhysicalDuhamel
    sobolevQuotient Cquot hCquot hQuotientRep hQuotientBound
    Udot Rdot reaction Kpressure Cmult CU Creact
    hK hU hreaction hPhysicalODE

#print axioms physical_A7_product_kernel_polynomial_bound
#print axioms physical_A7_from_actual_H2_coefficient_multipliers

end ReservoirSeismicityControl.Paper2026
