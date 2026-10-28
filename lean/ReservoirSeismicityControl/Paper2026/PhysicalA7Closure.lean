import ReservoirSeismicityControl.SeismicitySignedPhysicalH2HalfDamping
import ReservoirSeismicityControl.SeismicityPhysicalL2RateBridge
import Mathlib.Tactic

/-!
# Paper A.2 (A7): final signed SR Sobolev reconstruction from the EXISTING H² kernel

This module adds only the paper-specific final assembly: the prior polynomial
kernel theorem constructs an H² reciprocal representative from its actual
Duhamel terms, and the paper's external standard positive Sobolev quotient
calculus recovers R = exp(s gamma1 u)/Y. The previously proved physical
L²-rate theorem supplies the independent time-derivative bound.

Scope / honesty:
* `H` must be instantiated with the genuine H²(U_j) Sobolev space; the map
  `embed` is its continuous embedding into L²(U_j).
* `sobolevQuotient` and `hQuotientRep` / `hQuotientBound` are the EXTERNAL
  standard bounded-domain Sobolev calculus applied to exp(s gamma1 u)/Y.
  In particular, they are NOT a hypothesis that R already belongs to H².
* `hom`, `kernel`, `hHomPolynomial`, `hKernelPolynomial`, `hInt`, and
  `hPhysicalDuhamel` must still be instantiated with the real physical
  coefficients a = gamma2 * Rstar, b = gamma2 * exp(s gamma1 * u).
  Existing 3D weak kernel calculations provide intermediate tools, but this
  genuine coefficient-to-kernel Sobolev construction is NOT yet discharged.
* The `Kpressure` and reaction premises are the physical strong L² SR ODE
  and its already established uniform coefficients, not a premise on Rdot.

This is an honest **conditional physical A7 closure**, not yet a proof of A7
solely from Assumptions 1--5. It contains no `sorry`, custom `axiom` or
assumption that the conclusion of A7 already holds.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Physical (A7) assembly. Every kernel integral and damping moment bound
is provided by `sr_signed_physical_reciprocal_H2_from_polynomial_kernel`;
the L² rate is provided by `sr_rate_L2_from_pressure_ae`. The ONLY nonlinear
spatial calculus input is the cited local positive H² quotient rule, encoded
as an operation acting on an H² reciprocal (rather than assuming R ∈ H²).

`m` is half the coercive damping coefficient; all upper-bound constants are
spatial-uniform and independent of observation time. -/
theorem paper_A7_signed_physical_H2_and_L2_rate_from_existing_kernel
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X)
    (embed : H →L[ℝ] Lp ℝ 2 μ)
    (m D0 D1 D2 C0 C1 C2 : ℝ)
    (hm : 0 < m)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (Yphysical Rphysical : ℝ → Lp ℝ 2 μ)
    (hom : ℝ → H) (kernel : ℝ → ℝ → H)
    (hHomPolynomial : ∀ t, 0 ≤ t →
      ‖hom t‖ ≤ (D0 + D1 * t + D2 * t ^ 2) * Real.exp (-(m * t)))
    (hKernelPolynomial : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure m t,
        ‖kernel t v‖ ≤
          (C0 + C1 * max (t - v) 0 + C2 * (max (t - v) 0) ^ 2) *
            Real.exp (-(m * max (t - v) 0)))
    (hInt : ∀ t, 0 ≤ t →
      Integrable (kernel t) (pressureExponentialKernelMeasure m t))
    (hPhysicalDuhamel : ∀ t, 0 ≤ t →
      Yphysical t = embed (hom t) + m⁻¹ •
        (∫ v, embed (kernel t v)
          ∂pressureExponentialKernelMeasure m t))
    /- The following are the *standard external* local H² composition and
       bounded-positive inverse/quotient properties, with explicit growth.
       They require a lower bound on the physical Y and a bounded H²
       numerator exp(s gamma1 u); neither asserts a bound on R ∈ H². -/
    (sobolevQuotient : ℝ → H → H)
    (Cquot : ℝ) (hCquot : 0 ≤ Cquot)
    (hQuotientRep : ∀ t, 0 ≤ t → ∀ y : H,
      embed y = Yphysical t →
        embed (sobolevQuotient t y) = Rphysical t)
    (hQuotientBound : ∀ t, 0 ≤ t → ∀ y : H,
      embed y = Yphysical t →
        ‖sobolevQuotient t y‖ ≤
          Cquot * (1 + ‖y‖ + ‖y‖ ^ 2))
    (Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (Kpressure : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cmult CU Creact : ℝ)
    (hK : ∀ᵐ t ∂paperPositiveTime, ‖Kpressure t‖ ≤ Cmult)
    (hU : ∀ᵐ t ∂paperPositiveTime, ‖Udot t‖ ≤ CU)
    (hreaction : ∀ᵐ t ∂paperPositiveTime, ‖reaction t‖ ≤ Creact)
    (hPhysicalODE : ∀ᵐ t ∂paperPositiveTime,
      Rdot t = -(Kpressure t (Udot t)) - reaction t) :
    let Ybound : ℝ :=
      (D0 + D1 * m⁻¹ + D2 * ((m / 2)⁻¹) ^ 2) +
      (C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2) / m
    (∀ t : ℝ, 0 ≤ t → ∃ R_H2 : H,
      embed R_H2 = Rphysical t ∧
      ‖R_H2‖ ≤ Cquot * (1 + Ybound + Ybound ^ 2)) ∧
    (∀ᵐ t ∂paperPositiveTime,
      ‖Rdot t‖ ≤ Cmult * CU + Creact) := by
  dsimp
  let Ybound : ℝ :=
    (D0 + D1 * m⁻¹ + D2 * ((m / 2)⁻¹) ^ 2) +
    (C0 + C1 * m⁻¹ + C2 * ((m / 2)⁻¹) ^ 2) / m
  have hY : ∀ t : ℝ, 0 ≤ t → ∃ y : H,
      embed y = Yphysical t ∧ ‖y‖ ≤ Ybound :=
    sr_signed_physical_reciprocal_H2_from_polynomial_kernel
      embed m D0 D1 D2 C0 C1 C2 hm
      hD0 hD1 hD2 hC0 hC1 hC2
      Yphysical hom kernel hHomPolynomial hKernelPolynomial
      hInt hPhysicalDuhamel
  constructor
  · intro t ht
    obtain ⟨y, hyRep, hyBound⟩ := hY t ht
    refine ⟨sobolevQuotient t y, hQuotientRep t ht y hyRep, ?_⟩
    have hYnonneg : 0 ≤ ‖y‖ := norm_nonneg y
    have hYboundNonneg : 0 ≤ Ybound := le_trans hYnonneg hyBound
    have hgrowth :
        1 + ‖y‖ + ‖y‖ ^ 2 ≤ 1 + Ybound + Ybound ^ 2 := by
      have hmul := mul_nonneg (sub_nonneg.mpr hyBound)
        (add_nonneg hYnonneg hYboundNonneg)
      nlinarith
    exact (hQuotientBound t ht y hyRep).trans
      (mul_le_mul_of_nonneg_left hgrowth hCquot)
  · exact sr_rate_L2_from_pressure_ae μ Udot Rdot reaction Kpressure
      Cmult CU Creact hK hU hreaction hPhysicalODE

#print axioms ReservoirSeismicityControl.paper_A7_signed_physical_H2_and_L2_rate_from_existing_kernel

end ReservoirSeismicityControl
