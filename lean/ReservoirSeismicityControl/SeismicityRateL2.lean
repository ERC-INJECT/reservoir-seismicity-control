import ReservoirSeismicityControl.WellMeanDerivative

/-!
# SR rate estimates from the logistic PDE--ODE right-hand side

In the ReservoirSeismicityControl manuscript,
  R_t = -(γ₁ R) u_t - γ₂ R (R - R*).

First we give algebraic pointwise bounds using the actual coefficients.
Next we work in a real L² space and write this equation as
  Rdot(t) = -(K(t) (Udot(t))) - reaction(t),
where K(t) is a bounded multiplication operator. We prove a uniform L²
bound for Rdot and use the already-verified well-average derivative theorem.

The assumptions on the operator norm of K and the L² norm of the reaction
must still be derived from pointwise coefficient bounds in the specific
reservoir measure space. The existence and strong L² differentiability of
R, and the bounded L² pressure rate u_t, are also separate PDE obligations.
This file does not assume bounded Qdot.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A pointwise bound for the pressure-to-SR coefficient `γ₁ R`. -/
theorem sr_pressure_multiplier_pointwise_bound
    (γ₁ R γmax Rmax : ℝ)
    (hγ : |γ₁| ≤ γmax)
    (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax) :
    |γ₁ * R| ≤ γmax * Rmax := by
  rw [abs_mul, abs_of_nonneg hR0]
  exact (mul_le_mul_of_nonneg_right hγ hR0).trans
    (mul_le_mul_of_nonneg_left hRmax
      (le_trans (abs_nonneg γ₁) hγ))

/-- A pointwise bound for the logistic reaction `γ₂ R (R - R*)`. -/
theorem sr_reaction_pointwise_bound
    (γ₂ R Rstar γ2max Rmax RstarMax : ℝ)
    (hγ₂ : |γ₂| ≤ γ2max)
    (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax)
    (hRstar0 : 0 ≤ Rstar) (hRstarMax : Rstar ≤ RstarMax) :
    |γ₂ * R * (R - Rstar)| ≤
      γ2max * Rmax * (Rmax + RstarMax) := by
  have hγ2nonneg : 0 ≤ γ2max := (abs_nonneg γ₂).trans hγ₂
  have hRmax0 : 0 ≤ Rmax := hR0.trans hRmax
  have hdelta : |R - Rstar| ≤ Rmax + RstarMax := by
    apply abs_le.mpr
    constructor <;> linarith
  have hmul : |γ₂| * R ≤ γ2max * Rmax :=
    (mul_le_mul_of_nonneg_right hγ₂ hR0).trans
      (mul_le_mul_of_nonneg_left hRmax hγ2nonneg)
  calc
    |γ₂ * R * (R - Rstar)| = |γ₂| * R * |R - Rstar| := by
      simp [abs_mul, abs_of_nonneg hR0]
    _ ≤ γ2max * Rmax * |R - Rstar| :=
      mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
    _ ≤ γ2max * Rmax * (Rmax + RstarMax) :=
      mul_le_mul_of_nonneg_left hdelta
        (mul_nonneg hγ2nonneg hRmax0)

/-- Absolute bound for the actual pointwise SR ODE right-hand side. -/
theorem sr_rate_pointwise_bound
    (γ₁ γ₂ R Rstar ut Rt γmax γ2max Rmax RstarMax : ℝ)
    (hγ₁ : |γ₁| ≤ γmax) (hγ₂ : |γ₂| ≤ γ2max)
    (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax)
    (hRstar0 : 0 ≤ Rstar) (hRstarMax : Rstar ≤ RstarMax)
    (hODE : Rt = -γ₁ * R * ut - γ₂ * R * (R - Rstar)) :
    |Rt| ≤ γmax * Rmax * |ut| +
      γ2max * Rmax * (Rmax + RstarMax) := by
  have hpressure : |γ₁ * R| ≤ γmax * Rmax :=
    sr_pressure_multiplier_pointwise_bound γ₁ R γmax Rmax hγ₁ hR0 hRmax
  have hreact : |γ₂ * R * (R - Rstar)| ≤
      γ2max * Rmax * (Rmax + RstarMax) :=
    sr_reaction_pointwise_bound γ₂ R Rstar γ2max Rmax RstarMax
      hγ₂ hR0 hRmax hRstar0 hRstarMax
  calc
    |Rt| = |(-γ₁ * R * ut) + -(γ₂ * R * (R - Rstar))| := by
      rw [hODE]
      ring_nf
    _ ≤ |-γ₁ * R * ut| + |-(γ₂ * R * (R - Rstar))| :=
      abs_add_le _ _
    _ = |γ₁ * R| * |ut| + |γ₂ * R * (R - Rstar)| := by
      simp only [abs_neg, abs_mul]
    _ ≤ γmax * Rmax * |ut| +
        γ2max * Rmax * (Rmax + RstarMax) :=
      add_le_add (mul_le_mul_of_nonneg_right hpressure (abs_nonneg _)) hreact

/-- The logistic SR equation and uniform bounds on the pressure rate,
coefficient multiplication, and reaction imply a uniform L² SR-rate bound.
The coefficient operator is *intended* to be multiplication by `γ₁ R`.
This theorem treats its operator-norm bound as a hypothesis. -/
theorem sr_rate_L2_from_pressure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (K : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cmult CU Creact : ℝ)
    (hK : ∀ t : ℝ, 0 ≤ t → ‖K t‖ ≤ Cmult)
    (hU : ∀ t : ℝ, 0 ≤ t → ‖Udot t‖ ≤ CU)
    (hreaction : ∀ t : ℝ, 0 ≤ t → ‖reaction t‖ ≤ Creact)
    (hODE : ∀ t : ℝ, 0 ≤ t →
      Rdot t = -(K t (Udot t)) - reaction t) :
    ∀ t : ℝ, 0 ≤ t → ‖Rdot t‖ ≤ Cmult * CU + Creact := by
  intro t ht
  have hCU : 0 ≤ CU := (norm_nonneg (Udot t)).trans (hU t ht)
  calc
    ‖Rdot t‖ = ‖-(K t (Udot t)) - reaction t‖ := by
      rw [hODE t ht]
    _ = ‖-(K t (Udot t)) + -reaction t‖ := by
      rw [sub_eq_add_neg]
    _ ≤ ‖-(K t (Udot t))‖ + ‖-reaction t‖ := norm_add_le _ _
    _ = ‖K t (Udot t)‖ + ‖reaction t‖ := by rw [norm_neg, norm_neg]
    _ ≤ ‖K t‖ * ‖Udot t‖ + ‖reaction t‖ :=
      add_le_add ((K t).le_opNorm (Udot t)) (le_refl _)
    _ ≤ ‖K t‖ * CU + ‖reaction t‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hU t ht) (norm_nonneg (K t))) (le_refl _)
    _ ≤ Cmult * CU + ‖reaction t‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (hK t ht) hCU) (le_refl _)
    _ ≤ Cmult * CU + Creact :=
      add_le_add (le_refl _) (hreaction t ht)

/-- From the same logistic equation bounds and strong L² differentiability
of the SR state, the derivative of each normalized well average is bounded.
No pointwise bound on `u_t` or `R_t` is used. -/
theorem sr_well_mean_derivative_from_pressure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (R Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (K : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cmult CU Creact : ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt R (Rdot t) t)
    (hK : ∀ t : ℝ, 0 ≤ t → ‖K t‖ ≤ Cmult)
    (hU : ∀ t : ℝ, 0 ≤ t → ‖Udot t‖ ≤ CU)
    (hreaction : ∀ t : ℝ, 0 ≤ t → ‖reaction t‖ ≤ Creact)
    (hODE : ∀ t : ℝ, 0 ≤ t →
      Rdot t = -(K t (Udot t)) - reaction t) :
    ∀ t : ℝ, 0 ≤ t →
      |deriv (fun τ => wellMeanL2 μ s hs hfinite (R τ)) t| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) *
          (Cmult * CU + Creact)) / μ.real s := by
  exact well_mean_L2_deriv_uniform μ s hs hfinite hpositive R Rdot
    (Cmult * CU + Creact) hderiv
    (sr_rate_L2_from_pressure μ Udot Rdot reaction K
      Cmult CU Creact hK hU hreaction hODE)

end ReservoirSeismicityControl
