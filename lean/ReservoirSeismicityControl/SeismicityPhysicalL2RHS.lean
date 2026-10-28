import ReservoirSeismicityControl.SeismicityPhysicalL2Multiplier
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1: physical L² reaction and the complete SR right-hand side

The pressure multiplier by γ₁ R was already proved in
`SeismicityPhysicalL2Multiplier`. This module constructs the *other*
physical multiplier, γ₂ (R - R*), and combines the two into the actual
L² spatial SR right-hand side.

The pointwise physical SR ODE is used as a spatial a.e. identity at a
fixed time. Thus the theorem does not assume a bound on the L² SR rate
or an abstract coefficient operator. It does NOT establish that a
Carathéodory SR solution has this strong L² derivative at a.e. time,
nor does it prove local H² regularity. Those remain genuine M1 obligations.
No assumption on a derivative of the well rates appears.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The pointwise linear multiplier for the nonlinear reaction field. -/
noncomputable def srPhysicalReactionPointwiseCLM
    {X : Type*} (γ₂ : X → ℝ → ℝ) (R : ℝ → X → ℝ)
    (Rstar : X → ℝ) (t : ℝ) (x : X) : ℝ →L[ℝ] ℝ :=
  (γ₂ x t * (R t x - Rstar x)) • ContinuousLinearMap.id ℝ ℝ

/-- The nonlinear reaction can be written as a true L² multiplication
operator acting on the L² SR field, with an explicit uniform norm bound.
No L² reaction norm is assumed. -/
theorem sr_physical_L2_reaction_multiplier_exists
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (γ₂ : X → ℝ → ℝ) (R : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (t γ2max Rmax RstarMax : ℝ)
    (hγmeas : Measurable (fun x => γ₂ x t))
    (hRmeas : Measurable (R t))
    (hRstarmeas : Measurable Rstar)
    (hγ2max : 0 ≤ γ2max) (hRmax : 0 ≤ Rmax)
    (hRstarMax : 0 ≤ RstarMax)
    (hγ₂ : ∀ᵐ x ∂μ, |γ₂ x t| ≤ γ2max)
    (hR : ∀ᵐ x ∂μ, 0 ≤ R t x ∧ R t x ≤ Rmax)
    (hRstar : ∀ᵐ x ∂μ, 0 ≤ Rstar x ∧ Rstar x ≤ RstarMax) :
    ∃ K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ‖K‖ ≤ γ2max * (Rmax + RstarMax) ∧
      ∀ f : Lp ℝ 2 μ,
        (K f : X → ℝ) =ᵐ[μ]
          fun x => (γ₂ x t * (R t x - Rstar x)) * f x := by
  let C : X → ℝ →L[ℝ] ℝ :=
    srPhysicalReactionPointwiseCLM γ₂ R Rstar t
  have hC : AEStronglyMeasurable C μ := by
    have hm : Measurable C := by
      dsimp [C, srPhysicalReactionPointwiseCLM]
      exact (hγmeas.mul (hRmeas.sub hRstarmeas)).smul measurable_const
    exact hm.aestronglyMeasurable
  have hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ γ2max * (Rmax + RstarMax) := by
    filter_upwards [hγ₂, hR, hRstar] with x hγ hr hs
    have hdelta : |R t x - Rstar x| ≤ Rmax + RstarMax := by
      apply abs_le.mpr
      constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]
    have hmul : |γ₂ x t * (R t x - Rstar x)| ≤
        γ2max * (Rmax + RstarMax) := by
      rw [abs_mul]
      exact mul_le_mul hγ hdelta (abs_nonneg _) hγ2max
    simpa [C, srPhysicalReactionPointwiseCLM, norm_smul, Real.norm_eq_abs]
      using hmul
  have hnonneg : 0 ≤ γ2max * (Rmax + RstarMax) :=
    mul_nonneg hγ2max (add_nonneg hRmax hRstarMax)
  let K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    pressureNeumannL2Multiplier μ C hC
      (γ2max * (Rmax + RstarMax)) hnonneg hBound
  refine ⟨K, ?_, ?_⟩
  · exact pressure_neumann_l2_multiplier_norm_le μ C hC
      (γ2max * (Rmax + RstarMax)) hnonneg hBound
  · intro f
    have hPointwise := pressure_neumann_l2_multiplier_apply_ae μ C hC
      (γ2max * (Rmax + RstarMax)) hnonneg hBound f
    filter_upwards [hPointwise] with x hx
    change (K f : X → ℝ) x = C x (f x) at hx
    simpa [C, srPhysicalReactionPointwiseCLM, smul_eq_mul] using hx

/-- The spatially a.e. *physical* SR equation determines an L²
right-hand side, whose norm is controlled by the L² pressure rate and
L² SR state. This constructs both multipliers rather than assuming
abstract operator bounds. The pointwise equation is the stated model;
the time-derivative interpretation remains to be proved separately. -/
theorem sr_physical_L2_rhs_bound_of_pointwise_ode
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (γ₁ : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (t γmax γ2max Rmax RstarMax : ℝ)
    (hγ₁meas : Measurable γ₁)
    (hγ₂meas : Measurable (fun x => γ₂ x t))
    (hRmeas : Measurable (R t))
    (hRstarmeas : Measurable Rstar)
    (hγmax : 0 ≤ γmax) (hγ2max : 0 ≤ γ2max)
    (hRmax : 0 ≤ Rmax) (hRstarMax : 0 ≤ RstarMax)
    (hγ₁ : ∀ᵐ x ∂μ, |γ₁ x| ≤ γmax)
    (hγ₂ : ∀ᵐ x ∂μ, |γ₂ x t| ≤ γ2max)
    (hR : ∀ᵐ x ∂μ, 0 ≤ R t x ∧ R t x ≤ Rmax)
    (hRstar : ∀ᵐ x ∂μ, 0 ≤ Rstar x ∧ Rstar x ≤ RstarMax)
    (Udot R_L2 Rdot : Lp ℝ 2 μ)
    (hRrep : ∀ᵐ x ∂μ, (R_L2 x : ℝ) = R t x)
    (hODE : ∀ᵐ x ∂μ,
      (Rdot x : ℝ) =
        -γ₁ x * R t x * (Udot x) -
          γ₂ x t * R t x * (R t x - Rstar x)) :
    ‖Rdot‖ ≤
      (γmax * Rmax) * ‖Udot‖ +
        (γ2max * (Rmax + RstarMax)) * ‖R_L2‖ := by
  obtain ⟨Kp, hpNorm, hpRep⟩ :=
    sr_physical_L2_multiplier_exists μ γ₁ R t γmax Rmax
      hγ₁meas hRmeas hγmax hRmax hγ₁ hR
  obtain ⟨Kr, hrNorm, hrRep⟩ :=
    sr_physical_L2_reaction_multiplier_exists μ γ₂ R Rstar
      t γ2max Rmax RstarMax hγ₂meas hRmeas hRstarmeas
      hγ2max hRmax hRstarMax hγ₂ hR hRstar
  have hL2ODE : Rdot = -(Kp Udot) - Kr R_L2 := by
    apply Lp.ext
    filter_upwards [hODE, hRrep, hpRep Udot, hrRep R_L2,
      Lp.coeFn_neg (Kp Udot),
      Lp.coeFn_sub (-(Kp Udot)) (Kr R_L2)]
      with x hx hRval hpval hrval hneg hsub
    calc
      (Rdot x : ℝ) = -γ₁ x * R t x * (Udot x) -
          γ₂ x t * R t x * (R t x - Rstar x) := hx
      _ = -(Kp Udot x) - Kr R_L2 x := by
        rw [hpval, hrval, hRval]
        ring
      _ = ((-(Kp Udot) - Kr R_L2 : Lp ℝ 2 μ) x : ℝ) := by
        calc
          -(Kp Udot x) - Kr R_L2 x =
              ((-(Kp Udot) : Lp ℝ 2 μ) x : ℝ) - (Kr R_L2 x : ℝ) := by
                exact congrArg (fun a : ℝ => a - (Kr R_L2 x : ℝ)) hneg.symm
          _ = ((-(Kp Udot) - Kr R_L2 : Lp ℝ 2 μ) x : ℝ) := hsub.symm
  rw [hL2ODE]
  calc
    ‖-(Kp Udot) - Kr R_L2‖
        ≤ ‖Kp Udot‖ + ‖Kr R_L2‖ := by
          simpa [norm_neg] using (norm_sub_le (-(Kp Udot)) (Kr R_L2))
    _ ≤ ‖Kp‖ * ‖Udot‖ + ‖Kr‖ * ‖R_L2‖ :=
      add_le_add (Kp.le_opNorm Udot) (Kr.le_opNorm R_L2)
    _ ≤ (γmax * Rmax) * ‖Udot‖ +
        (γ2max * (Rmax + RstarMax)) * ‖R_L2‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right hpNorm (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hrNorm (norm_nonneg _))

/-- The physical SR a.e. rate bound (A7), with BOTH spatial
multipliers constructed from measurable coefficients and with NO
abstract `hK` or reaction-bound hypothesis. This assumes the
spatially a.e. SR equation for the candidate strong derivative;
proving that identity from the Carathéodory time evolution is the
remaining time-regularity obligation. -/
theorem sr_physical_L2_rate_bound_ae_of_spatial_ode
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (γ₁ : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (γmax γ2max Rmax RstarMax CU CR : ℝ)
    (hγ₁meas : Measurable γ₁)
    (hγ₂meas : ∀ t, Measurable (fun x => γ₂ x t))
    (hRmeas : ∀ t, Measurable (R t))
    (hRstarmeas : Measurable Rstar)
    (hγmax : 0 ≤ γmax) (hγ2max : 0 ≤ γ2max)
    (hRmax : 0 ≤ Rmax) (hRstarMax : 0 ≤ RstarMax)
    (hγ₁ : ∀ᵐ x ∂μ, |γ₁ x| ≤ γmax)
    (hγ₂ : ∀ t, ∀ᵐ x ∂μ, |γ₂ x t| ≤ γ2max)
    (hR : ∀ t, ∀ᵐ x ∂μ, 0 ≤ R t x ∧ R t x ≤ Rmax)
    (hRstar : ∀ᵐ x ∂μ, 0 ≤ Rstar x ∧ Rstar x ≤ RstarMax)
    (Udot R_L2 Rdot : ℝ → Lp ℝ 2 μ)
    (hU : ∀ᵐ t ∂paperPositiveTime, ‖Udot t‖ ≤ CU)
    (hRL2 : ∀ᵐ t ∂paperPositiveTime, ‖R_L2 t‖ ≤ CR)
    (hRrep : ∀ᵐ t ∂paperPositiveTime,
      ∀ᵐ x ∂μ, ((R_L2 t) x : ℝ) = R t x)
    (hODE : ∀ᵐ t ∂paperPositiveTime,
      ∀ᵐ x ∂μ, ((Rdot t) x : ℝ) =
        -γ₁ x * R t x * ((Udot t) x) -
          γ₂ x t * R t x * (R t x - Rstar x)) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖Rdot t‖ ≤
        (γmax * Rmax) * CU +
          (γ2max * (Rmax + RstarMax)) * CR := by
  have hfirst : 0 ≤ γmax * Rmax := mul_nonneg hγmax hRmax
  have hsecond : 0 ≤ γ2max * (Rmax + RstarMax) :=
    mul_nonneg hγ2max (add_nonneg hRmax hRstarMax)
  filter_upwards [hU, hRL2, hRrep, hODE] with t hUt hRt hRep hOde
  have hb := sr_physical_L2_rhs_bound_of_pointwise_ode
    μ γ₁ γ₂ R Rstar t γmax γ2max Rmax RstarMax
    hγ₁meas (hγ₂meas t) (hRmeas t) hRstarmeas
    hγmax hγ2max hRmax hRstarMax
    hγ₁ (hγ₂ t) (hR t) hRstar
    (Udot t) (R_L2 t) (Rdot t) hRep hOde
  calc
    ‖Rdot t‖ ≤
      (γmax * Rmax) * ‖Udot t‖ +
        (γ2max * (Rmax + RstarMax)) * ‖R_L2 t‖ := hb
    _ ≤ (γmax * Rmax) * CU +
        (γ2max * (Rmax + RstarMax)) * CR :=
      add_le_add
        (mul_le_mul_of_nonneg_left hUt hfirst)
        (mul_le_mul_of_nonneg_left hRt hsecond)

#print axioms ReservoirSeismicityControl.sr_physical_L2_reaction_multiplier_exists
#print axioms ReservoirSeismicityControl.sr_physical_L2_rhs_bound_of_pointwise_ode
#print axioms ReservoirSeismicityControl.sr_physical_L2_rate_bound_ae_of_spatial_ode

end ReservoirSeismicityControl
