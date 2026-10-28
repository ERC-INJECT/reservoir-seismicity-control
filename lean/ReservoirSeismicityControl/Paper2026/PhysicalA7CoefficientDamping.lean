import ReservoirSeismicityControl.SeismicitySignedSpatialL6Damping
import ReservoirSeismicityControl.SeismicitySignedPhysicalLocalH2
import Mathlib.Tactic

/-!
# Appendix A.2: instantiate recovered damping bounds for the actual SR coefficient

This is a physical *applicability* step, not a new generic diffusion or
Sobolev theorem. The reciprocal coefficient is `a(x,t) = gamma2(x,t)*Rstar(x)`.
Assumption 3 controls it for positive physical times only. The recovered
`sr_signed_spatial_damping_abs_le_one` theorem expects its coefficient bound
on all real times, so we extend `a` by freezing it at t=0 for negative times.
The extension agrees with the manuscript's coefficient for t >= 0.

The spatially dependent residual damping and its L6 contraction are then
obtained from existing theorems; no separate damping-bound assumption remains.
No derivative of well flux Q is used. These bounds alone do not give the
missing physical weak-H2 kernel or complete (A7).
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- Nonnegative-time continuation of the physical reciprocal coefficient.
    Negative times are not part of the PDE-ODE model. -/
private def physicalA7CoeffExtended
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ) :
    X → ℝ → ℝ :=
  fun x t => gamma2 x (max t 0) * Rstar x

/-- The extension agrees exactly with the physical coefficient on T=[0,∞). -/
theorem physical_A7_coefficient_matches_on_positive_time
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (x : X) (t : ℝ) (ht : 0 ≤ t) :
    physicalA7CoeffExtended gamma2 Rstar x t = gamma2 x t * Rstar x := by
  simp [physicalA7CoeffExtended, max_eq_left ht]

/-- Assumption 3's positive lower bounds imply a uniform positive damping
coefficient, including for the harmless constant extension at t<0. -/
theorem physical_A7_coefficient_lower_from_A3
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm : ℝ)
    (hg2 : 0 < gamma2m) (hRs : 0 < Rstarm)
    (hg2bound : ∀ x t, 0 ≤ t → gamma2m ≤ gamma2 x t)
    (hRsbound : ∀ x, Rstarm ≤ Rstar x) :
    ∀ x t, gamma2m * Rstarm ≤
      physicalA7CoeffExtended gamma2 Rstar x t := by
  intro x t
  have ht : 0 ≤ max t (0 : ℝ) := le_max_right _ _
  have hRpos : 0 ≤ Rstar x := (le_of_lt hRs).trans (hRsbound x)
  calc
    gamma2m * Rstarm ≤ gamma2m * Rstar x :=
      mul_le_mul_of_nonneg_left (hRsbound x) (le_of_lt hg2)
    _ ≤ gamma2 x (max t 0) * Rstar x :=
      mul_le_mul_of_nonneg_right (hg2bound x (max t 0) ht) hRpos
    _ = physicalA7CoeffExtended gamma2 Rstar x t := rfl

/-- Physical upper and lower box for a=gamma2*Rstar; in particular
both inequalities hold on the manuscript's nonnegative time axis. -/
theorem physical_A7_coefficient_box_from_A3
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m gamma2M Rstarm RstarM : ℝ)
    (hg2 : 0 < gamma2m) (hRs : 0 < Rstarm)
    (hg2M : 0 ≤ gamma2M)
    (hg2bound : ∀ x t, 0 ≤ t →
      gamma2m ≤ gamma2 x t ∧ gamma2 x t ≤ gamma2M)
    (hRsbound : ∀ x, Rstarm ≤ Rstar x ∧ Rstar x ≤ RstarM) :
    ∀ x t, 0 ≤ t →
      gamma2m * Rstarm ≤ gamma2 x t * Rstar x ∧
      gamma2 x t * Rstar x ≤ gamma2M * RstarM := by
  intro x t ht
  have hRsPos : 0 ≤ Rstar x :=
    (le_of_lt hRs).trans (hRsbound x).1
  have hg2Pos : 0 ≤ gamma2 x t :=
    (le_of_lt hg2).trans (hg2bound x t ht).1
  constructor
  · calc
      gamma2m * Rstarm ≤ gamma2m * Rstar x :=
        mul_le_mul_of_nonneg_left (hRsbound x).1 (le_of_lt hg2)
      _ ≤ gamma2 x t * Rstar x :=
        mul_le_mul_of_nonneg_right (hg2bound x t ht).1 hRsPos
  · calc
      gamma2 x t * Rstar x ≤ gamma2M * Rstar x :=
        mul_le_mul_of_nonneg_right (hg2bound x t ht).2 hRsPos
      _ ≤ gamma2M * RstarM :=
        mul_le_mul_of_nonneg_left (hRsbound x).2 hg2M

/-- The *actual signed forcing* b(x,t)=gamma2(x,t)*exp(s*gamma1(x)*u(x,t))
    has uniform positive lower and upper bounds from Assumptions 3 and
    (A4). This supplies the coefficient box for the RECOVERED logistic
    comparison theorem without assuming an independent b-box. -/
theorem physical_A7_signed_forcing_box_from_A3_A4
    {X : Type*} (gamma2 : X → ℝ → ℝ)
    (gamma1 : X → ℝ) (u : X → ℝ → ℝ)
    (s gamma2m gamma2M gamma1M Umax : ℝ)
    (hs : s = -1 ∨ s = 1)
    (hg2m : 0 < gamma2m) (hg2M : 0 ≤ gamma2M)
    (hUmax : 0 ≤ Umax)
    (hg2bound : ∀ x t, 0 ≤ t →
      gamma2m ≤ gamma2 x t ∧ gamma2 x t ≤ gamma2M)
    (hg1bound : ∀ x, 0 ≤ gamma1 x ∧ gamma1 x ≤ gamma1M)
    (hubound : ∀ x t, 0 ≤ t → |u x t| ≤ Umax) :
    ∀ x t, 0 ≤ t →
      gamma2m * Real.exp (-(gamma1M * Umax)) ≤
        gamma2 x t * Real.exp (s * gamma1 x * u x t) ∧
      gamma2 x t * Real.exp (s * gamma1 x * u x t) ≤
        gamma2M * Real.exp (gamma1M * Umax) := by
  intro x t ht
  have hsabs : |s| = 1 := by
    rcases hs with hsign | hsign
    · rw [hsign]; norm_num
    · rw [hsign]; norm_num
  have hg1 := hg1bound x
  have hC : |s * gamma1 x * u x t| ≤ gamma1M * Umax := by
    calc
      |s * gamma1 x * u x t| = gamma1 x * |u x t| := by
        rw [abs_mul, abs_mul, hsabs, one_mul, abs_of_nonneg hg1.1]
      _ ≤ gamma1M * Umax :=
        mul_le_mul hg1.2 (hubound x t ht)
          (abs_nonneg _) (hg1.1.trans hg1.2)
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hC
  have hElow : Real.exp (-(gamma1M * Umax)) ≤
      Real.exp (s * gamma1 x * u x t) :=
    Real.exp_le_exp.mpr hlow
  have hEhigh : Real.exp (s * gamma1 x * u x t) ≤
      Real.exp (gamma1M * Umax) :=
    Real.exp_le_exp.mpr hhigh
  have hgamma2pos : 0 ≤ gamma2 x t :=
    (le_of_lt hg2m).trans (hg2bound x t ht).1
  constructor
  · calc
      gamma2m * Real.exp (-(gamma1M * Umax)) ≤
          gamma2 x t * Real.exp (-(gamma1M * Umax)) :=
        mul_le_mul_of_nonneg_right (hg2bound x t ht).1
          (Real.exp_pos _).le
      _ ≤ gamma2 x t * Real.exp (s * gamma1 x * u x t) :=
        mul_le_mul_of_nonneg_left hElow hgamma2pos
  · calc
      gamma2 x t * Real.exp (s * gamma1 x * u x t) ≤
          gamma2M * Real.exp (s * gamma1 x * u x t) :=
        mul_le_mul_of_nonneg_right (hg2bound x t ht).2
          (Real.exp_pos _).le
      _ ≤ gamma2M * Real.exp (gamma1M * Umax) :=
        mul_le_mul_of_nonneg_left hEhigh hg2M

/-- The positive lower bound of the signed forcing is automatic from A3. -/
theorem physical_A7_signed_forcing_lower_positive
    (gamma2m gamma1M Umax : ℝ) (hg2m : 0 < gamma2m) :
    0 < gamma2m * Real.exp (-(gamma1M * Umax)) :=
  mul_pos hg2m (Real.exp_pos _)

/-- The real physical coefficient is in the hypotheses of the already
verified spatial residual-damping theorem. This closes the coefficient
positivity instantiation of the A.2 H2-kernel work; it does not assume the
conclusion (A7). -/
theorem physical_A7_residual_damping_abs_le_one_from_A3
    {X : Type*} (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm t v : ℝ) (x : X)
    (hg2 : 0 < gamma2m) (hRs : 0 < Rstarm)
    (hg2bound : ∀ x t, 0 ≤ t → gamma2m ≤ gamma2 x t)
    (hRsbound : ∀ x, Rstarm ≤ Rstar x) :
    |ReservoirSeismicityControl.srSignedSpatialDamping
      (physicalA7CoeffExtended gamma2 Rstar)
      (gamma2m * Rstarm) t v x| ≤ 1 := by
  exact ReservoirSeismicityControl.sr_signed_spatial_damping_abs_le_one
    (physicalA7CoeffExtended gamma2 Rstar) (gamma2m * Rstarm)
    (physical_A7_coefficient_lower_from_A3 gamma2 Rstar
      gamma2m Rstarm hg2 hRs hg2bound hRsbound) t v x

/-- The existing physical L6 contraction applies to the *actual* coefficient
without assuming an arbitrary coefficient lower bound: its lower bound has
been derived above from A3. Spatial measurability of the propagator is the
usual external Caratheodory/measurability applicability condition. -/
theorem physical_A7_residual_damping_L6_from_A3
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma2 : X → ℝ → ℝ) (Rstar : X → ℝ)
    (gamma2m Rstarm t v : ℝ)
    (hg2 : 0 < gamma2m) (hRs : 0 < Rstarm)
    (hg2bound : ∀ x t, 0 ≤ t → gamma2m ≤ gamma2 x t)
    (hRsbound : ∀ x, Rstarm ≤ Rstar x)
    (hDampingMeas : AEStronglyMeasurable
      (ReservoirSeismicityControl.srSignedSpatialDamping
        (physicalA7CoeffExtended gamma2 Rstar)
        (gamma2m * Rstarm) t v) μ)
    (f : Lp ℝ (6 : ENNReal) μ) :
    ‖ReservoirSeismicityControl.srSignedSpatialL6Multiplier μ
      (ReservoirSeismicityControl.srSignedSpatialDamping
        (physicalA7CoeffExtended gamma2 Rstar)
        (gamma2m * Rstarm) t v)
      hDampingMeas
      (Filter.Eventually.of_forall
        (ReservoirSeismicityControl.sr_signed_spatial_damping_abs_le_one
          (physicalA7CoeffExtended gamma2 Rstar)
          (gamma2m * Rstarm)
          (physical_A7_coefficient_lower_from_A3 gamma2 Rstar
            gamma2m Rstarm hg2 hRs hg2bound hRsbound) t v)) f‖ ≤ ‖f‖ := by
  exact ReservoirSeismicityControl.sr_signed_spatial_L6_physical_damping_contraction μ
    (physicalA7CoeffExtended gamma2 Rstar) (gamma2m * Rstarm)
    (physical_A7_coefficient_lower_from_A3 gamma2 Rstar
      gamma2m Rstarm hg2 hRs hg2bound hRsbound)
    t v hDampingMeas f

#print axioms physical_A7_coefficient_box_from_A3
#print axioms physical_A7_signed_forcing_box_from_A3_A4
#print axioms physical_A7_coefficient_lower_from_A3
#print axioms physical_A7_residual_damping_abs_le_one_from_A3
#print axioms physical_A7_residual_damping_L6_from_A3

end ReservoirSeismicityControl.Paper2026
