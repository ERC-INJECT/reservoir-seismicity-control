import ReservoirSeismicityControl.SeismicityPhysicalReciprocalCaratheodory
import ReservoirSeismicityControl.SeismicityPhysicalL2RHS
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl: known constant sign in the physical seismicity-rate model

Manuscript (22 October 2026), (3):
  R_t = R (s gamma1 u_t - gamma2 (R - Rstar)),  s ∈ {-1, 1}.

The previously compiled SR proofs treated `s = -1`.  They are retained
unchanged.  The identity `gammaEffective = -s * gamma1` recovers the old
coefficient convention and transports those proofs to either sign.

The transformation in Appendix A.2 is
  S = R exp(-s gamma1 u),  Y = exp(s gamma1 u) / R,
  a = gamma2 Rstar,  b = gamma2 exp(s gamma1 u),
  Y_t = -a Y + b.

The normalized SR tracking error is `-s*(yR-rR)/(gamma10*R0star)`.
Since `s*s=1`, its well-input term is independent of `s`; the
SR reaction/reference terms keep their indicated factor `s`.

This module proves exact sign transport for the pointwise construction,
pointwise L² norm bound, and the tracking-error sign cancellation.
It does not assert the missing local H² estimates.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The paper's known, constant coupling sign. -/
def SRSign (s : ℝ) : Prop := s = -1 ∨ s = 1

/-- Multiplying the sign by itself removes the sign in the control coefficient. -/
theorem sr_sign_sq_one (s : ℝ) (hs : SRSign s) : s * s = 1 := by
  rcases hs with hs | hs
  · rw [hs]; norm_num
  · rw [hs]; norm_num

/-- Both cases have unit absolute value. -/
theorem sr_sign_abs_one (s : ℝ) (hs : SRSign s) : |s| = 1 := by
  rcases hs with hs | hs
  · rw [hs]; norm_num
  · rw [hs]; norm_num

/-- The existing `-gamma*u_t` convention, with signed physical gamma. -/
def srSignedEffectiveGamma (s gamma : ℝ) : ℝ := -s * gamma

/-- Signed version of the previously verified explicit SR construction.
The old theorem can be applied with `gammaEffective = -s*gamma`. -/
noncomputable def srSignedPhysicalFromReciprocal
    (u : ℝ → ℝ) (s gamma Rstar : ℝ)
    (gamma2 : ℝ → ℝ) (y0 t : ℝ) : ℝ :=
  srPhysicalFromReciprocal u (srSignedEffectiveGamma s gamma) Rstar gamma2 y0 t

/-- The signed model has the expected reciprocal initial value. -/
theorem sr_signed_reciprocal_initial_matches
    (u : ℝ → ℝ) (s gamma Rstar : ℝ) (gamma2 : ℝ → ℝ)
    (R0 : ℝ) (hR0 : R0 ≠ 0) :
    srSignedPhysicalFromReciprocal u s gamma Rstar gamma2
      (Real.exp (s * gamma * u 0) / R0) 0 = R0 := by
  have hEq : -srSignedEffectiveGamma s gamma * u 0 =
      s * gamma * u 0 := by
    dsimp [srSignedEffectiveGamma]
    ring
  rw [← hEq]
  exact sr_physical_reciprocal_initial_matches
    u (srSignedEffectiveGamma s gamma) Rstar gamma2 R0 hR0

/-- Exact signed Carathéodory SR solution, transported from the old
explicit reciprocal construction. No assumption on `u_tt` or `Qdot`.
The sign restriction is only needed by the eventual control synthesis,
not by the scalar variation-of-constants identity itself. -/
theorem sr_signed_physical_reciprocal_caratheodory_ae
    (u ut : ℝ → ℝ) (s gamma Rstar : ℝ) (gamma2 : ℝ → ℝ)
    (y0 T : ℝ) (hT : 0 ≤ T) (hy0 : 0 < y0)
    (hgamma2 : ∀ v ∈ Set.Icc (0 : ℝ) T, 0 ≤ gamma2 v)
    (hAInt : IntervalIntegrable
      (fun v : ℝ => gamma2 v * Rstar) volume (0 : ℝ) T)
    (hBInt : IntervalIntegrable
      (fun v : ℝ =>
        Real.exp (srReciprocalPrimitive (fun w => gamma2 w * Rstar) v) *
          (gamma2 v * Real.exp (s * gamma * u v)))
      volume (0 : ℝ) T)
    (hu : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) T → HasDerivAt u (ut t) t) :
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < srSignedPhysicalFromReciprocal u s gamma Rstar gamma2 y0 t) ∧
    (∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (srSignedPhysicalFromReciprocal u s gamma Rstar gamma2 y0)
          (s * gamma * srSignedPhysicalFromReciprocal
              u s gamma Rstar gamma2 y0 t * ut t -
            gamma2 t * srSignedPhysicalFromReciprocal
              u s gamma Rstar gamma2 y0 t *
              (srSignedPhysicalFromReciprocal
                u s gamma Rstar gamma2 y0 t - Rstar)) t) := by
  let geff := srSignedEffectiveGamma s gamma
  have hExp : ∀ v : ℝ, -geff * u v = s * gamma * u v := by
    intro v
    dsimp [geff, srSignedEffectiveGamma]
    ring
  have hBIntOld : IntervalIntegrable
      (fun v : ℝ =>
        Real.exp (srReciprocalPrimitive (fun w => gamma2 w * Rstar) v) *
          (gamma2 v * Real.exp (-geff * u v)))
      volume (0 : ℝ) T := by
    have hFun :
        (fun v : ℝ =>
          Real.exp (srReciprocalPrimitive (fun w => gamma2 w * Rstar) v) *
            (gamma2 v * Real.exp (-geff * u v))) =
        (fun v : ℝ =>
          Real.exp (srReciprocalPrimitive (fun w => gamma2 w * Rstar) v) *
            (gamma2 v * Real.exp (s * gamma * u v))) := by
      funext v
      rw [hExp v]
    rw [hFun]
    exact hBInt
  obtain ⟨hpos, hder⟩ := sr_physical_reciprocal_caratheodory_ae
    u ut geff Rstar gamma2 y0 T hT hy0 hgamma2 hAInt hBIntOld hu
  constructor
  · exact hpos
  · filter_upwards [hder] with t ht
    intro htI
    have hbase := ht htI
    change HasDerivAt
      (srPhysicalFromReciprocal u geff Rstar gamma2 y0)
      (s * gamma * srPhysicalFromReciprocal
          u geff Rstar gamma2 y0 t * ut t -
        gamma2 t * srPhysicalFromReciprocal
          u geff Rstar gamma2 y0 t *
          (srPhysicalFromReciprocal
            u geff Rstar gamma2 y0 t - Rstar)) t
    have hrate :
        -geff * srPhysicalFromReciprocal
            u geff Rstar gamma2 y0 t * ut t -
          gamma2 t * srPhysicalFromReciprocal
            u geff Rstar gamma2 y0 t *
            (srPhysicalFromReciprocal
              u geff Rstar gamma2 y0 t - Rstar) =
        s * gamma * srPhysicalFromReciprocal
            u geff Rstar gamma2 y0 t * ut t -
          gamma2 t * srPhysicalFromReciprocal
            u geff Rstar gamma2 y0 t *
            (srPhysicalFromReciprocal
              u geff Rstar gamma2 y0 t - Rstar) := by
      dsimp [geff, srSignedEffectiveGamma]
      ring
    rw [← hrate]
    exact hbase

/-- The signed SR field inherits the same physical pointwise-to-L²
rate norm estimate. This uses only `|s|=1` and the *already verified*
physical L² multipliers. -/
theorem sr_signed_physical_L2_rhs_bound_of_pointwise_ode
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (s : ℝ) (hs : SRSign s)
    (gamma1 : X → ℝ) (gamma2 : X → ℝ → ℝ)
    (R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (t gammaMax gamma2Max Rmax RstarMax : ℝ)
    (hgammaMeas : Measurable gamma1)
    (hgamma2Meas : Measurable (fun x => gamma2 x t))
    (hRMeas : Measurable (R t))
    (hRstarMeas : Measurable Rstar)
    (hgammaMax : 0 ≤ gammaMax) (hgamma2Max : 0 ≤ gamma2Max)
    (hRmax : 0 ≤ Rmax) (hRstarMax : 0 ≤ RstarMax)
    (hgamma : ∀ᵐ x ∂mu, |gamma1 x| ≤ gammaMax)
    (hgamma2 : ∀ᵐ x ∂mu, |gamma2 x t| ≤ gamma2Max)
    (hR : ∀ᵐ x ∂mu, 0 ≤ R t x ∧ R t x ≤ Rmax)
    (hRstar : ∀ᵐ x ∂mu, 0 ≤ Rstar x ∧ Rstar x ≤ RstarMax)
    (Udot R_L2 Rdot : Lp ℝ 2 mu)
    (hRrep : ∀ᵐ x ∂mu, (R_L2 x : ℝ) = R t x)
    (hODE : ∀ᵐ x ∂mu,
      (Rdot x : ℝ) =
        s * gamma1 x * R t x * (Udot x) -
          gamma2 x t * R t x * (R t x - Rstar x)) :
    ‖Rdot‖ ≤ (gammaMax * Rmax) * ‖Udot‖ +
      (gamma2Max * (Rmax + RstarMax)) * ‖R_L2‖ := by
  let geff : X → ℝ := fun x => -s * gamma1 x
  have hgeffMeas : Measurable geff := by
    dsimp [geff]
    exact measurable_const.mul hgammaMeas
  have hgeffBound : ∀ᵐ x ∂mu, |geff x| ≤ gammaMax := by
    have hsabs : |s| = 1 := sr_sign_abs_one s hs
    filter_upwards [hgamma] with x hx
    calc
      |geff x| = |s| * |gamma1 x| := by simp [geff, abs_mul]
      _ = |gamma1 x| := by rw [hsabs, one_mul]
      _ ≤ gammaMax := hx
  have hODEeff : ∀ᵐ x ∂mu,
      (Rdot x : ℝ) =
        -geff x * R t x * (Udot x) -
          gamma2 x t * R t x * (R t x - Rstar x) := by
    filter_upwards [hODE] with x hx
    calc
      (Rdot x : ℝ) =
          s * gamma1 x * R t x * (Udot x) -
            gamma2 x t * R t x * (R t x - Rstar x) := hx
      _ = -geff x * R t x * (Udot x) -
            gamma2 x t * R t x * (R t x - Rstar x) := by
          dsimp [geff]
          ring
  exact sr_physical_L2_rhs_bound_of_pointwise_ode mu geff gamma2 R Rstar
    t gammaMax gamma2Max Rmax RstarMax hgeffMeas hgamma2Meas
    hRMeas hRstarMeas hgammaMax hgamma2Max hRmax hRstarMax
    hgeffBound hgamma2 hR hRstar Udot R_L2 Rdot hRrep hODEeff

/-- Eq. (12) normalization cancels the SR input sign: the gain
coefficient has the same sign and expression for both values of s.
The reaction term retains the factor s. -/
theorem sr_signed_tracking_error_input_cancellation
    (s gamma R ut reaction c : ℝ) (hs : SRSign s) :
    (-s * c) * (R * (s * gamma * ut - reaction)) =
      -c * (gamma * R * ut) + s * c * (R * reaction) := by
  rcases hs with hs | hs
  · rw [hs]; ring
  · rw [hs]; ring

#print axioms ReservoirSeismicityControl.sr_sign_sq_one
#print axioms ReservoirSeismicityControl.sr_sign_abs_one
#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_initial_matches
#print axioms ReservoirSeismicityControl.sr_signed_physical_reciprocal_caratheodory_ae
#print axioms ReservoirSeismicityControl.sr_signed_physical_L2_rhs_bound_of_pointwise_ode
#print axioms ReservoirSeismicityControl.sr_signed_tracking_error_input_cancellation

end ReservoirSeismicityControl
