import ReservoirSeismicityControl.SeismicitySignedSpatialFirstQuotientLp6
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# M1 — A time-uniform barrier for the actual signed SR reciprocal first quotient

Let `Y(x,t)` be the *constructed* reciprocal SR solution, with
`a=gamma2*Rstar` and `b=gamma2*exp(s*gamma1*u)` for either sign.
The verified first quotient solves

  z'(t) = -a(x+h,t)*z(t) + db(t) - da(t)*Y(x,t).

This module proves a signed comparison estimate for an arbitrary damped
scalar ODE, and then applies it to the *actual* quotient of the explicit
Caratheodory construction, rather than assuming a comparison inequality.

The estimates in this file are pointwise in space.  The coefficient
quotient bounds in the final theorem are pointwise and therefore stronger
than the L6 bounds of Assumption 3.  This is a verified analytic stepping
stone, NOT the missing physical L6_x bound or H2(U_j) theorem.  The latter
requires an L6_x estimate for a spatially varying positive propagator under
L-infinity-in-time L6-in-space coefficient bounds (plus weak compactness).

No bound on the derivative of well rates is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A possibly signed solution of `z'=-a*z+f` cannot cross an upper
barrier `K` if `a(t)>=aMin>0` and `f(t)<=Fmax<=aMin*K`.
The proof uses the *actual variable-coefficient integrating factor*, not
a constant-coefficient approximation. -/
theorem sr_damped_signed_upper_barrier
    (z a f : ℝ → ℝ) (aMin Fmax K : ℝ)
    (haMin : 0 < aMin) (hK : 0 ≤ K)
    (hFK : Fmax ≤ aMin * K)
    (haContinuous : Continuous a)
    (haLower : ∀ t : ℝ, 0 ≤ t → aMin ≤ a t)
    (hfUpper : ∀ t : ℝ, 0 ≤ t → f t ≤ Fmax)
    (hzInitial : z 0 ≤ K)
    (hzDeriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt z (-a t * z t + f t) t) :
    ∀ t : ℝ, 0 ≤ t → z t ≤ K := by
  let A : ℝ → ℝ := srReciprocalPrimitive a
  let F : ℝ → ℝ := fun t => Real.exp (A t) * (z t - K)
  have hAprime (t : ℝ) : HasDerivAt A (a t) t := by
    change HasDerivAt
      (fun v : ℝ => ∫ s in (0 : ℝ)..v, a s) (a t) t
    exact intervalIntegral.integral_hasDerivAt_right
      (haContinuous.intervalIntegrable 0 t)
      (haContinuous.stronglyMeasurableAtFilter _ _)
      haContinuous.continuousAt
  have hFder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F (Real.exp (A t) * (f t - a t * K)) t := by
    have hExp : HasDerivAt
        (fun v : ℝ => Real.exp (A v))
        (Real.exp (A t) * a t) t :=
      (Real.hasDerivAt_exp _).comp t (hAprime t)
    have hd := hExp.mul ((hzDeriv t ht).sub_const K)
    have hEq :
        Real.exp (A t) * a t * (z t - K) +
          Real.exp (A t) * (-a t * z t + f t) =
        Real.exp (A t) * (f t - a t * K) := by ring
    rw [hEq] at hd
    exact hd
  have hFcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hFder t ht).continuousAt.continuousWithinAt
  have hFdiff : DifferentiableOn ℝ F
      (interior (Set.Ici (0 : ℝ))) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    exact (hFder t ht0).differentiableAt.differentiableWithinAt
  have hFnonpos : ∀ t ∈ interior (Set.Ici (0 : ℝ)),
      deriv F t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    have haK : aMin * K ≤ a t * K :=
      mul_le_mul_of_nonneg_right (haLower t ht0) hK
    have hforce : f t - a t * K ≤ 0 := by
      have hf := hfUpper t ht0
      linarith
    rw [(hFder t ht0).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hforce
  have hFanti : AntitoneOn F (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
      hFcont hFdiff hFnonpos
  have hFzero : F 0 = z 0 - K := by
    simp [F, A, srReciprocalPrimitive]
  intro t ht
  have hbound : F t ≤ F 0 :=
    hFanti (by simp) (by simpa using ht) ht
  rw [hFzero] at hbound
  have hFnon : F t ≤ 0 := by linarith
  by_contra hz
  have hzpos : 0 < z t - K := sub_pos.mpr (lt_of_not_ge hz)
  have hFpos : 0 < F t := mul_pos (Real.exp_pos _) hzpos
  linarith

/-- The signed, time-uniform comparison for the *absolute value* of a
linear damped solution. Neither `z` nor `f` need be nonnegative. -/
theorem sr_damped_signed_abs_barrier
    (z a f : ℝ → ℝ) (aMin Fmax : ℝ)
    (haMin : 0 < aMin)
    (haContinuous : Continuous a)
    (haLower : ∀ t : ℝ, 0 ≤ t → aMin ≤ a t)
    (hfAbs : ∀ t : ℝ, 0 ≤ t → |f t| ≤ Fmax)
    (hzDeriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt z (-a t * z t + f t) t) :
    ∀ t : ℝ, 0 ≤ t →
      |z t| ≤ |z 0| + Fmax / aMin := by
  have hFnonneg : 0 ≤ Fmax :=
    (abs_nonneg (f 0)).trans (hfAbs 0 le_rfl)
  let K : ℝ := |z 0| + Fmax / aMin
  have hDiv : 0 ≤ Fmax / aMin :=
    div_nonneg hFnonneg haMin.le
  have hK : 0 ≤ K := add_nonneg (abs_nonneg _) hDiv
  have hFK : Fmax ≤ aMin * K := by
    have hEq : aMin * (Fmax / aMin) = Fmax := by
      field_simp [ne_of_gt haMin]
    dsimp [K]
    nlinarith [mul_nonneg haMin.le (abs_nonneg (z 0))]
  have hzZeroUpper : z 0 ≤ K := by
    dsimp [K]
    linarith [le_abs_self (z 0)]
  have hzZeroLower : -z 0 ≤ K := by
    dsimp [K]
    linarith [neg_le_abs (z 0)]
  have hPositive := sr_damped_signed_upper_barrier z a f
    aMin Fmax K haMin hK hFK haContinuous haLower
    (fun t ht => (le_abs_self (f t)).trans (hfAbs t ht))
    hzZeroUpper hzDeriv
  have hNegDerivative : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun v : ℝ => -z v)
        (-a t * (-z t) + (-f t)) t := by
    intro t ht
    have hd := (hzDeriv t ht).neg
    convert hd using 1 <;> ring
  have hNegative := sr_damped_signed_upper_barrier
    (fun t : ℝ => -z t) a (fun t : ℝ => -f t)
    aMin Fmax K haMin hK hFK haContinuous haLower
    (fun t ht => (neg_le_abs (f t)).trans (hfAbs t ht))
    hzZeroLower hNegDerivative
  intro t ht
  apply abs_le.mpr
  constructor
  · have h := hNegative t ht
    linarith
  · exact hPositive t ht

/-- At *every* time, the first quotient of the constructed reciprocal
has the expected variable-coefficient ODE, when its two pointwise
coefficient trajectories are continuous.  The earlier general theorem
requires only time integrability and gives the equation a.e.; here the
continuity hypothesis allows application of the classical barrier. -/
theorem sr_reciprocal_first_quotient_hasDerivAt_continuous
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₁ x₀ : X) (h t : ℝ)
    (ha₁ : Continuous (a x₁)) (ha₀ : Continuous (a x₀))
    (hb₁ : Continuous (b x₁)) (hb₀ : Continuous (b x₀)) :
    HasDerivAt (srReciprocalFirstQuotient a b y₀ x₁ x₀ h)
      (-a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
        (b x₁ t - b x₀ t) / h -
        ((a x₁ t - a x₀ t) / h) *
          srReciprocalSpatialField a b y₀ x₀ t) t := by
  have h₁ := sr_reciprocal_explicit_hasDerivAt_continuous
    (a x₁) (b x₁) (y₀ x₁) t ha₁ hb₁
  have h₀ := sr_reciprocal_explicit_hasDerivAt_continuous
    (a x₀) (b x₀) (y₀ x₀) t ha₀ hb₀
  have hd := (h₁.sub h₀).const_mul (h⁻¹)
  change HasDerivAt
    (fun v => h⁻¹ *
      (srReciprocalSpatialField a b y₀ x₁ v -
        srReciprocalSpatialField a b y₀ x₀ v))
    (h⁻¹ *
      ((-a x₁ t * srReciprocalSpatialField a b y₀ x₁ t + b x₁ t) -
       (-a x₀ t * srReciprocalSpatialField a b y₀ x₀ t + b x₀ t))) t
    at hd
  have hEq :
      h⁻¹ *
        ((-a x₁ t * srReciprocalSpatialField a b y₀ x₁ t + b x₁ t) -
         (-a x₀ t * srReciprocalSpatialField a b y₀ x₀ t + b x₀ t)) =
      -a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
        (b x₁ t - b x₀ t) / h -
        ((a x₁ t - a x₀ t) / h) *
          srReciprocalSpatialField a b y₀ x₀ t := by
    simp only [srReciprocalFirstQuotient, div_eq_mul_inv]
    ring
  rw [hEq] at hd
  have hFun :
      (fun v => h⁻¹ *
        (srReciprocalSpatialField a b y₀ x₁ v -
          srReciprocalSpatialField a b y₀ x₀ v)) =
      srReciprocalFirstQuotient a b y₀ x₁ x₀ h := by
    funext v
    simp only [srReciprocalFirstQuotient, div_eq_mul_inv]
    ring
  rw [hFun] at hd
  exact hd

/-- Time-independent first-quotient estimate for the **constructed**
reciprocal field at two spatial points.

This theorem is pointwise in space: its bounds on the coefficient
quotients are L∞_x-type assumptions, stronger than the paper's L6_x
data. It is not yet the desired uniform L6_x conclusion. -/
theorem sr_reciprocal_first_quotient_uniform_pointwise
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₁ x₀ : X) (h aMin A1 B1 YM : ℝ)
    (haMin : 0 < aMin) (hA1 : 0 ≤ A1)
    (ha₁ : Continuous (a x₁)) (ha₀ : Continuous (a x₀))
    (hb₁ : Continuous (b x₁)) (hb₀ : Continuous (b x₀))
    (haLower : ∀ t : ℝ, 0 ≤ t → aMin ≤ a x₁ t)
    (hDa : ∀ t : ℝ, 0 ≤ t →
      |(a x₁ t - a x₀ t) / h| ≤ A1)
    (hDb : ∀ t : ℝ, 0 ≤ t →
      |(b x₁ t - b x₀ t) / h| ≤ B1)
    (hY : ∀ t : ℝ, 0 ≤ t →
      |srReciprocalSpatialField a b y₀ x₀ t| ≤ YM) :
    ∀ t : ℝ, 0 ≤ t →
      |srReciprocalFirstQuotient a b y₀ x₁ x₀ h t| ≤
      |srReciprocalFirstQuotient a b y₀ x₁ x₀ h 0| +
        (B1 + A1 * YM) / aMin := by
  let z : ℝ → ℝ := srReciprocalFirstQuotient a b y₀ x₁ x₀ h
  let f : ℝ → ℝ := fun t =>
    (b x₁ t - b x₀ t) / h -
      ((a x₁ t - a x₀ t) / h) *
        srReciprocalSpatialField a b y₀ x₀ t
  have hf : ∀ t : ℝ, 0 ≤ t → |f t| ≤ B1 + A1 * YM := by
    intro t ht
    exact sr_reciprocal_first_quotient_forcing_abs_le
      ((a x₁ t - a x₀ t) / h) ((b x₁ t - b x₀ t) / h)
      (srReciprocalSpatialField a b y₀ x₀ t)
      A1 B1 YM (hDa t ht) (hDb t ht) (hY t ht) hA1
  have hzDeriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt z (-a x₁ t * z t + f t) t := by
    intro t _
    have hd := sr_reciprocal_first_quotient_hasDerivAt_continuous
      a b y₀ x₁ x₀ h t ha₁ ha₀ hb₁ hb₀
    have hAssoc :
        (-a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
          (b x₁ t - b x₀ t) / h -
          ((a x₁ t - a x₀ t) / h) *
            srReciprocalSpatialField a b y₀ x₀ t) =
        (-a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
          ((b x₁ t - b x₀ t) / h -
            ((a x₁ t - a x₀ t) / h) *
              srReciprocalSpatialField a b y₀ x₀ t)) := by
      ring
    rw [hAssoc] at hd
    exact hd
  exact sr_damped_signed_abs_barrier z (a x₁) f
    aMin (B1 + A1 * YM) haMin ha₁ haLower hf hzDeriv

#print axioms ReservoirSeismicityControl.sr_damped_signed_upper_barrier
#print axioms ReservoirSeismicityControl.sr_damped_signed_abs_barrier
#print axioms ReservoirSeismicityControl.sr_reciprocal_first_quotient_hasDerivAt_continuous
#print axioms ReservoirSeismicityControl.sr_reciprocal_first_quotient_uniform_pointwise

end ReservoirSeismicityControl
