import ReservoirSeismicityControl.SeismicitySignedSpatialH2Bootstrap
import Mathlib.Tactic

/-!
# M1 — Exact spatial finite-difference equations for the constructed SR reciprocal

The constructed reciprocal field is `Y(x,t) = srReciprocalExplicit (a x) (b x) (Y₀ x) t`
with the signed physical coefficients
  a(x,t) = γ₂(x,t) R*(x),  b(x,t) = γ₂(x,t) exp(s γ₁(x) u(x,t)).

This module removes the need to *assume* the derivative equations at the
finite-difference level.  It derives them from the existing a.e.-time
Carathéodory solution, requiring only the same local time integrability as
that solution.  No spatial differentiability of `a`, `b`, or `Y` is assumed.

First differences:
  (Y₁-Y₀)' = -a₁ (Y₁-Y₀) + (b₁-b₀) - (a₁-a₀) Y₀.

Mixed second differences (four points, indexed 00,10,01,11):
  (Y₁₁-Y₁₀-Y₀₁+Y₀₀)' = -a₁₁ (Y₁₁-Y₁₀-Y₀₁+Y₀₀)
       + (b₁₁-b₁₀-b₀₁+b₀₀)
       - (a₁₁-a₀₁)(Y₀₁-Y₀₀)
       - (a₁₁-a₁₀)(Y₁₀-Y₀₀)
       - (a₁₁-a₁₀-a₀₁+a₀₀) Y₀₀.

In the next step, translations in U_j and Sobolev difference-quotient estimates
will convert these identities into uniform L⁶ gradient / L² Hessian estimates,
then identify the weak spatial derivatives and finish local H²(U_j).
This module does NOT claim that final Sobolev identification yet.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The constructed reciprocal field at a spatial parameter `x`. -/
noncomputable def srReciprocalSpatialField
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x : X) (t : ℝ) : ℝ :=
  srReciprocalExplicit (a x) (b x) (y₀ x) t

/-- The first finite-difference equation, without assuming a spatial derivative.
All differentiability here is a.e. in **time**, obtained from the verified
Carathéodory construction. -/
theorem sr_reciprocal_first_difference_hasDerivAt_ae
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₁ x₀ : X) (T : ℝ) (hT : 0 ≤ T)
    (haInt : ∀ x, IntervalIntegrable (a x) volume (0 : ℝ) T)
    (hbInt : ∀ x,
      IntervalIntegrable
        (fun t : ℝ => Real.exp (srReciprocalPrimitive (a x) t) * b x t)
        volume (0 : ℝ) T) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt
        (fun v => srReciprocalSpatialField a b y₀ x₁ v -
          srReciprocalSpatialField a b y₀ x₀ v)
        (-a x₁ t * (srReciprocalSpatialField a b y₀ x₁ t -
            srReciprocalSpatialField a b y₀ x₀ t) +
          (b x₁ t - b x₀ t) -
          (a x₁ t - a x₀ t) * srReciprocalSpatialField a b y₀ x₀ t) t := by
  have h₁ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₁) (b x₁) (y₀ x₁) T hT (haInt x₁) (hbInt x₁)
  have h₀ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₀) (b x₀) (y₀ x₀) T hT (haInt x₀) (hbInt x₀)
  filter_upwards [h₁, h₀] with t ht₁ ht₀
  intro ht
  have hDiff := (ht₁ ht).sub (ht₀ ht)
  change HasDerivAt
    (fun v => srReciprocalSpatialField a b y₀ x₁ v -
      srReciprocalSpatialField a b y₀ x₀ v)
    ((-a x₁ t * srReciprocalSpatialField a b y₀ x₁ t + b x₁ t) -
     (-a x₀ t * srReciprocalSpatialField a b y₀ x₀ t + b x₀ t)) t
    at hDiff
  have hRing :
      ((-a x₁ t * srReciprocalSpatialField a b y₀ x₁ t + b x₁ t) -
       (-a x₀ t * srReciprocalSpatialField a b y₀ x₀ t + b x₀ t)) =
      -a x₁ t * (srReciprocalSpatialField a b y₀ x₁ t -
        srReciprocalSpatialField a b y₀ x₀ t) +
      (b x₁ t - b x₀ t) -
      (a x₁ t - a x₀ t) * srReciprocalSpatialField a b y₀ x₀ t := by
    ring
  rw [hRing] at hDiff
  exact hDiff

/-- The exact mixed second finite-difference equation, again proved from the
*constructed* reciprocal trajectories, not assumed as a PDE identity.
This is the algebraic content of the Hessian equation in Appendix A.2 and
is valid for any four spatial points; they will later be instantiated as
`x`, `x+h`, `x+k`, and `x+h+k` inside a well neighborhood. -/
theorem sr_reciprocal_mixed_second_difference_hasDerivAt_ae
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₀₀ x₁₀ x₀₁ x₁₁ : X) (T : ℝ) (hT : 0 ≤ T)
    (haInt : ∀ x, IntervalIntegrable (a x) volume (0 : ℝ) T)
    (hbInt : ∀ x,
      IntervalIntegrable
        (fun t : ℝ => Real.exp (srReciprocalPrimitive (a x) t) * b x t)
        volume (0 : ℝ) T) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt
        (fun v =>
          (srReciprocalSpatialField a b y₀ x₁₁ v -
           srReciprocalSpatialField a b y₀ x₁₀ v) -
          (srReciprocalSpatialField a b y₀ x₀₁ v -
           srReciprocalSpatialField a b y₀ x₀₀ v))
        (-a x₁₁ t *
            ((srReciprocalSpatialField a b y₀ x₁₁ t -
              srReciprocalSpatialField a b y₀ x₁₀ t) -
             (srReciprocalSpatialField a b y₀ x₀₁ t -
              srReciprocalSpatialField a b y₀ x₀₀ t)) +
          ((b x₁₁ t - b x₁₀ t) - (b x₀₁ t - b x₀₀ t)) -
          (a x₁₁ t - a x₀₁ t) *
            (srReciprocalSpatialField a b y₀ x₀₁ t -
             srReciprocalSpatialField a b y₀ x₀₀ t) -
          (a x₁₁ t - a x₁₀ t) *
            (srReciprocalSpatialField a b y₀ x₁₀ t -
             srReciprocalSpatialField a b y₀ x₀₀ t) -
          ((a x₁₁ t - a x₁₀ t) - (a x₀₁ t - a x₀₀ t)) *
            srReciprocalSpatialField a b y₀ x₀₀ t) t := by
  have h₀₀ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₀₀) (b x₀₀) (y₀ x₀₀) T hT (haInt x₀₀) (hbInt x₀₀)
  have h₁₀ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₁₀) (b x₁₀) (y₀ x₁₀) T hT (haInt x₁₀) (hbInt x₁₀)
  have h₀₁ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₀₁) (b x₀₁) (y₀ x₀₁) T hT (haInt x₀₁) (hbInt x₀₁)
  have h₁₁ := sr_reciprocal_explicit_hasDerivAt_ae
    (a x₁₁) (b x₁₁) (y₀ x₁₁) T hT (haInt x₁₁) (hbInt x₁₁)
  filter_upwards [h₀₀, h₁₀, h₀₁, h₁₁] with t ht₀₀ ht₁₀ ht₀₁ ht₁₁
  intro ht
  have hDiff := ((ht₁₁ ht).sub (ht₁₀ ht)).sub
    ((ht₀₁ ht).sub (ht₀₀ ht))
  change HasDerivAt
    (fun v =>
      (srReciprocalSpatialField a b y₀ x₁₁ v -
       srReciprocalSpatialField a b y₀ x₁₀ v) -
      (srReciprocalSpatialField a b y₀ x₀₁ v -
       srReciprocalSpatialField a b y₀ x₀₀ v))
    (((-a x₁₁ t * srReciprocalSpatialField a b y₀ x₁₁ t + b x₁₁ t) -
       (-a x₁₀ t * srReciprocalSpatialField a b y₀ x₁₀ t + b x₁₀ t)) -
      ((-a x₀₁ t * srReciprocalSpatialField a b y₀ x₀₁ t + b x₀₁ t) -
       (-a x₀₀ t * srReciprocalSpatialField a b y₀ x₀₀ t + b x₀₀ t))) t
    at hDiff
  have hRing :
      (((-a x₁₁ t * srReciprocalSpatialField a b y₀ x₁₁ t + b x₁₁ t) -
         (-a x₁₀ t * srReciprocalSpatialField a b y₀ x₁₀ t + b x₁₀ t)) -
        ((-a x₀₁ t * srReciprocalSpatialField a b y₀ x₀₁ t + b x₀₁ t) -
         (-a x₀₀ t * srReciprocalSpatialField a b y₀ x₀₀ t + b x₀₀ t))) =
      -a x₁₁ t *
          ((srReciprocalSpatialField a b y₀ x₁₁ t -
            srReciprocalSpatialField a b y₀ x₁₀ t) -
           (srReciprocalSpatialField a b y₀ x₀₁ t -
            srReciprocalSpatialField a b y₀ x₀₀ t)) +
        ((b x₁₁ t - b x₁₀ t) - (b x₀₁ t - b x₀₀ t)) -
        (a x₁₁ t - a x₀₁ t) *
          (srReciprocalSpatialField a b y₀ x₀₁ t -
           srReciprocalSpatialField a b y₀ x₀₀ t) -
        (a x₁₁ t - a x₁₀ t) *
          (srReciprocalSpatialField a b y₀ x₁₀ t -
           srReciprocalSpatialField a b y₀ x₀₀ t) -
        ((a x₁₁ t - a x₁₀ t) - (a x₀₁ t - a x₀₀ t)) *
          srReciprocalSpatialField a b y₀ x₀₀ t := by
    ring
  rw [hRing] at hDiff
  exact hDiff

#print axioms ReservoirSeismicityControl.sr_reciprocal_first_difference_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.sr_reciprocal_mixed_second_difference_hasDerivAt_ae

end ReservoirSeismicityControl
