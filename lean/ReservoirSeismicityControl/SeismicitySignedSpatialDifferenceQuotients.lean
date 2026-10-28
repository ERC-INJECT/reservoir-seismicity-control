import ReservoirSeismicityControl.SeismicitySignedSpatialFiniteDifferences
import Mathlib.Tactic

/-!
# M1 — normalized first and mixed second spatial differences of the constructed SR reciprocal

`Y(x,t) = srReciprocalSpatialField a b y₀ x t` is the already constructed
Carathéodory reciprocal, with the *signed* SR coefficient
`b(x,t) = γ₂(x,t) * exp(s * γ₁(x) * u(x,t))`.

This module derives, without spatial smoothness or a bound on `Qdot`, the
**normalized** first and mixed second difference-quotient equations. It also
bounds the algebraic forcing terms by the corresponding coefficient and
lower-order difference-quotient bounds.

The bounds in this module are scalar inequalities at individual spatial
points. The full local H²(U_j) theorem is NOT established here: to make its
hypotheses follow from the manuscript's H² coefficient assumptions one still
needs L⁶/L² difference-quotient inequalities on interior subdomains, spatial
integration, uniform-in-time damping estimates, and weak compactness.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Normalized first spatial difference of the constructed reciprocal. -/
noncomputable def srReciprocalFirstQuotient
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₁ x₀ : X) (h : ℝ) (t : ℝ) : ℝ :=
  (srReciprocalSpatialField a b y₀ x₁ t -
    srReciprocalSpatialField a b y₀ x₀ t) / h

/-- The first quotient solves a damped, forced linear equation a.e. in time.
Its forcing is a difference quotient of `b` minus the quotient of `a`
multiplied by the *actual* reciprocal solution at the base point. -/
theorem sr_reciprocal_first_quotient_hasDerivAt_ae
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₁ x₀ : X) (h T : ℝ) (hT : 0 ≤ T)
    (haInt : ∀ x, IntervalIntegrable (a x) volume (0 : ℝ) T)
    (hbInt : ∀ x,
      IntervalIntegrable
        (fun t : ℝ => Real.exp (srReciprocalPrimitive (a x) t) * b x t)
        volume (0 : ℝ) T) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (srReciprocalFirstQuotient a b y₀ x₁ x₀ h)
        (-a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
          (b x₁ t - b x₀ t) / h -
          ((a x₁ t - a x₀ t) / h) *
            srReciprocalSpatialField a b y₀ x₀ t) t := by
  have hDiff := sr_reciprocal_first_difference_hasDerivAt_ae
    a b y₀ x₁ x₀ T hT haInt hbInt
  filter_upwards [hDiff] with t ht
  intro htTime
  have hbase := ht htTime
  have hscaled := hbase.const_mul (h⁻¹)
  change HasDerivAt
    (fun v => h⁻¹ *
      (srReciprocalSpatialField a b y₀ x₁ v -
        srReciprocalSpatialField a b y₀ x₀ v))
    (h⁻¹ *
      (-a x₁ t * (srReciprocalSpatialField a b y₀ x₁ t -
          srReciprocalSpatialField a b y₀ x₀ t) +
        (b x₁ t - b x₀ t) -
        (a x₁ t - a x₀ t) * srReciprocalSpatialField a b y₀ x₀ t)) t
    at hscaled
  have hEq :
      h⁻¹ *
        (-a x₁ t * (srReciprocalSpatialField a b y₀ x₁ t -
            srReciprocalSpatialField a b y₀ x₀ t) +
          (b x₁ t - b x₀ t) -
          (a x₁ t - a x₀ t) * srReciprocalSpatialField a b y₀ x₀ t) =
      -a x₁ t * srReciprocalFirstQuotient a b y₀ x₁ x₀ h t +
        (b x₁ t - b x₀ t) / h -
        ((a x₁ t - a x₀ t) / h) *
          srReciprocalSpatialField a b y₀ x₀ t := by
    simp only [srReciprocalFirstQuotient, div_eq_mul_inv]
    ring
  rw [hEq] at hscaled
  have hFun :
      (fun v => h⁻¹ *
        (srReciprocalSpatialField a b y₀ x₁ v -
          srReciprocalSpatialField a b y₀ x₀ v)) =
      srReciprocalFirstQuotient a b y₀ x₁ x₀ h := by
    funext v
    simp only [srReciprocalFirstQuotient, div_eq_mul_inv]
    ring
  rw [hFun] at hscaled
  exact hscaled

/-- A uniform scalar bound for the *physical* first-quotient forcing.
The needed coefficient differences are later estimated in L⁶, not as
pointwise L∞ bounds, when working under Assumption 3. -/
theorem sr_reciprocal_first_quotient_forcing_abs_le
    (da db y A B Ymax : ℝ)
    (hA : |da| ≤ A) (hB : |db| ≤ B) (hY : |y| ≤ Ymax)
    (hA0 : 0 ≤ A) :
    |db - da * y| ≤ B + A * Ymax := by
  have hMul : |da * y| ≤ A * Ymax := by
    rw [abs_mul]
    exact mul_le_mul hA hY (abs_nonneg _) hA0
  calc
    |db - da * y| ≤ |db| + |da * y| := abs_sub _ _
    _ ≤ B + A * Ymax := add_le_add hB hMul

/-- Normalized mixed second spatial difference at four points. -/
noncomputable def srReciprocalSecondQuotient
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₀₀ x₁₀ x₀₁ x₁₁ : X) (h k : ℝ) (t : ℝ) : ℝ :=
  ((srReciprocalSpatialField a b y₀ x₁₁ t -
      srReciprocalSpatialField a b y₀ x₁₀ t) -
    (srReciprocalSpatialField a b y₀ x₀₁ t -
      srReciprocalSpatialField a b y₀ x₀₀ t)) / (h * k)

/-- The second quotient equation is a.e. in time and exact, with both
cross-products of first differences of `a` and `Y` explicitly present.
No spatial differentiability is assumed. -/
theorem sr_reciprocal_second_quotient_hasDerivAt_ae
    {X : Type*} (a b : X → ℝ → ℝ) (y₀ : X → ℝ)
    (x₀₀ x₁₀ x₀₁ x₁₁ : X) (h k T : ℝ) (hT : 0 ≤ T)
    (haInt : ∀ x, IntervalIntegrable (a x) volume (0 : ℝ) T)
    (hbInt : ∀ x,
      IntervalIntegrable
        (fun t : ℝ => Real.exp (srReciprocalPrimitive (a x) t) * b x t)
        volume (0 : ℝ) T) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (srReciprocalSecondQuotient a b y₀ x₀₀ x₁₀ x₀₁ x₁₁ h k)
        (-a x₁₁ t * srReciprocalSecondQuotient a b y₀ x₀₀ x₁₀ x₀₁ x₁₁ h k t +
          ((b x₁₁ t - b x₁₀ t) - (b x₀₁ t - b x₀₀ t)) / (h * k) -
          ((a x₁₁ t - a x₀₁ t) / h) *
            srReciprocalFirstQuotient a b y₀ x₀₁ x₀₀ k t -
          ((a x₁₁ t - a x₁₀ t) / k) *
            srReciprocalFirstQuotient a b y₀ x₁₀ x₀₀ h t -
          (((a x₁₁ t - a x₁₀ t) - (a x₀₁ t - a x₀₀ t)) / (h * k)) *
            srReciprocalSpatialField a b y₀ x₀₀ t) t := by
  have hDiff := sr_reciprocal_mixed_second_difference_hasDerivAt_ae
    a b y₀ x₀₀ x₁₀ x₀₁ x₁₁ T hT haInt hbInt
  filter_upwards [hDiff] with t ht
  intro htTime
  have hbase := ht htTime
  have hscaled := hbase.const_mul ((h * k)⁻¹)
  have hEq :
      (h * k)⁻¹ *
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
           srReciprocalSpatialField a b y₀ x₀₀ t) =
      -a x₁₁ t * srReciprocalSecondQuotient a b y₀ x₀₀ x₁₀ x₀₁ x₁₁ h k t +
        ((b x₁₁ t - b x₁₀ t) - (b x₀₁ t - b x₀₀ t)) / (h * k) -
        ((a x₁₁ t - a x₀₁ t) / h) *
          srReciprocalFirstQuotient a b y₀ x₀₁ x₀₀ k t -
        ((a x₁₁ t - a x₁₀ t) / k) *
          srReciprocalFirstQuotient a b y₀ x₁₀ x₀₀ h t -
        (((a x₁₁ t - a x₁₀ t) - (a x₀₁ t - a x₀₀ t)) / (h * k)) *
          srReciprocalSpatialField a b y₀ x₀₀ t := by
    simp only [srReciprocalSecondQuotient, srReciprocalFirstQuotient,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hEq] at hscaled
  have hFun :
      (fun v => (h * k)⁻¹ *
        ((srReciprocalSpatialField a b y₀ x₁₁ v -
            srReciprocalSpatialField a b y₀ x₁₀ v) -
          (srReciprocalSpatialField a b y₀ x₀₁ v -
            srReciprocalSpatialField a b y₀ x₀₀ v))) =
      srReciprocalSecondQuotient a b y₀ x₀₀ x₁₀ x₀₁ x₁₁ h k := by
    funext v
    simp only [srReciprocalSecondQuotient, div_eq_mul_inv]
    ring
  rw [hFun] at hscaled
  exact hscaled

/-- Triangle/product estimate for the mixed-quotient forcing. The pair of
first-order product terms is the discrete version of the Hessian cross term.
In the physical H² argument they are bounded in L² via L⁶ × L⁶ → L³
and the bounded-volume inclusion L³ → L². -/
theorem sr_reciprocal_second_quotient_forcing_abs_le
    (b₂ ah ak a₂ yh yk y : ℝ)
    (B₂ Ah Ak A₂ Gh Gk YM : ℝ)
    (hb : |b₂| ≤ B₂) (hah : |ah| ≤ Ah) (hak : |ak| ≤ Ak)
    (ha₂ : |a₂| ≤ A₂) (hyh : |yh| ≤ Gh) (hyk : |yk| ≤ Gk)
    (hy : |y| ≤ YM)
    (hAh : 0 ≤ Ah) (hAk : 0 ≤ Ak) (hA₂ : 0 ≤ A₂) :
    |b₂ - ah * yk - ak * yh - a₂ * y| ≤
      B₂ + Ah * Gk + Ak * Gh + A₂ * YM := by
  have h1 : |ah * yk| ≤ Ah * Gk := by
    rw [abs_mul]
    exact mul_le_mul hah hyk (abs_nonneg _) hAh
  have h2 : |ak * yh| ≤ Ak * Gh := by
    rw [abs_mul]
    exact mul_le_mul hak hyh (abs_nonneg _) hAk
  have h3 : |a₂ * y| ≤ A₂ * YM := by
    rw [abs_mul]
    exact mul_le_mul ha₂ hy (abs_nonneg _) hA₂
  have hBase : |b₂ - ah * yk - ak * yh - a₂ * y| ≤
      |b₂| + |ah * yk| + |ak * yh| + |a₂ * y| := by
    calc
      |b₂ - ah * yk - ak * yh - a₂ * y| ≤
        |b₂ - ah * yk - ak * yh| + |a₂ * y| := abs_sub _ _
      _ ≤ (|b₂ - ah * yk| + |ak * yh|) + |a₂ * y| := by
        have htri : |(b₂ - ah * yk) - ak * yh| ≤
            |b₂ - ah * yk| + |ak * yh| :=
          abs_sub (b₂ - ah * yk) (ak * yh)
        linarith only [htri]
      _ ≤ (|b₂| + |ah * yk| + |ak * yh|) + |a₂ * y| := by
        have hz := abs_sub b₂ (ah * yk)
        linarith
      _ = _ := by ring
  linarith

#print axioms ReservoirSeismicityControl.sr_reciprocal_first_quotient_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.sr_reciprocal_first_quotient_forcing_abs_le
#print axioms ReservoirSeismicityControl.sr_reciprocal_second_quotient_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.sr_reciprocal_second_quotient_forcing_abs_le

end ReservoirSeismicityControl
