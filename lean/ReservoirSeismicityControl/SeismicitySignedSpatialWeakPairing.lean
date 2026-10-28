import ReservoirSeismicityControl.SeismicitySignedSpatialDifferenceQuotients
import ReservoirSeismicityControl.SeismicitySignedSpatialHessianForcingBound
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# M1 — Spatial weak pairing of the *constructed* signed SR reciprocal

Let `Y(x,t)` be the explicit signed reciprocal field already constructed,
not a postulated spatially differentiable solution. For a spatial increment `h`
and any integrable test pair `φ`, translation invariance yields the exact
weak (distributional) difference identity

    ∫ ((Y(x+h,t) - Y(x,t))/δ) φ(x) dμ
      = ∫ Y(x,t) ((φ(x-h)-φ(x))/δ) dμ.

This is the integration-by-parts identity from which weak derivative
identification follows after taking spatial difference-quotient limits.
It works on an additive Haar-measure space, hence in particular for the
ambient three-dimensional Lebesgue measure. The local U_j argument will
use compactly supported tests and zero extensions, avoiding boundary terms.

This module does not assume gradients of Y or differentiability of a,b in x.
It also does not assert the final H² theorem: weak compactness and passage
to spatial limits remain to be proved.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The integral of the first spatial difference paired against a test
function equals the integral with the shift transferred onto the test
function. This is the key exact integration-by-parts step for weak
spatial derivatives; no derivatives of `Y` are assumed. -/
theorem sr_spatial_first_difference_weak_pairing
    {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddRightInvariant]
    (Y φ : G → ℝ) (h : G)
    (hForward : Integrable (fun x : G => Y (x + h) * φ x) μ)
    (hBase : Integrable (fun x : G => Y x * φ x) μ)
    (hBackward : Integrable (fun x : G => Y x * φ (x - h)) μ) :
    (∫ x, (Y (x + h) * φ x - Y x * φ x) ∂μ) =
      ∫ x, (Y x * φ (x - h) - Y x * φ x) ∂μ := by
  have hShift :
      (∫ x, Y (x + h) * φ x ∂μ) =
        ∫ x, Y x * φ (x - h) ∂μ := by
    have hChange := integral_add_right_eq_self
      (fun x : G => Y x * φ (x - h)) h (μ := μ)
    simpa only [add_sub_cancel_right] using hChange
  calc
    (∫ x, (Y (x + h) * φ x - Y x * φ x) ∂μ) =
        (∫ x, Y (x + h) * φ x ∂μ) -
          (∫ x, Y x * φ x ∂μ) :=
          integral_sub hForward hBase
    _ = (∫ x, Y x * φ (x - h) ∂μ) -
          (∫ x, Y x * φ x ∂μ) := by rw [hShift]
    _ = ∫ x, (Y x * φ (x - h) - Y x * φ x) ∂μ :=
          (integral_sub hBackward hBase).symm

/-- The precise *normalized* weak pairing identity for the spatial
first difference quotient of the constructed signed reciprocal solution.
The divisor `δ` may be any real scalar; no assumption `δ ≠ 0` is needed
for this algebraic integral identity. -/
theorem sr_signed_reciprocal_first_quotient_weak_pairing
    {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddRightInvariant]
    (a b : G → ℝ → ℝ) (y₀ : G → ℝ)
    (t δ : ℝ) (h : G) (φ : G → ℝ)
    (hForward : Integrable
      (fun x : G => srReciprocalSpatialField a b y₀ (x + h) t * φ x) μ)
    (hBase : Integrable
      (fun x : G => srReciprocalSpatialField a b y₀ x t * φ x) μ)
    (hBackward : Integrable
      (fun x : G => srReciprocalSpatialField a b y₀ x t * φ (x - h)) μ) :
    (∫ x, srReciprocalFirstQuotient a b y₀ (x + h) x δ t * φ x ∂μ) =
      ∫ x, srReciprocalSpatialField a b y₀ x t *
        ((φ (x - h) - φ x) / δ) ∂μ := by
  let Y : G → ℝ := fun x => srReciprocalSpatialField a b y₀ x t
  have hRaw := sr_spatial_first_difference_weak_pairing
    μ Y φ h hForward hBase hBackward
  calc
    (∫ x, srReciprocalFirstQuotient a b y₀ (x + h) x δ t * φ x ∂μ) =
        ∫ x, δ⁻¹ * (Y (x + h) * φ x - Y x * φ x) ∂μ := by
          congr 1
          funext x
          dsimp [Y, srReciprocalFirstQuotient]
          ring
    _ = δ⁻¹ * (∫ x, (Y (x + h) * φ x - Y x * φ x) ∂μ) :=
          integral_const_mul _ _
    _ = δ⁻¹ * (∫ x, (Y x * φ (x - h) - Y x * φ x) ∂μ) := by
          rw [hRaw]
    _ = ∫ x, δ⁻¹ * (Y x * φ (x - h) - Y x * φ x) ∂μ :=
          (integral_const_mul _ _).symm
    _ = ∫ x, srReciprocalSpatialField a b y₀ x t *
          ((φ (x - h) - φ x) / δ) ∂μ := by
          congr 1
          funext x
          dsimp [Y]
          ring

#print axioms ReservoirSeismicityControl.sr_spatial_first_difference_weak_pairing
#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_first_quotient_weak_pairing

end ReservoirSeismicityControl
