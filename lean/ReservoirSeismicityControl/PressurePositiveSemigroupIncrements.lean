import ReservoirSeismicityControl.PressurePositiveOperatorStepBound
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive increments of self-adjoint contraction semigroups

For a self-adjoint contraction semigroup `S` on a real Hilbert space,
`S t` is positive, and so is `S t - S (t+h)` for nonnegative times.

The key identity is
`S t - S (t+h) = (S (t/2))† ∘L (I-S h) ∘L S (t/2)`.

This result does not construct the physical semigroup or its Duhamel
representation. In particular, self-adjointness of its operators is
an explicit premise, not inferred here from its generator.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

section AbstractSemigroup

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A self-adjoint contraction has positive complementary operator. -/
theorem pressure_one_sub_symmetric_contraction_positive
    (T : H →L[ℝ] H)
    (hSelf : IsSelfAdjoint T)
    (hContract : ∀ x : H, ‖T x‖ ≤ ‖x‖) :
    ((1 : H →L[ℝ] H) - T).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).2
  refine ⟨(IsSelfAdjoint.one (H →L[ℝ] H)).sub hSelf, ?_⟩
  intro x
  have hInner : ⟪T x, x⟫_ℝ ≤ ‖x‖ ^ 2 := by
    calc
      ⟪T x, x⟫_ℝ ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right (hContract x) (norm_nonneg x)
      _ = ‖x‖ ^ 2 := by ring
  change 0 ≤ ⟪x - T x, x⟫_ℝ
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

/-- Every member of a self-adjoint semigroup is a positive operator. -/
theorem pressure_selfadjoint_semigroup_positive
    (S : NNReal → H →L[ℝ] H)
    (hSemigroup : ∀ s t : NNReal, S (s + t) = (S s) ∘L (S t))
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (t : NNReal) :
    (S t).IsPositive := by
  let V : H →L[ℝ] H := S (t / 2)
  have hTime : S t = V ∘L V := by
    simpa only [add_halves, V] using hSemigroup (t / 2) (t / 2)
  have hFactor : S t = V.adjoint ∘L (1 : H →L[ℝ] H) ∘L V := by
    rw [hTime, (hSelf (t / 2)).adjoint_eq]
    ext x
    simp [ContinuousLinearMap.comp_apply, V]
  rw [hFactor]
  exact ContinuousLinearMap.isPositive_one.adjoint_conj V

/-- Nonnegative increments of a self-adjoint contraction semigroup. -/
theorem pressure_selfadjoint_contraction_semigroup_increment_positive
    (S : NNReal → H →L[ℝ] H)
    (hSemigroup : ∀ s t : NNReal, S (s + t) = (S s) ∘L (S t))
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (hContract : ∀ (t : NNReal) (x : H), ‖S t x‖ ≤ ‖x‖)
    (t h : NNReal) :
    (S t - S (t + h)).IsPositive := by
  let V : H →L[ℝ] H := S (t / 2)
  have hTime : S t = V ∘L V := by
    simpa only [add_halves, V] using hSemigroup (t / 2) (t / 2)
  have hRearrange : t + h = (t / 2) + (h + t / 2) := by
    calc
      t + h = (t / 2 + t / 2) + h := by rw [add_halves]
      _ = t / 2 + (h + t / 2) := by ac_rfl
  have hTimeH : S (t + h) = V ∘L ((S h) ∘L V) := by
    calc
      S (t + h) = S ((t / 2) + (h + t / 2)) := by rw [hRearrange]
      _ = S (t / 2) ∘L S (h + t / 2) := hSemigroup _ _
      _ = V ∘L ((S h) ∘L V) := by rw [hSemigroup]
  have hFactor :
      S t - S (t + h) =
        V.adjoint ∘L ((1 : H →L[ℝ] H) - S h) ∘L V := by
    rw [hTime, hTimeH, (hSelf (t / 2)).adjoint_eq]
    ext x
    simp [ContinuousLinearMap.comp_apply, V]
  rw [hFactor]
  exact (pressure_one_sub_symmetric_contraction_positive
    (S h) (hSelf h) (hContract h)).adjoint_conj V

end AbstractSemigroup

end ReservoirSeismicityControl
