import ReservoirSeismicityControl.PressurePositiveSemigroupFiniteCellCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# ReservoirSeismicityControl (A5): geometric facts for physical time intervals

Half-open time cells `Set.Ico a b` have precisely the geometric and measure
properties required by our L1 cell-average convergence theorem. In particular,
they have nonzero Lebesgue mass for `a < b`, finite mass, and a simple
left-endpoint radius bound. These statements require no derivative of the
well rate.

This is the interval-local step. The separate finite-mesh step will show
that the chosen time cells partition the entire time domain and their
maximum length tends to zero.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- An interval `[a,b)` has Lebesgue mass `b-a` when `a ≤ b`. -/
theorem pressure_time_Ico_real_mass (a b : ℝ) (hab : a ≤ b) :
    (volume.restrict (Set.Ico a b)).real Set.univ = b - a := by
  calc
    (volume.restrict (Set.Ico a b)).real Set.univ =
        volume.real (Set.Ico a b) :=
      measureReal_restrict_apply_univ _
    _ = b - a := Real.volume_real_Ico_of_le hab

/-- Strictly ordered endpoints give a nonzero interval measure.
This lets Mathlib's `average` normalize by the cell mass. -/
theorem pressure_time_Ico_nonzero (a b : ℝ) (hab : a < b) :
    NeZero (volume.restrict (Set.Ico a b)) := by
  apply neZero_iff.mpr
  intro hzero
  have hPos : 0 < (volume.restrict (Set.Ico a b)).real Set.univ := by
    rw [pressure_time_Ico_real_mass a b hab.le]
    exact sub_pos.mpr hab
  have hZeroMass : (volume.restrict (Set.Ico a b)).real Set.univ = 0 := by
    have h := congrArg (fun ν : Measure ℝ => ν.real Set.univ) hzero
    simpa using h
  exact (ne_of_gt hPos) hZeroMass

/-- A point of `[a,b)` lies within `b-a` of the left endpoint. -/
theorem pressure_time_Ico_left_radius {a b x : ℝ}
    (hx : x ∈ Set.Ico a b) : dist x a ≤ b - a := by
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  linarith [hx.2]

/-- The preceding radius bound holds almost everywhere under the cell measure. -/
theorem pressure_time_Ico_left_radius_ae (a b : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Set.Ico a b)), dist x a ≤ b - a := by
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  exact pressure_time_Ico_left_radius hx

/-- Time intervals ordered from left to right are disjoint if they do not overlap. -/
theorem pressure_time_Ico_disjoint {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint (Set.Ico a b) (Set.Ico c d) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hbx : b ≤ x := le_trans hbc hy.1
  exact (not_lt_of_ge hbx) hx.2

/-- Every finite time cell `[a,b)` has a finite Lebesgue measure. -/
theorem pressure_time_Ico_finite (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Ico a b)) := inferInstance

end ReservoirSeismicityControl
