import ReservoirSeismicityControl.PressureNeumann3DSmoothCanonicalRealization
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Restricting a locally finite 3D ambient measure to a bounded reservoir

We construct the measure on the subtype of reservoir points by pulling
back a specified ambient measure on R^3. If that measure is finite on
compact sets, the restriction to a bounded reservoir is finite.

IMPORTANT: This module does NOT identify the ambient measure with
Euclidean Lebesgue measure. Mathlib's EuclideanSpace is a PiLp type and
does not have a default `MeasureSpace` instance. The physical volume
measure must be supplied separately.

This file does not assert test-field density or Sobolev identification.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped ENNReal

/-- Restrict a specified ambient measure to the subtype of reservoir points. -/
noncomputable def pressureNeumann3DRestrictedMeasure
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3) :
    Measure (Ω : Set pressureNeumannE3) :=
  ν.comap Subtype.val

/-- The mass of the subtype measure equals the ambient measure of the region. -/
theorem pressure_neumann_3d_restricted_measure_univ
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3) :
    pressureNeumann3DRestrictedMeasure Ω ν Set.univ =
      ν (Ω : Set pressureNeumannE3) := by
  unfold pressureNeumann3DRestrictedMeasure
  rw [comap_subtype_coe_apply Ω.isOpen.measurableSet]
  simp

/-- Bounded reservoirs have finite restricted measure when the specified
ambient measure is finite on compact sets. -/
theorem pressure_neumann_3d_restricted_measure_finite
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν) := by
  refine ⟨?_⟩
  rw [pressure_neumann_3d_restricted_measure_univ]
  exact hΩ.measure_lt_top

/-- The canonical L2 vector-test embedding on the restricted finite measure. -/
noncomputable def pressureNeumann3DRestrictedVectorL2Embed
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3) [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
      pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω ν) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  exact pressureNeumann3DSmoothVectorL2Embed Ω (pressureNeumann3DRestrictedMeasure Ω ν)

/-- The canonical L2 negative-divergence embedding on the restricted measure. -/
noncomputable def pressureNeumann3DRestrictedNegDivL2
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3) [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω ν) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  exact pressureNeumann3DSmoothNegDivL2 Ω (pressureNeumann3DRestrictedMeasure Ω ν)

end ReservoirSeismicityControl
