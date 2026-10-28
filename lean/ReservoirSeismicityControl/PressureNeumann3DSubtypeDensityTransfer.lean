import ReservoirSeismicityControl.PressureNeumann3DRestrictedInteriorTestApprox
import ReservoirSeismicityControl.PressureNeumann3DBoundedDomainMeasure
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Transfer of genuine interior smooth approximation to the reservoir subtype

The preceding approximation theorem uses the ambient space equipped with the
restricted measure `ν.restrict Ω`.  The canonical Neumann construction uses
`Lp` on the subtype `Ω` equipped with the pullback `ν.comap Subtype.val`.

We identify the two measures via the measurable subtype inclusion.  This
provides exact L² norm transport.  A zero extension of an arbitrary subtype
L² representative is again in ambient restricted L².  Applying the already
proved interior approximation then gives quantitative approximation of *any*
subtype L² vector/scalar field by genuine smooth tests.

This file does not yet prove `DenseRange` for the bundled canonical L² map;
that remaining final step is topological (from ε approximation to density).
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions ENNReal

variable (Ω : Opens pressureNeumannE3)
variable (ν : Measure pressureNeumannE3)

/-- The measurable inclusion of Ω pushes its pullback measure onto the
ambient measure restricted to Ω. -/
theorem pressure_neumann_3d_subtype_measure_preserving :
    MeasurePreserving
      (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3)
      (pressureNeumann3DRestrictedMeasure Ω ν)
      (ν.restrict (Ω : Set pressureNeumannE3)) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  exact map_comap_subtype_coe Ω.isOpen.measurableSet ν

/-- Exact eLp norm equality across the ambient and subtype pictures. -/
theorem pressure_neumann_3d_subtype_eLpNorm_eq
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : pressureNeumannE3 → F)
    (hf : AEStronglyMeasurable f (ν.restrict (Ω : Set pressureNeumannE3))) :
    eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => f x.val) 2
        (pressureNeumann3DRestrictedMeasure Ω ν) =
      eLpNorm f 2 (ν.restrict (Ω : Set pressureNeumannE3)) := by
  change eLpNorm (f ∘ (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3))
    2 (pressureNeumann3DRestrictedMeasure Ω ν) = _
  exact eLpNorm_comp_measurePreserving hf
    (pressure_neumann_3d_subtype_measure_preserving Ω ν)

/-- Extend a reservoir L² function by zero outside Ω. -/
noncomputable def pressureNeumann3DSubtypeZeroExtend
    (F : Type*) [NormedAddCommGroup F]
    (u : Lp F 2 (pressureNeumann3DRestrictedMeasure Ω ν)) :
    pressureNeumannE3 → F :=
  Function.extend
    (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3)
    (u : ↥(Ω : Set pressureNeumannE3) → F) 0

@[simp]
theorem pressure_neumann_3d_subtype_zero_extend_apply
    (F : Type*) [NormedAddCommGroup F]
    (u : Lp F 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (x : ↥(Ω : Set pressureNeumannE3)) :
    pressureNeumann3DSubtypeZeroExtend Ω ν F u x.val = u x := by
  simp [pressureNeumann3DSubtypeZeroExtend, Subtype.val_injective.extend_apply]

/-- An arbitrary subtype L² field admits an ambient representative supported
in Ω (zero outside), which belongs to L² for the restricted ambient measure. -/
theorem pressure_neumann_3d_subtype_zero_extend_memLp
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F 2 (pressureNeumann3DRestrictedMeasure Ω ν)) :
    MemLp (pressureNeumann3DSubtypeZeroExtend Ω ν F u) 2
      (ν.restrict (Ω : Set pressureNeumannE3)) := by
  let μ : Measure ↥(Ω : Set pressureNeumannE3) :=
    pressureNeumann3DRestrictedMeasure Ω ν
  let f : pressureNeumannE3 → F :=
    pressureNeumann3DSubtypeZeroExtend Ω ν F u
  have hfun : (f ∘ (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3)) =
      (u : ↥(Ω : Set pressureNeumannE3) → F) := by
    funext x
    exact pressure_neumann_3d_subtype_zero_extend_apply Ω ν F u x
  have hEmb : MeasurableEmbedding
      (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hmap : μ.map
      (Subtype.val : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3) =
      ν.restrict (Ω : Set pressureNeumannE3) :=
    map_comap_subtype_coe Ω.isOpen.measurableSet ν
  have hAS : AEStronglyMeasurable f (ν.restrict (Ω : Set pressureNeumannE3)) := by
    rw [← hmap]
    exact hEmb.aestronglyMeasurable_map_iff.mpr (by
      rw [hfun]
      exact Lp.aestronglyMeasurable u)
  change eLpNorm f 2 (ν.restrict (Ω : Set pressureNeumannE3)) < ∞
  rw [← eLpNorm_comp_measurePreserving hAS
    (pressure_neumann_3d_subtype_measure_preserving Ω ν), hfun]
  exact Lp.memLp u

variable [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]

/-- Arbitrary subtype L² vector fields admit quantitative approximations by
actual smooth vector test fields supported strictly inside Ω. -/
theorem pressure_neumann_3d_subtype_interior_vector_approx
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (u : Lp pressureNeumannE3 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothVectorTests Ω,
      eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        u x - φ x.val) 2 (pressureNeumann3DRestrictedMeasure Ω ν) ≤
          ENNReal.ofReal ε := by
  let f : pressureNeumannE3 → pressureNeumannE3 :=
    pressureNeumann3DSubtypeZeroExtend Ω ν pressureNeumannE3 u
  have hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)) :=
    pressure_neumann_3d_subtype_zero_extend_memLp Ω ν pressureNeumannE3 u
  obtain ⟨φ, happrox⟩ :=
    pressure_neumann_3d_restricted_interior_vector_approx Ω ν hΩ f hf hε
  refine ⟨φ, ?_⟩
  have hAS : AEStronglyMeasurable
      (f - (φ : pressureNeumannE3 → pressureNeumannE3))
      (ν.restrict (Ω : Set pressureNeumannE3)) :=
    hf.aestronglyMeasurable.sub φ.contDiff.continuous.aestronglyMeasurable
  have hfun : (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val) =
      (f - (φ : pressureNeumannE3 → pressureNeumannE3)) ∘ Subtype.val := by
    funext x
    change u x - φ x.val =
      pressureNeumann3DSubtypeZeroExtend Ω ν pressureNeumannE3 u x.val - φ x.val
    rw [pressure_neumann_3d_subtype_zero_extend_apply Ω ν pressureNeumannE3 u x]
  rw [hfun, eLpNorm_comp_measurePreserving hAS
    (pressure_neumann_3d_subtype_measure_preserving Ω ν)]
  exact happrox

/-- Scalar counterpart for arbitrary subtype L² pressure fields. -/
theorem pressure_neumann_3d_subtype_interior_scalar_approx
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (u : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω,
      eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        u x - φ x.val) 2 (pressureNeumann3DRestrictedMeasure Ω ν) ≤
          ENNReal.ofReal ε := by
  let f : pressureNeumannE3 → ℝ :=
    pressureNeumann3DSubtypeZeroExtend Ω ν ℝ u
  have hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)) :=
    pressure_neumann_3d_subtype_zero_extend_memLp Ω ν ℝ u
  obtain ⟨φ, happrox⟩ :=
    pressure_neumann_3d_restricted_interior_scalar_approx Ω ν hΩ f hf hε
  refine ⟨φ, ?_⟩
  have hAS : AEStronglyMeasurable (f - (φ : pressureNeumannE3 → ℝ))
      (ν.restrict (Ω : Set pressureNeumannE3)) :=
    hf.aestronglyMeasurable.sub φ.contDiff.continuous.aestronglyMeasurable
  have hfun : (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val) =
      (f - (φ : pressureNeumannE3 → ℝ)) ∘ Subtype.val := by
    funext x
    change u x - φ x.val =
      pressureNeumann3DSubtypeZeroExtend Ω ν ℝ u x.val - φ x.val
    rw [pressure_neumann_3d_subtype_zero_extend_apply Ω ν ℝ u x]
  rw [hfun, eLpNorm_comp_measurePreserving hAS
    (pressure_neumann_3d_subtype_measure_preserving Ω ν)]
  exact happrox

end ReservoirSeismicityControl
