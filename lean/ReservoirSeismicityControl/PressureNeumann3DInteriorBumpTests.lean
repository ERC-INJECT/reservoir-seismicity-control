import ReservoirSeismicityControl.PressureNeumann3DRestrictedAmbientDensity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Actual interior smooth test fields on a three-dimensional open domain

For every point of Ω and every open neighborhood of that point, construct a
compactly supported smooth scalar test function taking value 1 at the point,
and a compactly supported smooth vector test field taking an arbitrary
specified vector value there. Their supports lie in the chosen neighborhood
*and* in Ω. No density, regularity of the boundary or integration-by-parts
assumption is used here.

These are local building blocks for the later density argument. Existence of
local bumps alone does not prove density in L².
-/

namespace ReservoirSeismicityControl

open TopologicalSpace
open scoped Distributions

variable (Ω : Opens pressureNeumannE3)

/-- An interior bump function supported inside an arbitrarily small open
neighborhood of a point of the reservoir. -/
theorem pressure_neumann_3d_exists_interior_scalar_bump
    (U : Set pressureNeumannE3) (hU : IsOpen U)
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3))
    (hxU : x ∈ U) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω,
      φ x = 1 ∧
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆ U ∧
      ∀ y : pressureNeumannE3, 0 ≤ φ y ∧ φ y ≤ 1 := by
  have hOpen : IsOpen ((Ω : Set pressureNeumannE3) ∩ U) := Ω.isOpen.inter hU
  have hInside : x ∈ ((Ω : Set pressureNeumannE3) ∩ U) := ⟨hx, hxU⟩
  obtain ⟨f, hSupp, hCompact, hSmooth, hRange, hOne⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (hOpen.mem_nhds hInside)
  let φ : pressureNeumann3DSmoothScalarTests Ω :=
    ⟨f, hSmooth, hCompact, hSupp.trans Set.inter_subset_left⟩
  refine ⟨φ, hOne, hSupp.trans Set.inter_subset_right, ?_⟩
  intro y
  exact hRange (Set.mem_range_self y)

/-- In particular, a positive scalar smooth bump exists at every interior
point, without requiring a separate neighborhood choice. -/
theorem pressure_neumann_3d_exists_scalar_bump
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3)) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω, φ x = 1 := by
  obtain ⟨φ, hφ, _, _⟩ :=
    pressure_neumann_3d_exists_interior_scalar_bump Ω
      (Ω : Set pressureNeumannE3) Ω.isOpen x hx hx
  exact ⟨φ, hφ⟩

/-- A smooth vector test field with arbitrary prescribed value at one point,
with compact support in a chosen open neighborhood inside Ω. -/
theorem pressure_neumann_3d_exists_interior_vector_bump
    (U : Set pressureNeumannE3) (hU : IsOpen U)
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3))
    (hxU : x ∈ U) (v : pressureNeumannE3) :
    ∃ φ : pressureNeumann3DSmoothVectorTests Ω,
      φ x = v ∧
      tsupport (φ : pressureNeumannE3 → pressureNeumannE3) ⊆ U := by
  obtain ⟨ψ, hψ, hSupp, _⟩ :=
    pressure_neumann_3d_exists_interior_scalar_bump Ω U hU x hx hxU
  let φ : pressureNeumann3DSmoothVectorTests Ω :=
    ⟨fun y => ψ y • v,
      ψ.contDiff.smul_const v,
      ψ.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (ψ : pressureNeumannE3 → ℝ)
        (fun _ => v)).trans ψ.tsupport_subset⟩
  refine ⟨φ, ?_, ?_⟩
  · change ψ x • v = v
    rw [hψ, one_smul]
  · exact (tsupport_smul_subset_left (ψ : pressureNeumannE3 → ℝ)
      (fun _ => v)).trans hSupp

/-- Pointwise nontriviality of smooth vector tests on the reservoir. -/
theorem pressure_neumann_3d_exists_vector_bump
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3))
    (v : pressureNeumannE3) :
    ∃ φ : pressureNeumann3DSmoothVectorTests Ω, φ x = v := by
  obtain ⟨φ, hφ, _⟩ :=
    pressure_neumann_3d_exists_interior_vector_bump Ω
      (Ω : Set pressureNeumannE3) Ω.isOpen x hx hx v
  exact ⟨φ, hφ⟩

end ReservoirSeismicityControl
