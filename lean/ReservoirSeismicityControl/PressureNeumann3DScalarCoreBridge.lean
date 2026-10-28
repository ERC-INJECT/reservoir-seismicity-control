import ReservoirSeismicityControl.PressureNeumann3DWeakH1A3Semigroup

/-!
# The remaining scalar density condition reduces to a concrete smooth core

Given any scalar test core D with gradient G, if its integration-by-parts
identity against vector test fields holds, then D is included in the maximal
weak-H¹ candidate. If D is dense in scalar L², the maximal weak domain is
automatically dense. On D, the unique maximal weak gradient equals G.

For the physical Ω this reduces the outstanding analytic work to the familiar
smooth-core facts, not an unmotivated assumption about the maximal graph.
This file does NOT prove smoothness, test-field density, or the physical
integration-by-parts identity for the chosen domain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- A scalar core whose gradient satisfies distributional integration by parts
is contained in the maximal weak-H¹ candidate. -/
theorem pressure_neumann_3d_scalar_core_le_weak_H1
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (D : Submodule ℝ (pressureNeumann3DScalarL2 Ω μ))
    (G : D →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (hIBP : ∀ φ : Φ, ∀ u : D,
      ⟪embed φ, G u⟫_ℝ = ⟪negDiv φ, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ) :
    D ≤ pressureNeumann3DWeakH1Candidate μ embed negDiv := by
  intro u hu
  let v : D := ⟨u, hu⟩
  let z := pressureNeumannTestGraphMap D G v
  have hz : z ∈ pressureNeumann3DTestGraph μ embed negDiv := by
    apply (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv z).2
    intro φ
    change ⟪embed φ, G v⟫_ℝ = ⟪negDiv φ, (v : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ
    exact hIBP φ v
  let x : pressureNeumann3DTestGraph μ embed negDiv := ⟨z, hz⟩
  change u ∈ LinearMap.range
    (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap
  refine ⟨x, ?_⟩
  change (WithLp.fstL 2 ℝ _ _) z = u
  rfl

/-- Density of an explicit scalar core implies density of the maximal weak
pressure domain. The latter does not need an independently assumed density. -/
theorem pressure_neumann_3d_weak_H1_dense_of_scalar_core
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (D : Submodule ℝ (pressureNeumann3DScalarL2 Ω μ))
    (G : D →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (hIBP : ∀ φ : Φ, ∀ u : D,
      ⟪embed φ, G u⟫_ℝ = ⟪negDiv φ, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ)
    (hDDense : DenseRange (D.subtype : D → pressureNeumann3DScalarL2 Ω μ)) :
    DenseRange ((pressureNeumann3DWeakH1Candidate μ embed negDiv).subtype :
      pressureNeumann3DWeakH1Candidate μ embed negDiv →
        pressureNeumann3DScalarL2 Ω μ) := by
  let M := pressureNeumann3DWeakH1Candidate μ embed negDiv
  have hIncl : D ≤ M :=
    pressure_neumann_3d_scalar_core_le_weak_H1 μ embed negDiv D G hIBP
  let incl : D →ₗ[ℝ] M := D.subtype.codRestrict M (fun v => hIncl v.property)
  have hcomp : ((M.subtype : M → pressureNeumann3DScalarL2 Ω μ) ∘ incl) =
      (D.subtype : D → pressureNeumann3DScalarL2 Ω μ) := by
    funext v
    rfl
  have hcompDense : DenseRange
      ((M.subtype : M → pressureNeumann3DScalarL2 Ω μ) ∘ incl) := by
    rw [hcomp]
    exact hDDense
  exact DenseRange.of_comp hcompDense

/-- The maximal distributional gradient agrees with the scalar core
gradient, assuming density of the vector tests. -/
theorem pressure_neumann_3d_weak_gradient_agrees_on_core
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hTestsDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (D : Submodule ℝ (pressureNeumann3DScalarL2 Ω μ))
    (G : D →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (hIBP : ∀ φ : Φ, ∀ u : D,
      ⟪embed φ, G u⟫_ℝ = ⟪negDiv φ, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ)
    (v : D) :
    pressureNeumann3DWeakGradient μ embed negDiv hTestsDense
      ⟨(v : pressureNeumann3DScalarL2 Ω μ),
        pressure_neumann_3d_scalar_core_le_weak_H1
          μ embed negDiv D G hIBP v.property⟩ = G v := by
  let z := pressureNeumannTestGraphMap D G v
  have hz : z ∈ pressureNeumann3DTestGraph μ embed negDiv := by
    apply (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv z).2
    intro φ
    change ⟪embed φ, G v⟫_ℝ = ⟪negDiv φ, (v : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ
    exact hIBP φ v
  have h := pressure_neumann_3d_weak_gradient_on_graph μ embed negDiv
    hTestsDense (⟨z, hz⟩ : pressureNeumann3DTestGraph μ embed negDiv)
  change pressureNeumann3DWeakGradient μ embed negDiv hTestsDense
      ⟨(v : pressureNeumann3DScalarL2 Ω μ),
        pressure_neumann_3d_scalar_core_le_weak_H1
          μ embed negDiv D G hIBP v.property⟩ = G v at h
  exact h

end ReservoirSeismicityControl
