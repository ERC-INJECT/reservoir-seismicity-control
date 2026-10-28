import ReservoirSeismicityControl.PressureNeumann3DCanonicalTestDensity

/-!
# From smooth integration by parts to density of the maximal pressure domain

The scalar and vector C_c^∞ test embeddings are already proved dense in
L²(Ω) for a bounded open region and an inner-regular ambient measure.

The one additional analytic ingredient needed for maximal weak-pressure
core density is the *actual smooth integration-by-parts identity*:
for every smooth scalar test ψ there is an L² vector field g such that

    ⟪φ, g⟫ = ⟪-div φ, ψ⟫

for all compactly supported smooth vector tests φ.

This file proves two implications without assuming weak-pressure density:
* the above identity places each scalar test in the maximal weak-H¹ domain;
* since scalar tests are dense in L², the maximal weak-H¹ domain is dense.

WARNING: The smooth integration-by-parts property does not follow for an
arbitrary locally finite inner-regular measure. In the physical model the
measure must be specified as Euclidean volume (or a measure with a proven
corresponding weighted integration-by-parts identity). Proving this exact
identity for the chosen physical volume measure is a remaining task.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))
variable [IsFiniteMeasure μ]

/-- If a particular smooth scalar pressure ψ satisfies the genuine
weak integration-by-parts identity against every vector test, its L²
representative belongs to the maximal weak-gradient pressure domain. -/
theorem pressure_neumann_3d_smooth_pressure_mem_weak_H1_of_ibp
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (g : pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ)
    (hIBP : ∀ φ : pressureNeumann3DSmoothVectorTests Ω,
      ⟪pressureNeumann3DSmoothVectorL2Embed Ω μ φ, g⟫_ℝ =
        ⟪pressureNeumann3DSmoothNegDivL2 Ω μ φ,
          pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ⟫_ℝ) :
    (pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ :
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) ∈
      pressureNeumann3DWeakH1Candidate μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ) := by
  let u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ :=
    pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ
  let z : WithLp 2
      (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ ×
        pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) :=
    WithLp.toLp 2 (u, g)
  have hz : z ∈ pressureNeumann3DTestGraph μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ) := by
    apply (pressure_neumann_3d_test_graph_mem_iff μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ) z).2
    intro φ
    change
      ⟪pressureNeumann3DSmoothVectorL2Embed Ω μ φ, g⟫_ℝ =
        ⟪pressureNeumann3DSmoothNegDivL2 Ω μ φ, u⟫_ℝ
    exact hIBP φ
  change ∃ a : pressureNeumann3DTestGraph μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ),
    pressureNeumann3DWeakPressureProjection μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ) a =
        (pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ :
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
  refine ⟨⟨z, hz⟩, ?_⟩
  rfl

/-- Quantitative density of smooth scalar tests, together with the
smooth IBP property, proves density of the *actual maximal* weak-pressure
domain. This is not a restatement of the desired density as a premise. -/
theorem pressure_neumann_3d_weak_H1_dense_of_smooth_ibp
    (hScalarDense : DenseRange
      (pressureNeumann3DSmoothToL2CLM Ω μ ℝ :
        pressureNeumann3DSmoothScalarTests Ω →
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ))
    (hSmoothIBP : ∀ ψ : pressureNeumann3DSmoothScalarTests Ω,
      ∃ g : pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ,
        ∀ φ : pressureNeumann3DSmoothVectorTests Ω,
          ⟪pressureNeumann3DSmoothVectorL2Embed Ω μ φ, g⟫_ℝ =
            ⟪pressureNeumann3DSmoothNegDivL2 Ω μ φ,
              pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ⟫_ℝ) :
    DenseRange
      ((pressureNeumann3DWeakH1Candidate μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ)).subtype :
          pressureNeumann3DWeakH1Candidate μ
            (pressureNeumann3DSmoothVectorL2Embed Ω μ)
            (pressureNeumann3DSmoothNegDivL2 Ω μ) →
              pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  obtain ⟨ψ, hψ⟩ := (Metric.denseRange_iff.mp hScalarDense) u ε hε
  obtain ⟨g, hg⟩ := hSmoothIBP ψ
  have hmem := pressure_neumann_3d_smooth_pressure_mem_weak_H1_of_ibp
    Ω μ ψ g hg
  refine ⟨⟨pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ, hmem⟩, ?_⟩
  exact hψ

/-- For a specified bounded physical region and a locally finite,
inner-regular ambient measure, the only extra ingredient to establish
maximal weak-pressure density is the smooth distributional IBP identity.
This theorem intentionally exposes that analytic ingredient. -/
theorem pressure_neumann_3d_restricted_weak_H1_dense_of_smooth_ibp
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (hSmoothIBP : ∀ ψ : pressureNeumann3DSmoothScalarTests Ω,
      ∃ g : pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω ν),
        ∀ φ : pressureNeumann3DSmoothVectorTests Ω,
          ⟪pressureNeumann3DRestrictedVectorL2Embed Ω ν hΩ φ, g⟫_ℝ =
            ⟪pressureNeumann3DRestrictedNegDivL2 Ω ν hΩ φ,
              pressureNeumann3DRestrictedScalarL2Embed Ω ν hΩ ψ⟫_ℝ) :
    DenseRange
      ((pressureNeumann3DWeakH1Candidate
        (pressureNeumann3DRestrictedMeasure Ω ν)
        (pressureNeumann3DRestrictedVectorL2Embed Ω ν hΩ)
        (pressureNeumann3DRestrictedNegDivL2 Ω ν hΩ)).subtype :
          pressureNeumann3DWeakH1Candidate
            (pressureNeumann3DRestrictedMeasure Ω ν)
            (pressureNeumann3DRestrictedVectorL2Embed Ω ν hΩ)
            (pressureNeumann3DRestrictedNegDivL2 Ω ν hΩ) →
              pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
                (pressureNeumann3DRestrictedMeasure Ω ν)) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  apply pressure_neumann_3d_weak_H1_dense_of_smooth_ibp Ω
    (pressureNeumann3DRestrictedMeasure Ω ν)
  · change DenseRange (pressureNeumann3DRestrictedScalarL2Embed Ω ν hΩ :
      pressureNeumann3DSmoothScalarTests Ω →
        pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
          (pressureNeumann3DRestrictedMeasure Ω ν))
    exact pressure_neumann_3d_canonical_scalar_tests_dense Ω ν hΩ
  · intro ψ
    exact hSmoothIBP ψ

end ReservoirSeismicityControl
