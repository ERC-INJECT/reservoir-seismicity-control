import ReservoirSeismicityControl.PressureNeumann3DSmoothCanonicalL2

/-!
# Reduced analytic obligations for the physical 3D Neumann construction

Compared with `PressureNeumann3DSmoothL2Realization`, we no longer ask the
user to provide the L² embedding of smooth tests, the L² negative divergence,
or their almost-everywhere identification with pointwise tests. The previous
module canonically constructs all four from Mathlib's function-space maps,
under the explicit assumption that the reservoir measure is finite.

Only genuinely nontrivial density/core results remain as fields of the
record below. These are hypotheses, not established existence theorems.
Once supplied, the earlier completed graph and Neumann semigroup theorems
apply to the canonical smooth-test realization without arbitrary embeddings.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped InnerProductSpace

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))
variable [IsFiniteMeasure μ]

/-- The remaining analytic obligations for a *canonical* smooth-test L²
realization. In particular, `testsDense` and the integration-by-parts core
are not silently assumed as global axioms. -/
structure PressureNeumann3DSmoothL2AnalyticCore where
  testsDense : DenseRange
    (pressureNeumann3DSmoothVectorL2Embed Ω μ :
      pressureNeumann3DSmoothVectorTests Ω →
        pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ)
  core : Submodule ℝ
    (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
  coreGradient : core →ₗ[ℝ]
    pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ
  coreIBP : ∀ (φ : pressureNeumann3DSmoothVectorTests Ω) (u : core),
    ⟪pressureNeumann3DSmoothVectorL2Embed Ω μ φ, coreGradient u⟫_ℝ =
      ⟪pressureNeumann3DSmoothNegDivL2 Ω μ φ,
        (u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)⟫_ℝ
  coreDense : DenseRange
    (core.subtype : core →
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)

namespace PressureNeumann3DSmoothL2AnalyticCore

/-- Discharge the earlier realization's four embedding/AE data fields by
actual constructions. Only density and core properties are supplied here. -/
noncomputable def toRealization
    (r : PressureNeumann3DSmoothL2AnalyticCore Ω μ) :
    PressureNeumann3DSmoothL2Realization Ω μ where
  embed := pressureNeumann3DSmoothVectorL2Embed Ω μ
  negDiv := pressureNeumann3DSmoothNegDivL2 Ω μ
  testEmbedding_ae := pressure_neumann_3d_smooth_vector_embed_ae Ω μ
  divergenceEmbedding_ae := pressure_neumann_3d_smooth_negDiv_embed_ae Ω μ
  testsDense := r.testsDense
  core := r.core
  coreGradient := r.coreGradient
  coreIBP := r.coreIBP
  coreDense := r.coreDense

/-- Density of the maximal weak-H¹ candidate now follows from the reduced,
physical-core assumptions and the canonical L² realization. -/
theorem canonical_weak_H1_dense
    (r : PressureNeumann3DSmoothL2AnalyticCore Ω μ) :
    DenseRange
      ((pressureNeumann3DWeakH1Candidate μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ)).subtype :
          pressureNeumann3DWeakH1Candidate μ
            (pressureNeumann3DSmoothVectorL2Embed Ω μ)
            (pressureNeumann3DSmoothNegDivL2 Ω μ) →
              pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) :=
  (toRealization Ω μ r).weak_H1_dense Ω μ

/-- The canonical weak-gradient graph is exactly its Hilbert completion,
conditioned only on the remaining analytic-core record. -/
theorem canonical_graph_eq_completion
    (r : PressureNeumann3DSmoothL2AnalyticCore Ω μ) :
    pressureNeumannGraphHilbertDomain
      (pressureNeumann3DWeakH1Candidate μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ))
      (pressureNeumann3DWeakGradient μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ) r.testsDense) =
    pressureNeumann3DTestGraph μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ) := by
  exact (toRealization Ω μ r).graph_eq_completion Ω μ

end PressureNeumann3DSmoothL2AnalyticCore
end ReservoirSeismicityControl
