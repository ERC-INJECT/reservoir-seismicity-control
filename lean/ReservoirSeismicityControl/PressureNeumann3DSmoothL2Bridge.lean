import ReservoirSeismicityControl.PressureNeumann3DSmoothTests

/-!
# L² realization and weak-gradient graph for genuine C_c^∞ tests

The fields and negative divergence are the actual smooth test objects from
`PressureNeumann3DSmoothTests`. To connect to Hilbert L²(Ω), we package the
remaining *analytic* facts in a structure. The structure is not an existence
theorem: constructing it for restricted Lebesgue measure is an open task.

Important: `testEmbedding_ae` and `divergenceEmbedding_ae` prohibit silently
replacing the negative divergence by an arbitrary L² linear map.
Density of compactly supported vector tests in L² and a dense scalar core
with integration by parts are independent obligations. The earlier general
theorems then yield a dense, single-valued, closed weak-gradient graph.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped InnerProductSpace

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))

/-- Precise pending requirements for lifting *actual* smooth compactly
supported 3D tests into L² of the reservoir. This contains no axioms and
makes no claim that all fields can yet be constructed from Mathlib.

For the intended reservoir, μ is volume on Ω, not an arbitrary measure.
The two AE fields force the lift to preserve pointwise fields and the
specific smooth negative divergence defined in the preceding module. -/
structure PressureNeumann3DSmoothL2Realization where
  embed : pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
    pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ
  negDiv : pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
    pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ
  testEmbedding_ae : ∀ φ,
    (embed φ : ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3) =ᵐ[μ]
      fun x => φ x.val
  divergenceEmbedding_ae : ∀ φ,
    (negDiv φ : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[μ]
      fun x => (pressureNeumann3DSmoothNegDiv Ω φ) x.val
  testsDense : DenseRange
    (embed : pressureNeumann3DSmoothVectorTests Ω →
      pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ)
  core : Submodule ℝ (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
  coreGradient : core →ₗ[ℝ]
    pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ
  coreIBP : ∀ (φ : pressureNeumann3DSmoothVectorTests Ω) (u : core),
    ⟪embed φ, coreGradient u⟫_ℝ =
      ⟪negDiv φ, (u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)⟫_ℝ
  coreDense : DenseRange
    (core.subtype : core → pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)

namespace PressureNeumann3DSmoothL2Realization

/-- The physical smooth scalar core, once supplied and verified, is included
in the maximal weak gradient domain. -/
theorem core_le_weak_H1
    (r : PressureNeumann3DSmoothL2Realization Ω μ) :
    r.core ≤ pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv :=
  pressure_neumann_3d_scalar_core_le_weak_H1 μ
    r.embed r.negDiv r.core r.coreGradient r.coreIBP

/-- The actual smooth scalar core gives density of the weak pressure domain.
Unlike earlier abstract semigroup results, this proof uses the explicit
scalar core in the realization record, not an independently assumed density. -/
theorem weak_H1_dense
    (r : PressureNeumann3DSmoothL2Realization Ω μ) :
    DenseRange
      ((pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv).subtype :
        pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv →
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) :=
  pressure_neumann_3d_weak_H1_dense_of_scalar_core μ
    r.embed r.negDiv r.core r.coreGradient r.coreIBP r.coreDense

/-- Concrete smooth test fields yield the completed Hilbert graph equality.
The analytic lifting conditions reside explicitly in the realization. -/
theorem graph_eq_completion
    (r : PressureNeumann3DSmoothL2Realization Ω μ) :
    pressureNeumannGraphHilbertDomain
      (pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv)
      (pressureNeumann3DWeakGradient μ r.embed r.negDiv r.testsDense) =
    pressureNeumann3DTestGraph μ r.embed r.negDiv :=
  pressure_neumann_3d_weak_graph_eq_test_graph μ r.embed r.negDiv r.testsDense

/-- The Hilbert gradient graph embedding has dense scalar range. -/
theorem graph_embedding_dense
    (r : PressureNeumann3DSmoothL2Realization Ω μ) :
    DenseRange (pressureNeumannGraphHilbertEmbedding
      (pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv)
      (pressureNeumann3DWeakGradient μ r.embed r.negDiv r.testsDense)) :=
  pressure_neumann_3d_weak_graph_embedding_dense μ r.embed r.negDiv
    r.testsDense (weak_H1_dense Ω μ r)

end PressureNeumann3DSmoothL2Realization
end ReservoirSeismicityControl
