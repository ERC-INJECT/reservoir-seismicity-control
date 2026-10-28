import ReservoirSeismicityControl.PressureNeumann3DSmoothA3Semigroup
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Canonical L² lift of compactly supported smooth 3D test fields

This module eliminates the assumed `embed` and `negDiv` linear maps in the
previous smooth-test realization. A smooth compactly supported test function
is a bounded continuous function on Euclidean 3-space. Restriction to the
reservoir subtype preserves bounded continuity. On any finite-measure
reservoir, Mathlib's `BoundedContinuousFunction.toLp` supplies a canonical
continuous linear map into L². The two almost-everywhere identification
statements are consequences of its `coeFn_toLp` theorem.

The reservoir measure is assumed finite here. A physically bounded reservoir
with restricted volume measure meets this requirement, but we do not prove
that particular measure-theoretic fact in this module.

This does not prove density of tests in L² or the scalar integration-by-parts
identity. Those remain separate analytical obligations.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions ENNReal BoundedContinuousFunction

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))

/-- Inclusion of reservoir points into ambient Euclidean three-space. -/
noncomputable def pressureNeumann3DDomainInclusion :
    C(↥(Ω : Set pressureNeumannE3), pressureNeumannE3) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The canonical linear L² lift of an actual smooth compactly supported
function on an open 3D reservoir. No free choice of embedding is involved. -/
noncomputable def pressureNeumann3DSmoothToL2CLM
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsFiniteMeasure μ] :
    TestFunction Ω F ⊤ →L[ℝ] Lp F 2 μ :=
  (BoundedContinuousFunction.toLp (E := F) (2 : ℝ≥0∞) μ ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM F ℝ
      (pressureNeumann3DDomainInclusion Ω)).comp
        (TestFunction.toBoundedContinuousFunctionCLM ℝ))

/-- Every canonical L² representative agrees almost everywhere with the
actual smooth test function restricted to Ω. -/
theorem pressure_neumann_3d_smooth_toL2_ae
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsFiniteMeasure μ] (φ : TestFunction Ω F ⊤) :
    ((pressureNeumann3DSmoothToL2CLM Ω μ F φ : Lp F 2 μ) :
      ↥(Ω : Set pressureNeumannE3) → F) =ᵐ[μ]
        fun x => φ x.val := by
  let b : (↥(Ω : Set pressureNeumannE3)) →ᵇ F :=
    (BoundedContinuousFunction.compContinuousCLM F ℝ
      (pressureNeumann3DDomainInclusion Ω))
        (TestFunction.toBoundedContinuousFunctionCLM ℝ φ)
  change ((BoundedContinuousFunction.toLp (E := F) (2 : ℝ≥0∞) μ ℝ b :
      Lp F 2 μ) : ↥(Ω : Set pressureNeumannE3) → F) =ᵐ[μ]
        (b : ↥(Ω : Set pressureNeumannE3) → F)
  exact BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) μ ℝ b

/-- The actual smooth vector test fields lifted into L²(Ω;ℝ³). -/
noncomputable def pressureNeumann3DSmoothVectorL2Embed [IsFiniteMeasure μ] :
    pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
      pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ :=
  (pressureNeumann3DSmoothToL2CLM Ω μ pressureNeumannE3).toLinearMap

/-- The actual smooth negative divergence lifted into scalar L²(Ω). -/
noncomputable def pressureNeumann3DSmoothNegDivL2 [IsFiniteMeasure μ] :
    pressureNeumann3DSmoothVectorTests Ω →ₗ[ℝ]
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ :=
  (pressureNeumann3DSmoothToL2CLM Ω μ ℝ).toLinearMap.comp
    (pressureNeumann3DSmoothNegDiv Ω).toLinearMap

/-- The vector embedding is the given pointwise field, almost everywhere. -/
theorem pressure_neumann_3d_smooth_vector_embed_ae [IsFiniteMeasure μ]
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    ((pressureNeumann3DSmoothVectorL2Embed Ω μ φ :
      pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) :
        ↥(Ω : Set pressureNeumannE3) → pressureNeumannE3) =ᵐ[μ]
          fun x => φ x.val :=
  pressure_neumann_3d_smooth_toL2_ae Ω μ pressureNeumannE3 φ

/-- The negative-divergence embedding is the actual distributional test
negative divergence, almost everywhere. -/
theorem pressure_neumann_3d_smooth_negDiv_embed_ae [IsFiniteMeasure μ]
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    ((pressureNeumann3DSmoothNegDivL2 Ω μ φ :
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) :
        ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[μ]
          fun x => (pressureNeumann3DSmoothNegDiv Ω φ) x.val :=
  pressure_neumann_3d_smooth_toL2_ae Ω μ ℝ
    (pressureNeumann3DSmoothNegDiv Ω φ)

end ReservoirSeismicityControl
