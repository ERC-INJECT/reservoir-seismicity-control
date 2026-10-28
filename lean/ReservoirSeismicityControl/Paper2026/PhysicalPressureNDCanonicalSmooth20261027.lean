import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDRestrictedSmoothDensity20261027
import ReservoirSeismicityControl.Paper2026.PhysicalA7DimensionalWeakH2_20261027
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-!
# Actual smooth tests, physical divergence and canonical L² maps, for n_d=1,2,3

The old 3D smooth-test representation used genuine TestFunction fields,
continuous negative divergence and bounded-continuous-to-L² canonical maps.
This is their shared dimension-indexed construction on PaperSpatial n_d.
The standard smooth L² approximation is a separate accepted theorem;
the canonical embedding, divergence and representative identities are proved.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions ENNReal BoundedContinuousFunction BigOperators

variable {n_d : ℕ}

abbrev pressureNDSmoothVectorTests
    (Ω : Opens (Paper2026.PaperSpatial n_d)) :=
  TestFunction Ω (EuclideanSpace ℝ (Fin n_d)) ⊤

abbrev pressureNDSmoothScalarTests
    (Ω : Opens (Paper2026.PaperSpatial n_d)) :=
  TestFunction Ω ℝ ⊤

/-- Actual smooth negative divergence: -∑ᵢ ∂ᵢφᵢ. -/
noncomputable def pressureNDSmoothNegDiv
    (Ω : Opens (Paper2026.PaperSpatial n_d)) :
    pressureNDSmoothVectorTests Ω →L[ℝ] pressureNDSmoothScalarTests Ω :=
  -(∑ i : Fin n_d,
      (TestFunction.lineDerivCLM ℝ (Paper2026.paperCoordinateDirection i) :
        pressureNDSmoothScalarTests Ω →L[ℝ]
          pressureNDSmoothScalarTests Ω) ∘L
      (TestFunction.postcompCLM (EuclideanSpace.proj i) :
        pressureNDSmoothVectorTests Ω →L[ℝ]
          pressureNDSmoothScalarTests Ω))

/-- Inclusion from an open n_d-dimensional reservoir into the ambient space. -/
noncomputable def pressureNDDomainInclusion
    (Ω : Opens (Paper2026.PaperSpatial n_d)) :
    C(↥(Ω : Set (Paper2026.PaperSpatial n_d)), Paper2026.PaperSpatial n_d) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Genuine canonical smooth-to-L² embedding on the reservoir subtype. -/
noncomputable def pressureNDSmoothToL2CLM
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsFiniteMeasure μ] :
    TestFunction Ω F ⊤ →L[ℝ] Lp F 2 μ :=
  (BoundedContinuousFunction.toLp (E := F) (2 : ℝ≥0∞) μ ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM F ℝ
      (pressureNDDomainInclusion Ω)).comp
        (TestFunction.toBoundedContinuousFunctionCLM ℝ))

/-- Canonical smooth representative is precisely the actual test field a.e. -/
theorem pressure_nd_smooth_toL2_ae
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsFiniteMeasure μ] (φ : TestFunction Ω F ⊤) :
    ((pressureNDSmoothToL2CLM Ω μ F φ : Lp F 2 μ) :
      ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → F) =ᵐ[μ]
        fun x => φ x.val := by
  let b : (↥(Ω : Set (Paper2026.PaperSpatial n_d))) →ᵇ F :=
    (BoundedContinuousFunction.compContinuousCLM F ℝ
      (pressureNDDomainInclusion Ω))
        (TestFunction.toBoundedContinuousFunctionCLM ℝ φ)
  change ((BoundedContinuousFunction.toLp (E := F) (2 : ℝ≥0∞) μ ℝ b :
      Lp F 2 μ) : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → F) =ᵐ[μ]
        (b : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → F)
  exact BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) μ ℝ b

/-- The real n_d-component smooth vector test embedding. -/
noncomputable def pressureNDSmoothVectorL2Embed
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    [IsFiniteMeasure μ] :
    pressureNDSmoothVectorTests Ω →ₗ[ℝ]
      pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ :=
  (pressureNDSmoothToL2CLM Ω μ (EuclideanSpace ℝ (Fin n_d))).toLinearMap

/-- Canonical L² embedding of the actual negative divergence. -/
noncomputable def pressureNDSmoothNegDivL2
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    [IsFiniteMeasure μ] :
    pressureNDSmoothVectorTests Ω →ₗ[ℝ]
      pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ :=
  (pressureNDSmoothToL2CLM Ω μ ℝ).toLinearMap.comp
    (pressureNDSmoothNegDiv Ω).toLinearMap

/-- No assumed representative identification is needed for actual vectors. -/
theorem pressure_nd_smooth_vector_embed_ae
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    [IsFiniteMeasure μ] (φ : pressureNDSmoothVectorTests Ω) :
    ((pressureNDSmoothVectorL2Embed Ω μ φ :
      pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) :
      ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → EuclideanSpace ℝ (Fin n_d)) =ᵐ[μ]
      fun x => φ x.val :=
  pressure_nd_smooth_toL2_ae Ω μ (EuclideanSpace ℝ (Fin n_d)) φ

/-- The scalar divergence embedding is the actual smooth divergence a.e. -/
theorem pressure_nd_smooth_negDiv_embed_ae
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    [IsFiniteMeasure μ] (φ : pressureNDSmoothVectorTests Ω) :
    ((pressureNDSmoothNegDivL2 Ω μ φ :
      pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) :
      ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → ℝ) =ᵐ[μ]
        fun x => (pressureNDSmoothNegDiv Ω φ) x.val :=
  pressure_nd_smooth_toL2_ae Ω μ ℝ (pressureNDSmoothNegDiv Ω φ)

/-- Actual canonical n_d-dimensional scalar and vector smooth embeddings
are dense in physical L² under the standard interior approximation theorem.
No `DenseRange` premise on these embeddings is introduced. -/
theorem pressure_nd_canonical_smooth_vector_tests_dense
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set (Paper2026.PaperSpatial n_d)))
    (hApprox : ∀ (f : Paper2026.PaperSpatial n_d →
        EuclideanSpace ℝ (Fin n_d)),
      MemLp f 2 (ν.restrict (Ω : Set _)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ φ : pressureNDSmoothVectorTests Ω,
          eLpNorm (f - (φ : Paper2026.PaperSpatial n_d →
              EuclideanSpace ℝ (Fin n_d))) 2
            (ν.restrict (Ω : Set _)) ≤ ENNReal.ofReal ε) :
    (letI : IsFiniteMeasure (pressureNDRestrictedMeasure Ω ν) :=
      pressure_nd_restricted_measure_finite Ω ν hΩ
     DenseRange (pressureNDSmoothVectorL2Embed Ω
        (pressureNDRestrictedMeasure Ω ν) :
      pressureNDSmoothVectorTests Ω →
        pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d))
          (pressureNDRestrictedMeasure Ω ν))) := by
  letI := pressure_nd_restricted_measure_finite Ω ν hΩ
  exact pressure_nd_physical_smooth_tests_dense Ω ν
    (EuclideanSpace ℝ (Fin n_d))
    (pressureNDSmoothToL2CLM Ω (pressureNDRestrictedMeasure Ω ν)
      (EuclideanSpace ℝ (Fin n_d)))
    (pressure_nd_smooth_toL2_ae Ω (pressureNDRestrictedMeasure Ω ν)
      (EuclideanSpace ℝ (Fin n_d))) hApprox

/-- Same genuine geometric density statement for the scalar smooth tests. -/
theorem pressure_nd_canonical_smooth_scalar_tests_dense
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set (Paper2026.PaperSpatial n_d)))
    (hApprox : ∀ (f : Paper2026.PaperSpatial n_d → ℝ),
      MemLp f 2 (ν.restrict (Ω : Set _)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ φ : pressureNDSmoothScalarTests Ω,
          eLpNorm (f - (φ : Paper2026.PaperSpatial n_d → ℝ)) 2
            (ν.restrict (Ω : Set _)) ≤ ENNReal.ofReal ε) :
    (letI : IsFiniteMeasure (pressureNDRestrictedMeasure Ω ν) :=
      pressure_nd_restricted_measure_finite Ω ν hΩ
     DenseRange (pressureNDSmoothToL2CLM Ω
        (pressureNDRestrictedMeasure Ω ν) ℝ :
      pressureNDSmoothScalarTests Ω →
        pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d))
          (pressureNDRestrictedMeasure Ω ν))) := by
  letI := pressure_nd_restricted_measure_finite Ω ν hΩ
  exact pressure_nd_physical_smooth_tests_dense Ω ν ℝ
    (pressureNDSmoothToL2CLM Ω (pressureNDRestrictedMeasure Ω ν) ℝ)
    (pressure_nd_smooth_toL2_ae Ω (pressureNDRestrictedMeasure Ω ν) ℝ) hApprox

end ReservoirSeismicityControl
