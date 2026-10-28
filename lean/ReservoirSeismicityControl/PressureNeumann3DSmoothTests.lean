import ReservoirSeismicityControl.PressureNeumann3DScalarCoreBridge
import Mathlib.Analysis.Distribution.TestFunction

/-!
# Concrete smooth compactly supported vector tests in 3D

Mathlib already implements the bundled test functions `TestFunction Ω F ⊤`.
Here Ω is an *open subset of Euclidean ℝ³*, not an arbitrary type of
abstract tests. Each vector test is smooth, compactly supported and has
support contained in Ω. Its (negative) divergence is constructed as a
continuous linear map of test-function spaces using coordinate projections
and directional derivatives. There are no extra smoothness assumptions.

This module does NOT yet turn these tests into L²(Ω) equivalence classes.
That requires a measure and a proof that the restriction of each test and
its divergence belongs to L², preserving linearity. Those missing links
must be proved before the abstract weak gradient can be called the
physical Sobolev gradient.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace
open scoped Distributions BigOperators

abbrev pressureNeumannE3 := EuclideanSpace ℝ (Fin 3)

/-- Genuine smooth compactly supported vector test fields inside Ω. -/
abbrev pressureNeumann3DSmoothVectorTests (Ω : Opens pressureNeumannE3) :=
  TestFunction Ω pressureNeumannE3 ⊤

/-- Genuine smooth compactly supported scalar test functions inside Ω. -/
abbrev pressureNeumann3DSmoothScalarTests (Ω : Opens pressureNeumannE3) :=
  TestFunction Ω ℝ ⊤

variable (Ω : Opens pressureNeumannE3)

/-- Vector tests are smooth (not merely abstract elements of a vector space). -/
theorem pressure_neumann_3d_smooth_vector_test_contDiff
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (φ : pressureNeumannE3 → pressureNeumannE3) :=
  φ.contDiff

/-- Vector tests have compact support. -/
theorem pressure_neumann_3d_smooth_vector_test_compact
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    HasCompactSupport (φ : pressureNeumannE3 → pressureNeumannE3) :=
  φ.hasCompactSupport

/-- Vector test support lies in the open physical domain Ω. -/
theorem pressure_neumann_3d_smooth_vector_test_support
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    tsupport (φ : pressureNeumannE3 → pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3) :=
  φ.tsupport_subset

/-- The physical negative divergence of compactly supported smooth vector
fields, as a continuous linear operator between test-function spaces.
For φ : Ω → ℝ³, the result equals `-∑ i ∂ᵢ φᵢ`. -/
noncomputable def pressureNeumann3DSmoothNegDiv :
    pressureNeumann3DSmoothVectorTests Ω →L[ℝ]
      pressureNeumann3DSmoothScalarTests Ω :=
  -(∑ i : Fin 3,
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) :
        pressureNeumann3DSmoothScalarTests Ω →L[ℝ]
          pressureNeumann3DSmoothScalarTests Ω) ∘L
      (TestFunction.postcompCLM (EuclideanSpace.proj i) :
        pressureNeumann3DSmoothVectorTests Ω →L[ℝ]
          pressureNeumann3DSmoothScalarTests Ω))

/-- Negative divergence is linear in its test field. -/
theorem pressure_neumann_3d_smooth_neg_div_add
    (φ ψ : pressureNeumann3DSmoothVectorTests Ω) :
    pressureNeumann3DSmoothNegDiv Ω (φ + ψ) =
      pressureNeumann3DSmoothNegDiv Ω φ +
        pressureNeumann3DSmoothNegDiv Ω ψ :=
  map_add (pressureNeumann3DSmoothNegDiv Ω) φ ψ

/-- The scalar negative divergence is also smooth and compactly supported
in Ω, by construction of the TestFunction codomain. -/
theorem pressure_neumann_3d_smooth_neg_div_compact
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    HasCompactSupport
      (pressureNeumann3DSmoothNegDiv Ω φ : pressureNeumannE3 → ℝ) :=
  (pressureNeumann3DSmoothNegDiv Ω φ).hasCompactSupport

theorem pressure_neumann_3d_smooth_neg_div_support
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    tsupport (pressureNeumann3DSmoothNegDiv Ω φ : pressureNeumannE3 → ℝ) ⊆
      (Ω : Set pressureNeumannE3) :=
  (pressureNeumann3DSmoothNegDiv Ω φ).tsupport_subset

end ReservoirSeismicityControl
