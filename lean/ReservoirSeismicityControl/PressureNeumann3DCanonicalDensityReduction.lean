import ReservoirSeismicityControl.PressureNeumann3DSmoothIntegralIBP

/-!
# Only two density statements remain in the canonical smooth-test core

The prior analytic-core record contains a scalar core, its gradient, and an
integration-by-parts condition. These are not *independent* obligations.
Whenever the actual vector tests have dense image in L2 and the maximal
weak-gradient pressure domain is dense in scalar L2, we may select the
maximal weak-gradient domain itself as the scalar core. Its gradient and
integration-by-parts equation are already constructed and proved.

Conversely, an existing analytic core entails exactly these two densities.
We prove the equivalence, eliminating arbitrary scalar-core choices.
This is a reduction of remaining obligations, not a proof of the densities.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped InnerProductSpace

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))
variable [IsFiniteMeasure μ]

/-- The canonical core built from the entire maximal weak-gradient domain.
It requires just the two genuine density results, rather than user-supplied
scalar core, gradient, and integration-by-parts data. -/
noncomputable def pressureNeumann3DAnalyticCoreOfTwoDensities
    (hTest : DenseRange
      (pressureNeumann3DSmoothVectorL2Embed Ω μ :
        pressureNeumann3DSmoothVectorTests Ω →
          pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ))
    (hPressure : DenseRange
      ((pressureNeumann3DWeakH1Candidate μ
        (pressureNeumann3DSmoothVectorL2Embed Ω μ)
        (pressureNeumann3DSmoothNegDivL2 Ω μ)).subtype :
          pressureNeumann3DWeakH1Candidate μ
            (pressureNeumann3DSmoothVectorL2Embed Ω μ)
            (pressureNeumann3DSmoothNegDivL2 Ω μ) →
              pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)) :
    PressureNeumann3DSmoothL2AnalyticCore Ω μ where
  testsDense := hTest
  core := pressureNeumann3DWeakH1Candidate μ
    (pressureNeumann3DSmoothVectorL2Embed Ω μ)
    (pressureNeumann3DSmoothNegDivL2 Ω μ)
  coreGradient := pressureNeumann3DWeakGradient μ
    (pressureNeumann3DSmoothVectorL2Embed Ω μ)
    (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest
  coreIBP := by
    intro φ u
    exact pressure_neumann_3d_weak_gradient_ibp μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest φ u
  coreDense := hPressure

/-- The original analytic-core record exists if and only if the *two*
real density obligations hold. This identifies the exact remaining input
for the existing canonical Neumann semigroup bridge. -/
theorem pressure_neumann_3d_analytic_core_iff_two_densities :
    Nonempty (PressureNeumann3DSmoothL2AnalyticCore Ω μ) ↔
      ∃ hTest : DenseRange
        (pressureNeumann3DSmoothVectorL2Embed Ω μ :
          pressureNeumann3DSmoothVectorTests Ω →
            pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ),
      DenseRange
        ((pressureNeumann3DWeakH1Candidate μ
          (pressureNeumann3DSmoothVectorL2Embed Ω μ)
          (pressureNeumann3DSmoothNegDivL2 Ω μ)).subtype :
            pressureNeumann3DWeakH1Candidate μ
              (pressureNeumann3DSmoothVectorL2Embed Ω μ)
              (pressureNeumann3DSmoothNegDivL2 Ω μ) →
                pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.testsDense,
      PressureNeumann3DSmoothL2AnalyticCore.canonical_weak_H1_dense Ω μ r⟩
  · rintro ⟨hTest, hPressure⟩
    exact ⟨pressureNeumann3DAnalyticCoreOfTwoDensities Ω μ hTest hPressure⟩

end ReservoirSeismicityControl
