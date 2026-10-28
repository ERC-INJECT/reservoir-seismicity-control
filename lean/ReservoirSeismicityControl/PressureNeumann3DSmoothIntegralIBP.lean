import ReservoirSeismicityControl.PressureNeumann3DBoundedDomainMeasure

/-!
# The canonical weak-gradient identity is the distributional integral identity

The older abstract graph formulation uses Hilbert-space inner products.
Here we show that, for the *actual* compactly supported smooth tests and
their canonical L2 representatives, this identity is exactly the usual
Bochner integral of the pointwise vector field against the L2 gradient,
with the genuine smooth negative divergence on the other side.

The theorem requires density of the vector tests to make the weak gradient
single-valued. It does NOT prove this density.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped InnerProductSpace

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))
variable [IsFiniteMeasure μ]

/-- Exact pointwise distributional identity for the canonical smooth
realization, conditional only on test-field density. -/
theorem pressure_neumann_3d_canonical_weak_gradient_integral_ibp
    (hTest : DenseRange
      (pressureNeumann3DSmoothVectorL2Embed Ω μ :
        pressureNeumann3DSmoothVectorTests Ω →
          pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ))
    (φ : pressureNeumann3DSmoothVectorTests Ω)
    (u : pressureNeumann3DWeakH1Candidate μ
      (pressureNeumann3DSmoothVectorL2Embed Ω μ)
      (pressureNeumann3DSmoothNegDivL2 Ω μ)) :
    (∫ x : ↥(Ω : Set pressureNeumannE3),
      inner ℝ (φ x.val)
        ((pressureNeumann3DWeakGradient μ
          (pressureNeumann3DSmoothVectorL2Embed Ω μ)
          (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest u :
            pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) x) ∂μ) =
    (∫ x : ↥(Ω : Set pressureNeumannE3),
      inner ℝ ((pressureNeumann3DSmoothNegDiv Ω φ) x.val)
        ((u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) x) ∂μ) := by
  have h := pressure_neumann_3d_weak_gradient_ibp μ
    (pressureNeumann3DSmoothVectorL2Embed Ω μ)
    (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest φ u
  simp only [MeasureTheory.L2.inner_def] at h
  calc
    (∫ x : ↥(Ω : Set pressureNeumannE3),
      inner ℝ (φ x.val)
        ((pressureNeumann3DWeakGradient μ
          (pressureNeumann3DSmoothVectorL2Embed Ω μ)
          (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest u :
            pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) x) ∂μ) =
      (∫ x : ↥(Ω : Set pressureNeumannE3),
        inner ℝ ((pressureNeumann3DSmoothVectorL2Embed Ω μ φ) x)
          ((pressureNeumann3DWeakGradient μ
            (pressureNeumann3DSmoothVectorL2Embed Ω μ)
            (pressureNeumann3DSmoothNegDivL2 Ω μ) hTest u) x) ∂μ) := by
          apply integral_congr_ae
          filter_upwards [pressure_neumann_3d_smooth_vector_embed_ae Ω μ φ] with x hx
          simp [hx]
    _ = (∫ x : ↥(Ω : Set pressureNeumannE3),
        inner ℝ ((pressureNeumann3DSmoothNegDivL2 Ω μ φ) x)
          ((u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) x) ∂μ) := h
    _ = (∫ x : ↥(Ω : Set pressureNeumannE3),
        inner ℝ ((pressureNeumann3DSmoothNegDiv Ω φ) x.val)
          ((u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) x) ∂μ) := by
          apply integral_congr_ae
          filter_upwards [pressure_neumann_3d_smooth_negDiv_embed_ae Ω μ φ] with x hx
          simp [hx]

end ReservoirSeismicityControl
