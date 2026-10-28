import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeCoordinateIBP

/-!
# From coordinate IBP to the physical vector-gradient/divergence pairing

Unlike an abstract integration-by-parts hypothesis, all the tests here are
actual `C_c^∞(Ω)` functions and the measure is actual Euclidean `volume`.
The scalar coordinate IBP theorem in the imported module is the analytic input.

The first two theorems prove IBP for each projected component of a vector test
and for the complete sum of three coordinates. A test-function-valued gradient
and an explicit pointwise formula for negative divergence are then constructed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped Distributions BigOperators InnerProductSpace

variable (Ω : Opens pressureNeumannE3)

/-- The `i`-th component of a smooth compactly supported vector test is a
smooth compactly supported scalar test on the same domain. -/
noncomputable def pressureNeumann3DVectorTestComponent (i : Fin 3) :
    pressureNeumann3DSmoothVectorTests Ω →L[ℝ]
      pressureNeumann3DSmoothScalarTests Ω :=
  TestFunction.postcompCLM (EuclideanSpace.proj i)

@[simp]
theorem pressure_neumann_3d_vector_component_apply
    (i : Fin 3) (φ : pressureNeumann3DSmoothVectorTests Ω)
    (x : pressureNeumannE3) :
    pressureNeumann3DVectorTestComponent Ω i φ x = φ x i := by
  change (EuclideanSpace.proj i) (φ x) = (φ x) i
  rfl

/-- Genuine physical-volume integration by parts for one component of an
arbitrary smooth vector test field. -/
theorem pressure_neumann_3d_volume_vector_component_ibp
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (φ : pressureNeumann3DSmoothVectorTests Ω) (i : Fin 3) :
    (∫ x in (Ω : Set pressureNeumannE3),
      ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x
        (EuclideanSpace.single i (1 : ℝ))
      ∂(volume : Measure pressureNeumannE3)) =
      -(∫ x in (Ω : Set pressureNeumannE3),
        fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x
          (EuclideanSpace.single i (1 : ℝ)) * (φ x) i
        ∂(volume : Measure pressureNeumannE3)) := by
  let χ := pressureNeumann3DVectorTestComponent Ω i φ
  have hχ : (χ : pressureNeumannE3 → ℝ) = fun x => (φ x) i := by
    funext x
    exact pressure_neumann_3d_vector_component_apply Ω i φ x
  have h := pressure_neumann_3d_volume_coordinate_ibp_on_domain Ω ψ χ i
  rw [hχ] at h
  exact h

/-- The three-dimensional coordinate sum, with no additional boundary or
integrability assumptions beyond the actual compactly supported smooth tests. -/
theorem pressure_neumann_3d_volume_vector_coordinate_sum_ibp
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    (∑ i : Fin 3,
      ∫ x in (Ω : Set pressureNeumannE3),
        ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x
          (EuclideanSpace.single i (1 : ℝ))
        ∂(volume : Measure pressureNeumannE3)) =
      -(∑ i : Fin 3,
        ∫ x in (Ω : Set pressureNeumannE3),
          fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x
            (EuclideanSpace.single i (1 : ℝ)) * (φ x) i
          ∂(volume : Measure pressureNeumannE3)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact pressure_neumann_3d_volume_vector_component_ibp Ω ψ φ i

/-- Assemble the three coordinate derivatives into an actual smooth,
compactly supported vector test. This packages smoothness and support
without a separate approximation or existence assumption. -/
noncomputable def pressureNeumann3DPhysicalSmoothGradient :
    pressureNeumann3DSmoothScalarTests Ω →L[ℝ]
      pressureNeumann3DSmoothVectorTests Ω :=
  ∑ i : Fin 3,
    (TestFunction.postcompCLM
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (EuclideanSpace.single i (1 : ℝ))) :
      pressureNeumann3DSmoothScalarTests Ω →L[ℝ]
        pressureNeumann3DSmoothVectorTests Ω) ∘L
    (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) :
      pressureNeumann3DSmoothScalarTests Ω →L[ℝ]
        pressureNeumann3DSmoothScalarTests Ω)

/-- A pointwise formula for the physically constructed smooth gradient. -/
theorem pressure_neumann_3d_physical_smooth_gradient_apply
    (ψ : pressureNeumann3DSmoothScalarTests Ω) (x : pressureNeumannE3) :
    pressureNeumann3DPhysicalSmoothGradient Ω ψ x =
      ∑ i : Fin 3,
        (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
          (EuclideanSpace.single i (1 : ℝ)) •
            (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  have hder (i : Fin 3) :
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ))
        ψ : pressureNeumann3DSmoothScalarTests Ω) x =
        (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
          (EuclideanSpace.single i (1 : ℝ)) := by
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact (ψ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  simp only [pressureNeumann3DPhysicalSmoothGradient,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    Finset.sum_apply, TestFunction.postcompCLM_apply,
    Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self]
  congr 1

end ReservoirSeismicityControl
