import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeVectorIBP
import ReservoirSeismicityControl.PressureNeumann3DBoundedDomainMeasure

/-!
# Physical vector integration by parts in the actual L² reservoir spaces

This file connects the already proved coordinate-wise physical-volume IBP
identity to the exact negative divergence and the exact smooth L² embeddings
used by the maximal weak-gradient and Neumann semigroup constructions.

There is no freely assumed smooth IBP witness. The witness for ψ is the actual
L² embedding of its smooth gradient, whose compact support was established
in `PressureNeumann3DPhysicalVolumeVectorIBP`.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped Distributions BigOperators InnerProductSpace

variable (Ω : Opens pressureNeumannE3)

/-- The gradient test constructed from the three smooth directional
    derivatives has the expected coordinate values. -/
theorem pressure_neumann_3d_physical_gradient_component
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (x : pressureNeumannE3) (i : Fin 3) :
    (pressureNeumann3DPhysicalSmoothGradient Ω ψ x) i =
      fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x
        (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  rw [pressure_neumann_3d_physical_smooth_gradient_apply]
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

/-- The actual smooth negative divergence equals the negative coordinate sum.
    No definition of divergence is changed or replaced here. -/
theorem pressure_neumann_3d_physical_neg_div_apply
    (φ : pressureNeumann3DSmoothVectorTests Ω)
    (x : pressureNeumannE3) :
    pressureNeumann3DSmoothNegDiv Ω φ x =
      -(∑ i : Fin 3,
          fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x
            (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  change -(∑ i : Fin 3,
      ((TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)))
        (pressureNeumann3DVectorTestComponent Ω i φ) :
          pressureNeumann3DSmoothScalarTests Ω) x) = _
  congr 1

/-- Products of two actual scalar smooth compactly supported test functions
    are integrable over the reservoir using physical Euclidean volume. -/
theorem pressure_neumann_3d_physical_test_product_integrable
    (ψ χ : pressureNeumann3DSmoothScalarTests Ω) :
    Integrable (fun x : pressureNeumannE3 => ψ x * χ x)
      ((volume : Measure pressureNeumannE3).restrict (Ω : Set pressureNeumannE3)) := by
  have h : Integrable (fun x : pressureNeumannE3 => ψ x * χ x)
      (volume : Measure pressureNeumannE3) :=
    (ψ.contDiff.continuous.mul χ.contDiff.continuous).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_right)
  exact h.mono_measure Measure.restrict_le_self

/-- The physical IBP formula written with the actual vector inner product
    and the actual test-function negative divergence. -/
theorem pressure_neumann_3d_physical_vector_integral_ibp
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (φ : pressureNeumann3DSmoothVectorTests Ω) :
    (∫ x in (Ω : Set pressureNeumannE3),
      ⟪φ x, pressureNeumann3DPhysicalSmoothGradient Ω ψ x⟫_ℝ
        ∂(volume : Measure pressureNeumannE3)) =
      (∫ x in (Ω : Set pressureNeumannE3),
        (pressureNeumann3DSmoothNegDiv Ω φ x) * ψ x
        ∂(volume : Measure pressureNeumannE3)) := by
  classical
  let e : Fin 3 → pressureNeumannE3 := fun i => EuclideanSpace.single i (1 : ℝ)
  let χ (i : Fin 3) := pressureNeumann3DVectorTestComponent Ω i φ
  let dχ (i : Fin 3) : pressureNeumann3DSmoothScalarTests Ω :=
    TestFunction.lineDerivCLM ℝ (e i) (χ i)
  let dψ (i : Fin 3) : pressureNeumann3DSmoothScalarTests Ω :=
    TestFunction.lineDerivCLM ℝ (e i) ψ
  have hχ (i : Fin 3) (x : pressureNeumannE3) : χ i x = (φ x) i :=
    pressure_neumann_3d_vector_component_apply Ω i φ x
  have hdχ (i : Fin 3) (x : pressureNeumannE3) :
      dχ i x = fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x (e i) := by
    change (TestFunction.lineDerivCLM ℝ (e i) (χ i) :
      pressureNeumann3DSmoothScalarTests Ω) x = _
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    have hfun : (χ i : pressureNeumannE3 → ℝ) =
        fun y : pressureNeumannE3 => (φ y) i := by
      funext y
      exact hχ i y
    rw [← hfun]
    exact ((χ i).contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  have hdψ (i : Fin 3) (x : pressureNeumannE3) :
      dψ i x = fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x (e i) := by
    change (TestFunction.lineDerivCLM ℝ (e i) ψ :
      pressureNeumann3DSmoothScalarTests Ω) x = _
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact (ψ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  have hIntLeft (i : Fin 3) :
      Integrable (fun x : pressureNeumannE3 =>
        ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x (e i))
        ((volume : Measure pressureNeumannE3).restrict (Ω : Set pressureNeumannE3)) := by
    simpa only [hdχ i] using
      pressure_neumann_3d_physical_test_product_integrable Ω ψ (dχ i)
  have hIntRight (i : Fin 3) :
      Integrable (fun x : pressureNeumannE3 =>
        fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x (e i) * (φ x) i)
        ((volume : Measure pressureNeumannE3).restrict (Ω : Set pressureNeumannE3)) := by
    simpa only [hdψ i, hχ i] using
      pressure_neumann_3d_physical_test_product_integrable Ω (dψ i) (χ i)
  have hPointInner (x : pressureNeumannE3) :
      ⟪φ x, pressureNeumann3DPhysicalSmoothGradient Ω ψ x⟫_ℝ =
        ∑ i : Fin 3,
          fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x (e i) * (φ x) i := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [pressure_neumann_3d_physical_gradient_component Ω ψ x i]
  have hPointNeg (x : pressureNeumannE3) :
      (pressureNeumann3DSmoothNegDiv Ω φ x) * ψ x =
        -(∑ i : Fin 3,
          ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x (e i)) := by
    rw [pressure_neumann_3d_physical_neg_div_apply Ω φ x]
    simp only [neg_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSum := pressure_neumann_3d_volume_vector_coordinate_sum_ibp Ω ψ φ
  calc
    (∫ x in (Ω : Set pressureNeumannE3),
      ⟪φ x, pressureNeumann3DPhysicalSmoothGradient Ω ψ x⟫_ℝ
        ∂(volume : Measure pressureNeumannE3)) =
      (∫ x in (Ω : Set pressureNeumannE3),
        ∑ i : Fin 3,
          fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x (e i) * (φ x) i
        ∂(volume : Measure pressureNeumannE3)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hPointInner
    _ = ∑ i : Fin 3,
        ∫ x in (Ω : Set pressureNeumannE3),
          fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x (e i) * (φ x) i
          ∂(volume : Measure pressureNeumannE3) := by
        exact integral_finsetSum _ (fun i _ => hIntRight i)
    _ = -(∑ i : Fin 3,
        ∫ x in (Ω : Set pressureNeumannE3),
          ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x (e i)
          ∂(volume : Measure pressureNeumannE3)) := by
        simpa only [neg_neg, e] using (congrArg Neg.neg hSum.symm)
    _ = (∫ x in (Ω : Set pressureNeumannE3),
          -(∑ i : Fin 3,
            ψ x * fderiv ℝ (fun y : pressureNeumannE3 => (φ y) i) x (e i))
          ∂(volume : Measure pressureNeumannE3)) := by
        rw [integral_neg, integral_finsetSum _ (fun i _ => hIntLeft i)]
    _ = (∫ x in (Ω : Set pressureNeumannE3),
        (pressureNeumann3DSmoothNegDiv Ω φ x) * ψ x
        ∂(volume : Measure pressureNeumannE3)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (hPointNeg x).symm)

/-- The required physical-volume smooth IBP witness, in the exact L² spaces
    and with exactly the canonical smooth-field and negative-divergence maps.
    The witness is the L² class of the genuine compactly supported gradient. -/
theorem pressure_neumann_3d_physical_smooth_ibp_l2
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (ψ : pressureNeumann3DSmoothScalarTests Ω) :
    ∃ g : pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
      (pressureNeumann3DRestrictedMeasure Ω
        (volume : Measure pressureNeumannE3)),
      ∀ φ : pressureNeumann3DSmoothVectorTests Ω,
        ⟪pressureNeumann3DRestrictedVectorL2Embed Ω
            (volume : Measure pressureNeumannE3) hΩ φ, g⟫_ℝ =
          ⟪pressureNeumann3DRestrictedNegDivL2 Ω
              (volume : Measure pressureNeumannE3) hΩ φ,
            pressureNeumann3DRestrictedScalarL2Embed Ω
              (volume : Measure pressureNeumannE3) hΩ ψ⟫_ℝ := by
  let μ := pressureNeumann3DRestrictedMeasure Ω
    (volume : Measure pressureNeumannE3)
  letI : IsFiniteMeasure μ :=
    pressure_neumann_3d_restricted_measure_finite Ω
      (volume : Measure pressureNeumannE3) hΩ
  let gradPsi := pressureNeumann3DPhysicalSmoothGradient Ω ψ
  refine ⟨pressureNeumann3DRestrictedVectorL2Embed Ω
    (volume : Measure pressureNeumannE3) hΩ gradPsi, ?_⟩
  intro φ
  change ⟪pressureNeumann3DSmoothVectorL2Embed Ω μ φ,
      pressureNeumann3DSmoothVectorL2Embed Ω μ gradPsi⟫_ℝ =
    ⟪pressureNeumann3DSmoothNegDivL2 Ω μ φ,
      pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ⟫_ℝ
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hφ := pressure_neumann_3d_smooth_vector_embed_ae Ω μ φ
  have hGrad := pressure_neumann_3d_smooth_vector_embed_ae Ω μ gradPsi
  have hdiv := pressure_neumann_3d_smooth_negDiv_embed_ae Ω μ φ
  have hψ := pressure_neumann_3d_smooth_toL2_ae Ω μ ℝ ψ
  calc
    (∫ x : ↥(Ω : Set pressureNeumannE3),
      ⟪(pressureNeumann3DSmoothVectorL2Embed Ω μ φ :
        pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) x,
        (pressureNeumann3DSmoothVectorL2Embed Ω μ gradPsi :
        pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) x⟫_ℝ ∂μ) =
      (∫ x : ↥(Ω : Set pressureNeumannE3),
        ⟪φ x.val, gradPsi x.val⟫_ℝ ∂μ) := by
          apply integral_congr_ae
          filter_upwards [hφ, hGrad] with x hx hy
          rw [hx, hy]
    _ = (∫ x in (Ω : Set pressureNeumannE3),
        ⟪φ x, gradPsi x⟫_ℝ ∂(volume : Measure pressureNeumannE3)) := by
          exact integral_subtype_comap
            (μ := (volume : Measure pressureNeumannE3))
            Ω.isOpen.measurableSet
            (fun y : pressureNeumannE3 =>
              ⟪(φ y : pressureNeumannE3), (gradPsi y : pressureNeumannE3)⟫_ℝ)
    _ = (∫ x in (Ω : Set pressureNeumannE3),
        (pressureNeumann3DSmoothNegDiv Ω φ x) * ψ x
        ∂(volume : Measure pressureNeumannE3)) :=
          pressure_neumann_3d_physical_vector_integral_ibp Ω ψ φ
    _ = (∫ x : ↥(Ω : Set pressureNeumannE3),
        (pressureNeumann3DSmoothNegDiv Ω φ x.val) * ψ x.val ∂μ) := by
          exact (integral_subtype_comap
            (μ := (volume : Measure pressureNeumannE3))
            Ω.isOpen.measurableSet
            (fun y : pressureNeumannE3 =>
              pressureNeumann3DSmoothNegDiv Ω φ y * ψ y)).symm
    _ = (∫ x : ↥(Ω : Set pressureNeumannE3),
        ⟪(pressureNeumann3DSmoothNegDivL2 Ω μ φ :
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) x,
          (pressureNeumann3DSmoothToL2CLM Ω μ ℝ ψ :
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) x⟫_ℝ ∂μ) := by
          apply integral_congr_ae
          filter_upwards [hdiv, hψ] with x hx hy
          rw [hx, hy]
          simp only [RCLike.inner_apply, conj_trivial]
          ring

end ReservoirSeismicityControl
