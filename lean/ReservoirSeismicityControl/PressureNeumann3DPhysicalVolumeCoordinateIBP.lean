import ReservoirSeismicityControl.PressureNeumann3DWeakPressureCoreFromIBP
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Physical Euclidean-volume integration by parts: the first analytic milestone

This is **not** a new integration-by-parts assumption. The central lemma
is deduced from Mathlib's Haar-measure integration-by-parts theorem
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.

The two functions are *actual* compactly supported C-infinity tests on
an open subset of the three-dimensional Euclidean space, and the measure
is the Euclidean Haar/Lebesgue `volume` measure.

The domain version has no boundary term because both test functions vanish
outside Omega. This file proves the required scalar coordinate identity,
not yet the full vector inner-product/negative-divergence identity used by
the maximal graph construction.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped Distributions

variable (Ω : Opens pressureNeumannE3)

/-- Direct Mathlib-backed physical-volume integration by parts for one
coordinate. Both functions have compact support strictly inside Ω. -/
theorem pressure_neumann_3d_volume_coordinate_ibp
    (ψ χ : pressureNeumann3DSmoothScalarTests Ω) (i : Fin 3) :
    (∫ x : pressureNeumannE3,
       (ψ x) * (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x)
         (EuclideanSpace.single i (1 : ℝ))
       ∂(volume : Measure pressureNeumannE3)) =
      -(∫ x : pressureNeumannE3,
         (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ)) * χ x
         ∂(volume : Measure pressureNeumannE3)) := by
  let v : pressureNeumannE3 := EuclideanSpace.single i (1 : ℝ)
  have hψc : Continuous (ψ : pressureNeumannE3 → ℝ) := ψ.contDiff.continuous
  have hχc : Continuous (χ : pressureNeumannE3 → ℝ) := χ.contDiff.continuous
  have hψd : Continuous (fun x : pressureNeumannE3 =>
      (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x) v) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχd : Continuous (fun x : pressureNeumannE3 =>
      (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x) v) :=
    (χ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint1 : Integrable (fun x : pressureNeumannE3 =>
      (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x) v * χ x)
      (volume : Measure pressureNeumannE3) :=
    (hψd.mul hχc).integrable_of_hasCompactSupport
      (χ.hasCompactSupport.mul_left)
  have hint2 : Integrable (fun x : pressureNeumannE3 =>
      ψ x * (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x) v)
      (volume : Measure pressureNeumannE3) :=
    (hψc.mul hχd).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_right)
  have hint3 : Integrable (fun x : pressureNeumannE3 => ψ x * χ x)
      (volume : Measure pressureNeumannE3) :=
    (hψc.mul hχc).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_right)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure pressureNeumannE3))
    (v := v) hint1 hint2 hint3
    (fun x _ => (ψ.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (χ.contDiff.differentiable (by simp)).differentiableAt)

/-- Outside Ω a compactly supported smooth scalar test function is zero. -/
theorem pressure_neumann_3d_scalar_test_zero_off_domain
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (x : pressureNeumannE3) (hx : x ∉ (Ω : Set pressureNeumannE3)) :
    ψ x = 0 := by
  have hx' : x ∉ Function.support (ψ : pressureNeumannE3 → ℝ) := by
    intro h
    exact hx (ψ.tsupport_subset ((subset_tsupport (ψ : pressureNeumannE3 → ℝ)) h))
  by_contra hne
  exact hx' hne

/-- Local domain version with Euclidean volume and *no* boundary term.
This is the identity from which the weak vector-gradient IBP must be built. -/
theorem pressure_neumann_3d_volume_coordinate_ibp_on_domain
    (ψ χ : pressureNeumann3DSmoothScalarTests Ω) (i : Fin 3) :
    (∫ x in (Ω : Set pressureNeumannE3),
       (ψ x) * (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x)
         (EuclideanSpace.single i (1 : ℝ))
       ∂(volume : Measure pressureNeumannE3)) =
      -(∫ x in (Ω : Set pressureNeumannE3),
         (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ)) * χ x
         ∂(volume : Measure pressureNeumannE3)) := by
  have hleft :
      (∫ x in (Ω : Set pressureNeumannE3),
         ψ x * (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ))
         ∂(volume : Measure pressureNeumannE3)) =
      (∫ x : pressureNeumannE3,
         ψ x * (fderiv ℝ (χ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ))
         ∂(volume : Measure pressureNeumannE3)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [pressure_neumann_3d_scalar_test_zero_off_domain Ω ψ x hx]
    simp
  have hright :
      (∫ x in (Ω : Set pressureNeumannE3),
         (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ)) * χ x
         ∂(volume : Measure pressureNeumannE3)) =
      (∫ x : pressureNeumannE3,
         (fderiv ℝ (ψ : pressureNeumannE3 → ℝ) x)
           (EuclideanSpace.single i (1 : ℝ)) * χ x
         ∂(volume : Measure pressureNeumannE3)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [pressure_neumann_3d_scalar_test_zero_off_domain Ω χ x hx]
    simp
  rw [hleft, hright]
  exact pressure_neumann_3d_volume_coordinate_ibp Ω ψ χ i

end ReservoirSeismicityControl
