import ReservoirSeismicityControl.PressureTensorBilinearForm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Stage 32: L2 gradients and bounded tensors give integrable cross terms

The Stage 31 bilinear energy required integrability of every anisotropic
cross term. That assumption follows from square-integrability of the weak
gradient components and an essentially bounded measurable tensor coefficient.
This file proves the deduction via the L2-times-L2-to-L1 product lemma.

The tensor and gradient functions are still abstract. We have not constructed
the ReservoirSeismicityControl Sobolev H1 space, its distributional gradient, the Neumann
operator self-adjointness, or parabolic PDE solution regularity.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- If all gradient components belong to L² and the tensor entries are
measurable and essentially bounded, the entire anisotropic cross-energy
integrand is integrable. No independent `hcross` hypothesis is necessary. -/
theorem pressure_tensor_cross_integrable_of_L2_bounded
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (htensor : ∀ i j : Fin n,
      AEStronglyMeasurable (fun x => tensor x i j) μ)
    (hbound : ∀ i j : Fin n,
      ∀ᵐ x ∂μ, |tensor x i j| ≤ C)
    (hgrad : ∀ u : V, ∀ i : Fin n,
      MemLp (fun x => gradient u x i) 2 μ)
    (u v : V) :
    Integrable (pressureTensorIntegrand tensor gradient u v) μ := by
  have hentry (i j : Fin n) :
      Integrable (fun x =>
        gradient u x i * tensor x i j * gradient v x j) μ := by
    have hweighted :
        MemLp (fun x => tensor x i j * gradient u x i) 2 μ := by
      apply ((hgrad u i).const_mul C).mono
        ((htensor i j).mul (hgrad u i).aestronglyMeasurable)
      filter_upwards [hbound i j] with x hx
      change ‖tensor x i j * gradient u x i‖ ≤ ‖C * gradient u x i‖
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using
        (mul_le_mul_of_nonneg_right hx (abs_nonneg (gradient u x i)))
    have hproduct :
        Integrable (fun x =>
          (tensor x i j * gradient u x i) * gradient v x j) μ :=
      hweighted.integrable_mul (hgrad v j)
    exact hproduct.congr (Filter.Eventually.of_forall (fun x => by ring))
  have hrows (i : Fin n) :
      Integrable (fun x => ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient v x j) μ := by
    simpa only using (integrable_finsetSum (s := Finset.univ)
      (f := fun j : Fin n => fun x : Ω =>
        gradient u x i * tensor x i j * gradient v x j)
      (by intro j hj; exact hentry i j))
  change Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
    gradient u x i * tensor x i j * gradient v x j) μ
  simpa only using (integrable_finsetSum (s := Finset.univ)
    (f := fun i : Fin n => fun x : Ω => ∑ j : Fin n,
      gradient u x i * tensor x i j * gradient v x j)
    (by intro i hi; exact hrows i))

/-- The Stage 31 bilinear map with its cross-integrability supplied by
square-integrable gradients and bounded matrix coefficients. -/
noncomputable def pressureTensorEnergyFromL2
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (htensor : ∀ i j : Fin n,
      AEStronglyMeasurable (fun x => tensor x i j) μ)
    (hbound : ∀ i j : Fin n,
      ∀ᵐ x ∂μ, |tensor x i j| ≤ C)
    (hgrad : ∀ u : V, ∀ i : Fin n,
      MemLp (fun x => gradient u x i) 2 μ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  pressureTensorEnergyBilinear V μ tensor gradient
    (pressure_tensor_cross_integrable_of_L2_bounded
      V μ tensor gradient C hC htensor hbound hgrad)

/-- The L²-constructed bilinear energy equals the explicit tensor integral. -/
theorem pressure_tensor_energy_from_L2_eq_integral
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (htensor : ∀ i j : Fin n,
      AEStronglyMeasurable (fun x => tensor x i j) μ)
    (hbound : ∀ i j : Fin n,
      ∀ᵐ x ∂μ, |tensor x i j| ≤ C)
    (hgrad : ∀ u : V, ∀ i : Fin n,
      MemLp (fun x => gradient u x i) 2 μ)
    (u v : V) :
    pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad u v =
      pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) u v := by
  exact pressure_tensor_energy_bilinear_eq_integral V μ tensor gradient
    (pressure_tensor_cross_integrable_of_L2_bounded
      V μ tensor gradient C hC htensor hbound hgrad) u v

/-- Green's identity now follows for the weak operator built from the
actual tensor integral, with no independent cross-term integrability assumption. -/
theorem pressure_tensor_weak_operator_green_from_L2
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (htensor : ∀ i j : Fin n,
      AEStronglyMeasurable (fun x => tensor x i j) μ)
    (hbound : ∀ i j : Fin n,
      ∀ᵐ x ∂μ, |tensor x i j| ≤ C)
    (hgrad : ∀ u : V, ∀ i : Fin n,
      MemLp (fun x => gradient u x i) 2 μ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (u : pressureWeakNeumannDomain V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad))
    (v : V) :
    ⟪pressureWeakNeumannOperator V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
      hsep u, (v : H)⟫_ℝ =
      pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) (u : V) v := by
  calc
    ⟪pressureWeakNeumannOperator V
        (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
        hsep u, (v : H)⟫_ℝ =
        pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad
          (u : V) v :=
      pressure_weak_neumann_operator_green V
        (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
        hsep u v
    _ = pressureNeumannTensorEnergyForm V μ tensor
        (fun w => gradient w) (u : V) v :=
      pressure_tensor_energy_from_L2_eq_integral
        V μ tensor gradient C hC htensor hbound hgrad (u : V) v

end ReservoirSeismicityControl
