import ReservoirSeismicityControl.PressureTensorLpIntegrability

/-!
# Stage 33: connect the integrable tensor form to the weak operator

This module closes the abstract chain between Stages 29–32. The bilinear
energy constructed from L² gradient components defines the weak operator
of Stage 30. Its symmetry, nonnegativity, coercivity and modal gap are now
proved for this *specific* constructed operator, not an unrelated A with a
postulated Green identity.

The gradient, test space and tensor are still abstract. To apply the
statements to the reservoir, one must build the actual H¹(V) weak gradient,
prove density and Poincaré–Wirtinger, and establish self-adjointness,
compact resolvent and appropriate evolution regularity. No such claims
are made in this module.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The bilinear energy built from L² gradients is symmetric when the tensor
coefficient is pointwise symmetric. -/
theorem pressure_tensor_L2_energy_symmetric
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
    (hsym : ∀ x i j, tensor x i j = tensor x j i)
    (u v : V) :
    pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad u v =
      pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad v u := by
  calc
    pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad u v =
        pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) u v :=
      pressure_tensor_energy_from_L2_eq_integral
        V μ tensor gradient C hC htensor hbound hgrad u v
    _ = pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) v u :=
      pressure_neumann_tensor_energy_symmetric
        V μ tensor (fun w => gradient w) hsym u v
    _ = pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad v u :=
      (pressure_tensor_energy_from_L2_eq_integral
        V μ tensor gradient C hC htensor hbound hgrad v u).symm

/-- Nonnegativity of the L²-constructed energy from the anisotropic
pointwise positive-semidefinite coefficient. -/
theorem pressure_tensor_L2_energy_nonneg
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
    (hpsd : ∀ x (g : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (u : V) :
    0 ≤ pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad u u := by
  rw [pressure_tensor_energy_from_L2_eq_integral
    V μ tensor gradient C hC htensor hbound hgrad u u]
  exact pressure_neumann_tensor_energy_nonneg
    V μ tensor (fun w => gradient w) hpsd u

/-- Symmetry for the weak operator actually constructed from the L² tensor
energy. There is no independent operator Green identity in the hypotheses. -/
theorem pressure_tensor_L2_weak_operator_symmetric
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
    (hsym : ∀ x i j, tensor x i j = tensor x j i)
    (u v : pressureWeakNeumannDomain V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)) :
    ⟪pressureWeakNeumannOperator V
        (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
        hsep u, ((v : V) : H)⟫_ℝ =
      ⟪((u : V) : H),
        pressureWeakNeumannOperator V
          (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
          hsep v⟫_ℝ := by
  exact pressure_weak_neumann_operator_symmetric
    V (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
    hsep (pressure_tensor_L2_energy_symmetric
      V μ tensor gradient C hC htensor hbound hgrad hsym) u v

/-- Nonnegativity of the actual constructed weak operator. -/
theorem pressure_tensor_L2_weak_operator_nonneg
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
    (hpsd : ∀ x (g : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (u : pressureWeakNeumannDomain V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)) :
    0 ≤ ⟪pressureWeakNeumannOperator V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
      hsep u, ((u : V) : H)⟫_ℝ := by
  exact pressure_weak_neumann_operator_nonneg
    V (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
    hsep (pressure_tensor_L2_energy_nonneg
      V μ tensor gradient C hC htensor hbound hgrad hpsd) u

/-- Square-integrability of the components implies integrability of the
sum of gradient squares. This discharges the old independent `hgrad` energy
integrability hypothesis in Stage 29. -/
theorem pressure_tensor_gradient_square_integrable_of_L2
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (hgrad : ∀ u : V, ∀ i : Fin n,
      MemLp (fun x => gradient u x i) 2 μ)
    (u : V) :
    Integrable (fun x => ∑ i : Fin n, (gradient u x i) ^ 2) μ := by
  have hi (i : Fin n) :
      Integrable (fun x => (gradient u x i) ^ 2) μ := by
    have hmul := (hgrad u i).integrable_mul (hgrad u i)
    change Integrable (fun x : Ω => gradient u x i * gradient u x i) μ at hmul
    simpa only [pow_two] using hmul
  simpa only using (integrable_finsetSum (s := Finset.univ)
    (f := fun i : Fin n => fun x : Ω => (gradient u x i) ^ 2)
    (by intro i hi'; exact hi i))

/-- Coercivity of the *constructed* tensor operator on a mean-zero test
space. Poincaré–Wirtinger is the remaining geometric input, but neither
tensor-energy integrability nor an operator Green identity is assumed. -/
theorem pressure_tensor_L2_weak_operator_coercive
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
    (cmin κ : ℝ) (hcmin : 0 < cmin)
    (helliptic : ∀ x (g : Fin n → ℝ),
      cmin * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (hPoincare : ∀ v : V,
      κ * ⟪(v : H), (v : H)⟫_ℝ ≤
        ∫ x, ∑ i : Fin n, (gradient v x i) ^ 2 ∂μ)
    (u : pressureWeakNeumannDomain V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)) :
    (cmin * κ) * ⟪((u : V) : H), ((u : V) : H)⟫_ℝ ≤
      ⟪pressureWeakNeumannOperator V
          (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
          hsep u, ((u : V) : H)⟫_ℝ := by
  have hgradient :
      Integrable (fun x => ∑ i : Fin n, (gradient (u : V) x i) ^ 2) μ :=
    pressure_tensor_gradient_square_integrable_of_L2 V μ gradient hgrad (u : V)
  have henergy :
      Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
        gradient (u : V) x i * tensor x i j * gradient (u : V) x j) μ :=
    pressure_tensor_cross_integrable_of_L2_bounded
      V μ tensor gradient C hC htensor hbound hgrad (u : V) (u : V)
  have hlow := pressure_neumann_tensor_energy_gradient_lower
    V μ tensor (fun w => gradient w) cmin helliptic
    (u : V) hgradient henergy
  have hp := mul_le_mul_of_nonneg_left (hPoincare (u : V)) (le_of_lt hcmin)
  calc
    (cmin * κ) * ⟪((u : V) : H), ((u : V) : H)⟫_ℝ =
        cmin * (κ * ⟪((u : V) : H), ((u : V) : H)⟫_ℝ) := by ring
    _ ≤ cmin * (∫ x, ∑ i : Fin n, (gradient (u : V) x i) ^ 2 ∂μ) := hp
    _ ≤ pressureNeumannTensorEnergyForm V μ tensor
        (fun w => gradient w) (u : V) (u : V) := hlow
    _ = ⟪pressureWeakNeumannOperator V
          (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
          hsep u, ((u : V) : H)⟫_ℝ :=
      (pressure_tensor_weak_operator_green_from_L2
        V μ tensor gradient C hC htensor hbound hgrad hsep u (u : V)).symm

/-- Eigenvalues of the constructed mean-zero tensor operator have the
Poincaré–ellipticity spectral gap. This is conditional on an eigenvector,
not a proof that an eigenbasis exists. -/
theorem pressure_tensor_L2_weak_operator_eigenvalue_gap
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
    (cmin κ : ℝ) (hcmin : 0 < cmin)
    (helliptic : ∀ x (g : Fin n → ℝ),
      cmin * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (hPoincare : ∀ v : V,
      κ * ⟪(v : H), (v : H)⟫_ℝ ≤
        ∫ x, ∑ i : Fin n, (gradient v x i) ^ 2 ∂μ)
    (e : pressureWeakNeumannDomain V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad))
    (lam : ℝ)
    (heig : pressureWeakNeumannOperator V
      (pressureTensorEnergyFromL2 V μ tensor gradient C hC htensor hbound hgrad)
      hsep e = lam • ((e : V) : H))
    (hepos : 0 < ⟪((e : V) : H), ((e : V) : H)⟫_ℝ) :
    cmin * κ ≤ lam := by
  have hgap := pressure_tensor_L2_weak_operator_coercive
    V μ tensor gradient C hC htensor hbound hgrad hsep
    cmin κ hcmin helliptic hPoincare e
  rw [heig, real_inner_smul_left] at hgap
  exact (mul_le_mul_iff_of_pos_right hepos).mp hgap

end ReservoirSeismicityControl
