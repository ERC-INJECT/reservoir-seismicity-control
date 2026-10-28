import ReservoirSeismicityControl.PressureWeakNeumannRealization
import Mathlib

/-!
# Stage 31: bilinearity of the anisotropic weak diffusion energy

The matrix-valued weak energy in Stage 29 was an ordinary function of two
arguments. Stage 30 requires an actual bilinear map `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`.

Here the gradient is a **linear** map from the Sobolev test subspace `V`
to vector-valued spatial functions. For integrable cross terms, we construct
the bilinear energy by integrating the exact anisotropic tensor expression.
The proof derives linearity from the finite tensor sums and linearity of the
spatial gradient; it does not assume that the energy itself is bilinear.

IMPORTANT: Cross-term integrability and the concrete Sobolev gradient remain
hypotheses. The module does NOT construct `H¹`, prove compact resolvent, or
identify the Neumann differential expression on the ReservoirSeismicityControl domain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- Pointwise anisotropic energy integrand with a linear spatial gradient. -/
def pressureTensorIntegrand
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {V : Submodule ℝ H}
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (u v : V) (x : Ω) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    gradient u x i * tensor x i j * gradient v x j

private theorem pressureTensorIntegrand_add_left
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {V : Submodule ℝ H}
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (u v w : V) :
    pressureTensorIntegrand tensor gradient (u + v) w =
      pressureTensorIntegrand tensor gradient u w +
        pressureTensorIntegrand tensor gradient v w := by
  funext x
  simp only [pressureTensorIntegrand, map_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

private theorem pressureTensorIntegrand_add_right
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {V : Submodule ℝ H}
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (u v w : V) :
    pressureTensorIntegrand tensor gradient u (v + w) =
      pressureTensorIntegrand tensor gradient u v +
        pressureTensorIntegrand tensor gradient u w := by
  funext x
  simp only [pressureTensorIntegrand, map_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

private theorem pressureTensorIntegrand_smul_left
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {V : Submodule ℝ H}
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (c : ℝ) (u v : V) :
    pressureTensorIntegrand tensor gradient (c • u) v =
      c • pressureTensorIntegrand tensor gradient u v := by
  funext x
  change
    (∑ i : Fin n, ∑ j : Fin n,
      gradient (c • u) x i * tensor x i j * gradient v x j) =
      c * (∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient v x j)
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      gradient (c • u) x i * tensor x i j * gradient v x j) =
        ∑ i : Fin n, ∑ j : Fin n,
          c * (gradient u x i * tensor x i j * gradient v x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    _ = c * (∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient v x j) := by
      simp only [Finset.mul_sum]

private theorem pressureTensorIntegrand_smul_right
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {V : Submodule ℝ H}
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (c : ℝ) (u v : V) :
    pressureTensorIntegrand tensor gradient u (c • v) =
      c • pressureTensorIntegrand tensor gradient u v := by
  funext x
  change
    (∑ i : Fin n, ∑ j : Fin n,
      gradient u x i * tensor x i j * gradient (c • v) x j) =
      c * (∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient v x j)
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      gradient u x i * tensor x i j * gradient (c • v) x j) =
        ∑ i : Fin n, ∑ j : Fin n,
          c * (gradient u x i * tensor x i j * gradient v x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    _ = c * (∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient v x j) := by
      simp only [Finset.mul_sum]

/-- The true anisotropic energy, constructed as a bilinear map from a linear
spatial gradient and integrability of each cross term. -/
noncomputable def pressureTensorEnergyBilinear
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (hcross : ∀ u v : V, Integrable
      (pressureTensorIntegrand tensor gradient u v) μ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun := fun u => {
    toFun := fun v => ∫ x, pressureTensorIntegrand tensor gradient u v x ∂μ
    map_add' := by
      intro v w
      change (∫ x, pressureTensorIntegrand tensor gradient u (v + w) x ∂μ) =
        (∫ x, pressureTensorIntegrand tensor gradient u v x ∂μ) +
          (∫ x, pressureTensorIntegrand tensor gradient u w x ∂μ)
      rw [pressureTensorIntegrand_add_right]
      simpa only [Pi.add_apply] using (integral_add (hcross u v) (hcross u w))
    map_smul' := by
      intro c v
      change (∫ x, pressureTensorIntegrand tensor gradient u (c • v) x ∂μ) =
        c * (∫ x, pressureTensorIntegrand tensor gradient u v x ∂μ)
      rw [pressureTensorIntegrand_smul_right]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (integral_const_mul c (pressureTensorIntegrand tensor gradient u v))
  }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change (∫ x, pressureTensorIntegrand tensor gradient (u + v) w x ∂μ) =
      (∫ x, pressureTensorIntegrand tensor gradient u w x ∂μ) +
        (∫ x, pressureTensorIntegrand tensor gradient v w x ∂μ)
    rw [pressureTensorIntegrand_add_left]
    simpa only [Pi.add_apply] using (integral_add (hcross u w) (hcross v w))
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change (∫ x, pressureTensorIntegrand tensor gradient (c • u) v x ∂μ) =
      c * (∫ x, pressureTensorIntegrand tensor gradient u v x ∂μ)
    rw [pressureTensorIntegrand_smul_left]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (integral_const_mul c (pressureTensorIntegrand tensor gradient u v))

/-- Applying the bilinear map recovers exactly Stage 29's anisotropic energy. -/
theorem pressure_tensor_energy_bilinear_eq_integral
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (hcross : ∀ u v : V, Integrable
      (pressureTensorIntegrand tensor gradient u v) μ)
    (u v : V) :
    pressureTensorEnergyBilinear V μ tensor gradient hcross u v =
      pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) u v := by
  rfl

/-- The Stage 30 construction now gives a genuine Green identity for the
specific matrix-valued tensor energy, rather than an unrelated bilinear form.
Separation of the test space is still a hypothesis. -/
theorem pressure_tensor_weak_operator_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (V : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : V →ₗ[ℝ] (Ω → Fin n → ℝ))
    (hcross : ∀ u v : V, Integrable
      (pressureTensorIntegrand tensor gradient u v) μ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (u : pressureWeakNeumannDomain V
      (pressureTensorEnergyBilinear V μ tensor gradient hcross))
    (v : V) :
    ⟪pressureWeakNeumannOperator V
      (pressureTensorEnergyBilinear V μ tensor gradient hcross) hsep u,
      (v : H)⟫_ℝ =
      pressureNeumannTensorEnergyForm V μ tensor (fun w => gradient w) (u : V) v := by
  calc
    ⟪pressureWeakNeumannOperator V
        (pressureTensorEnergyBilinear V μ tensor gradient hcross) hsep u,
        (v : H)⟫_ℝ =
        pressureTensorEnergyBilinear V μ tensor gradient hcross (u : V) v :=
      pressure_weak_neumann_operator_green V
        (pressureTensorEnergyBilinear V μ tensor gradient hcross) hsep u v
    _ = pressureNeumannTensorEnergyForm V μ tensor
        (fun w => gradient w) (u : V) v :=
      pressure_tensor_energy_bilinear_eq_integral V μ tensor gradient hcross (u : V) v

end ReservoirSeismicityControl
