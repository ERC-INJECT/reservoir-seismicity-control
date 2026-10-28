import ReservoirSeismicityControl.PressureNeumannEnergyForm
import Mathlib

/-!
# Appendix A.1: anisotropic Neumann energy and the mean-zero spectral gap

In the manuscript k(x) is a SYMMETRIC MATRIX, not a scalar coefficient.
Stage 28 covers scalar diffusion. Here the effective matrix coefficient
represents a(x) = k(x) / (beta * eta(x)), in 3D when `n = 3`.

The gradient and operator domains are explicit; neither a Sobolev Neumann
operator nor its Green identity is constructed here. Symmetry of the tensor,
pointwise uniform ellipticity, the weak Green identity and the
Poincare-Wirtinger inequality are separate hypotheses. The results derive
operator coercivity and a lower bound on nonzero eigenvalues from them.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Weak diffusion energy with an anisotropic matrix-valued coefficient.
For ReservoirSeismicityControl take `n = 3` and `tensor x = k(x)/(beta * eta(x))`. -/
noncomputable def pressureNeumannTensorEnergyForm
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (u v : D) : ℝ :=
  ∫ x, ∑ i : Fin n, ∑ j : Fin n,
    gradient u x i * tensor x i j * gradient v x j ∂μ

/-- A symmetric permeability tensor gives a symmetric weak energy form. -/
theorem pressure_neumann_tensor_energy_symmetric
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hsym : ∀ x i j, tensor x i j = tensor x j i)
    (u v : D) :
    pressureNeumannTensorEnergyForm D μ tensor gradient u v =
      pressureNeumannTensorEnergyForm D μ tensor gradient v u := by
  unfold pressureNeumannTensorEnergyForm
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    (∑ i : Fin n, ∑ j : Fin n,
       gradient u x i * tensor x i j * gradient v x j)
      = ∑ j : Fin n, ∑ i : Fin n,
          gradient u x i * tensor x i j * gradient v x j := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n,
          gradient v x j * tensor x j i * gradient u x i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsym x i j]
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
          gradient v x i * tensor x i j * gradient u x j := rfl

/-- Pointwise positive semidefiniteness of the matrix coefficient gives
nonnegative diffusion energy. -/
theorem pressure_neumann_tensor_energy_nonneg
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hpsd : ∀ x (g : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (u : D) :
    0 ≤ pressureNeumannTensorEnergyForm D μ tensor gradient u u := by
  unfold pressureNeumannTensorEnergyForm
  apply integral_nonneg
  intro x
  exact hpsd x (gradient u x)

/-- The pointwise uniform ellipticity condition can be integrated. The
integrability assumptions are explicit because `Ω` is an abstract space. -/
theorem pressure_neumann_tensor_energy_gradient_lower
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω)
    (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (cmin : ℝ)
    (helliptic : ∀ x (g : Fin n → ℝ),
      cmin * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (u : D)
    (hgrad : Integrable (fun x => ∑ i : Fin n, (gradient u x i) ^ 2) μ)
    (henergy : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
       gradient u x i * tensor x i j * gradient u x j) μ) :
    cmin * (∫ x, ∑ i : Fin n, (gradient u x i) ^ 2 ∂μ) ≤
      pressureNeumannTensorEnergyForm D μ tensor gradient u u := by
  have hlow :
      (∫ x, cmin * (∑ i : Fin n, (gradient u x i) ^ 2) ∂μ) ≤
        (∫ x, ∑ i : Fin n, ∑ j : Fin n,
          gradient u x i * tensor x i j * gradient u x j ∂μ) := by
    apply integral_mono (hgrad.const_mul cmin) henergy
    intro x
    exact helliptic x (gradient u x)
  simpa only [integral_const_mul, pressureNeumannTensorEnergyForm] using hlow

/-- The tensor-valued Neumann Green identity implies symmetry of the
unbounded operator on its supplied domain. -/
theorem pressure_neumann_tensor_operator_symmetric_from_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hsym : ∀ x i j, tensor x i j = tensor x j i)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannTensorEnergyForm D μ tensor gradient u v) :
    ∀ u v : D, ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ := by
  intro u v
  calc
    ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannTensorEnergyForm D μ tensor gradient u v := hGreen u v
    _ = pressureNeumannTensorEnergyForm D μ tensor gradient v u :=
      pressure_neumann_tensor_energy_symmetric D μ tensor gradient hsym u v
    _ = ⟪A v, (u : H)⟫_ℝ := (hGreen v u).symm
    _ = ⟪(u : H), A v⟫_ℝ := real_inner_comm _ _

/-- Uniform ellipticity plus a Poincare-Wirtinger estimate on the
mean-zero domain yields a coercivity bound with margin `cmin * κ`.
The Poincare hypothesis is intended for mean-zero `u` only. -/
theorem pressure_neumann_tensor_operator_coercive
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (cmin κ : ℝ)
    (hcmin : 0 < cmin)
    (helliptic : ∀ x (g : Fin n → ℝ),
      cmin * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (hgrad : ∀ u : D,
      Integrable (fun x => ∑ i : Fin n, (gradient u x i) ^ 2) μ)
    (henergy : ∀ u : D,
      Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient u x j) μ)
    (hPoincare : ∀ u : D,
      κ * ⟪(u : H), (u : H)⟫_ℝ ≤
        ∫ x, ∑ i : Fin n, (gradient u x i) ^ 2 ∂μ)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannTensorEnergyForm D μ tensor gradient u v)
    (u : D) :
    (cmin * κ) * ⟪(u : H), (u : H)⟫_ℝ ≤
      ⟪A u, (u : H)⟫_ℝ := by
  have hlow := pressure_neumann_tensor_energy_gradient_lower
    D μ tensor gradient cmin helliptic u (hgrad u) (henergy u)
  have hp := mul_le_mul_of_nonneg_left (hPoincare u) (le_of_lt hcmin)
  calc
    (cmin * κ) * ⟪(u : H), (u : H)⟫_ℝ =
        cmin * (κ * ⟪(u : H), (u : H)⟫_ℝ) := by ring
    _ ≤ cmin * (∫ x, ∑ i : Fin n, (gradient u x i) ^ 2 ∂μ) := hp
    _ ≤ pressureNeumannTensorEnergyForm D μ tensor gradient u u := hlow
    _ = ⟪A u, (u : H)⟫_ℝ := (hGreen u u).symm

/-- Each nonzero eigenmode of the mean-zero Neumann operator has eigenvalue
at least `cmin * κ`. This is the spectral gap in Appendix A.1. -/
theorem pressure_neumann_tensor_eigenvalue_gap
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (tensor : Ω → Fin n → Fin n → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (cmin κ : ℝ)
    (hcmin : 0 < cmin)
    (helliptic : ∀ x (g : Fin n → ℝ),
      cmin * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * tensor x i j * g j)
    (hgrad : ∀ u : D,
      Integrable (fun x => ∑ i : Fin n, (gradient u x i) ^ 2) μ)
    (henergy : ∀ u : D,
      Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
        gradient u x i * tensor x i j * gradient u x j) μ)
    (hPoincare : ∀ u : D,
      κ * ⟪(u : H), (u : H)⟫_ℝ ≤
        ∫ x, ∑ i : Fin n, (gradient u x i) ^ 2 ∂μ)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannTensorEnergyForm D μ tensor gradient u v)
    (e : D) (lam : ℝ)
    (heig : A e = lam • (e : H))
    (hepos : 0 < ⟪(e : H), (e : H)⟫_ℝ) :
    cmin * κ ≤ lam := by
  have hgap := pressure_neumann_tensor_operator_coercive
    D A μ tensor gradient cmin κ hcmin helliptic
    hgrad henergy hPoincare hGreen e
  rw [heig, real_inner_smul_left] at hgap
  exact (mul_le_mul_iff_of_pos_right hepos).mp hgap

end ReservoirSeismicityControl
