import ReservoirSeismicityControl.PressureSymmetricDomain
import Mathlib

/-!
# Appendix A.1: energy-form consequences of a Neumann Green identity

The variable-coefficient Neumann diffusion operator is unbounded on L².
This file does not pretend to define that operator on arbitrary L² functions.
Instead, it represents its operator domain by `D : Submodule ℝ H` and
its weak energy form as an integral of `coefficient * (gradient dot gradient)`.
The gradient is represented by a supplied map on the operator domain.

From nonnegative diffusivity and a Green identity we prove symmetry and
nonnegative quadratic form of the operator, then its eigenfunction testing
identity and positivity of nontrivial eigenvalues. In a future step one must
construct the actual Sobolev gradient and Neumann operator, establish Green's
identity and an appropriate spectral basis on the ReservoirSeismicityControl domain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The weak Neumann form with a spatially variable scalar coefficient.
`gradient u x i` represents component `i` of ∇u at point `x`. The dimension
`n` can be set to three for the reservoir model. -/
noncomputable def pressureNeumannEnergyForm
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (u v : D) : ℝ :=
  ∫ x, coefficient x *
    (∑ i : Fin n, gradient u x i * gradient v x i) ∂μ

/-- Symmetry of the concrete gradient energy form requires no assumption
on the operator: it follows by commutativity of scalar multiplication. -/
theorem pressure_neumann_energy_form_symmetric
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ) (u v : D) :
    pressureNeumannEnergyForm D μ coefficient gradient u v =
      pressureNeumannEnergyForm D μ coefficient gradient v u := by
  let fu : Ω → ℝ := fun x => coefficient x *
    (∑ i : Fin n, gradient u x i * gradient v x i)
  let fv : Ω → ℝ := fun x => coefficient x *
    (∑ i : Fin n, gradient v x i * gradient u x i)
  have hfun : fu = fv := by
    funext x
    have hsum :
        (∑ i : Fin n, gradient u x i * gradient v x i) =
        (∑ i : Fin n, gradient v x i * gradient u x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    exact congrArg (fun z : ℝ => coefficient x * z) hsum
  change (∫ x, fu x ∂μ) = ∫ x, fv x ∂μ
  rw [hfun]

/-- Positivity of the energy form for a nonnegative, potentially
spatially varying diffusion coefficient. -/
theorem pressure_neumann_energy_form_nonneg
    {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hcoefficient : ∀ x, 0 ≤ coefficient x) (u : D) :
    0 ≤ pressureNeumannEnergyForm D μ coefficient gradient u u := by
  unfold pressureNeumannEnergyForm
  apply integral_nonneg
  intro x
  apply mul_nonneg (hcoefficient x)
  apply Finset.sum_nonneg
  intro i hi
  nlinarith [sq_nonneg (gradient u x i)]

/-- The Neumann Green identity implies operator symmetry. This removes
Stage 27's independent symmetry hypothesis, conditional on the Green
identity for the intended operator and domain. -/
theorem pressure_neumann_operator_symmetric_from_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannEnergyForm D μ coefficient gradient u v) :
    ∀ u v : D, ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ := by
  intro u v
  calc
    ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannEnergyForm D μ coefficient gradient u v := hGreen u v
    _ = pressureNeumannEnergyForm D μ coefficient gradient v u :=
      pressure_neumann_energy_form_symmetric D μ coefficient gradient u v
    _ = ⟪A v, (u : H)⟫_ℝ := (hGreen v u).symm
    _ = ⟪(u : H), A v⟫_ℝ := real_inner_comm _ _

/-- Under the Neumann Green identity, the diffusion operator has a
nonnegative quadratic form. -/
theorem pressure_neumann_operator_nonneg_from_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hcoefficient : ∀ x, 0 ≤ coefficient x)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannEnergyForm D μ coefficient gradient u v)
    (u : D) :
    0 ≤ ⟪A u, (u : H)⟫_ℝ := by
  rw [hGreen u u]
  exact pressure_neumann_energy_form_nonneg
    D μ coefficient gradient hcoefficient u

/-- A Neumann Green identity supplies the spectral testing identity
used by Stages 26–27, without assuming symmetry separately. -/
theorem pressure_neumann_eigen_test_from_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannEnergyForm D μ coefficient gradient u v)
    (e : D) (lam : ℝ)
    (heig : A e = lam • (e : H)) (p : D) :
    ((innerSL ℝ) (e : H)) (A p) =
      lam * ((innerSL ℝ) (e : H)) (p : H) := by
  apply pressure_symmetric_eigen_test D A
    (pressure_neumann_operator_symmetric_from_green
      D A μ coefficient gradient hGreen) e lam heig p

/-- Nontrivial Neumann eigenmodes have nonnegative eigenvalues.
The positive inner self-product is equivalent to nonzero eigenvector
in a real Hilbert space. -/
theorem pressure_neumann_eigenvalue_nonneg_from_green
    {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {n : ℕ}
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (μ : Measure Ω) (coefficient : Ω → ℝ)
    (gradient : D → Ω → Fin n → ℝ)
    (hcoefficient : ∀ x, 0 ≤ coefficient x)
    (hGreen : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ =
        pressureNeumannEnergyForm D μ coefficient gradient u v)
    (e : D) (lam : ℝ)
    (heig : A e = lam • (e : H))
    (hepos : 0 < ⟪(e : H), (e : H)⟫_ℝ) :
    0 ≤ lam := by
  have henergy : 0 ≤ ⟪A e, (e : H)⟫_ℝ :=
    pressure_neumann_operator_nonneg_from_green
      D A μ coefficient gradient hcoefficient hGreen e
  rw [heig, real_inner_smul_left] at henergy
  nlinarith

end ReservoirSeismicityControl
