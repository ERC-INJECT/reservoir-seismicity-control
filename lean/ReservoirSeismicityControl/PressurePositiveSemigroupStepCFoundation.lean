import ReservoirSeismicityControl.PressurePositiveSemigroupStepDuhamel
import MarkovProcess.Semigroup.GeneratorClosed

/-!
# A5 foundation for the bounded-input limit

This module completes the finite-step extension from one well to finitely many
wells and records the existing closed-generator convergence theorem in the exact
form needed for Duhamel approximations.

IMPORTANT. The strong-generator-convergence hypothesis in the last theorem is
NOT derived from the uniform A5 bound. In an infinite-dimensional Hilbert space,
a bounded sequence need not converge strongly. Replacing that hypothesis by a
weak-compactness/weak-graph argument and constructing interval-step approximants
for general bounded measurable rates are outstanding tasks.

No eigenbasis, compact-resolvent hypothesis, or time derivative of the input
is used here.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace BigOperators

section MultiwellStep

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A finite sum of genuine stepwise Duhamel terms, one for each well. -/
noncomputable def pressureMultiwellStepDuhamelDomain
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal) (q : Fin m → ℕ → ℝ)
    (f : Fin m → H) : S.generatorDomain :=
  ∑ j : Fin m, pressureStepDuhamelDomain S (n j) (τ j) (h j) (q j) (f j)

/-- The exact finite-multiwell A5 estimate with no dependence on the
number of time blocks. Each well can have its own partition. -/
theorem pressure_multiwell_step_duhamel_generator_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal)
    (hτ0 : ∀ j : Fin m, τ j 0 = 0)
    (hStep : ∀ j : Fin m, ∀ i < n j, τ j (i + 1) = τ j i + h j i)
    (q : Fin m → ℕ → ℝ) (M : Fin m → ℝ)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hq : ∀ j : Fin m, ∀ i < n j, |q j i| ≤ M j)
    (f : Fin m → H) :
    ‖S.generator (pressureMultiwellStepDuhamelDomain S m n τ h q f)‖ ≤
      ∑ j : Fin m, M j * ‖f j‖ := by
  unfold pressureMultiwellStepDuhamelDomain
  rw [map_sum]
  calc
    ‖∑ j : Fin m, S.generator
        (pressureStepDuhamelDomain S (n j) (τ j) (h j) (q j) (f j))‖ ≤
      ∑ j : Fin m, ‖S.generator
        (pressureStepDuhamelDomain S (n j) (τ j) (h j) (q j) (f j))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin m, M j * ‖f j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact pressure_step_duhamel_generator_bound S hSelf
        (n j) (τ j) (h j) (hτ0 j) (hStep j)
        (q j) (M j) (hM j) (hq j) (f j)

/-- Include the free evolution of the initial pressure. -/
theorem pressure_multiwell_step_duhamel_full_generator_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal)
    (hτ0 : ∀ j : Fin m, τ j 0 = 0)
    (hStep : ∀ j : Fin m, ∀ i < n j, τ j (i + 1) = τ j i + h j i)
    (q : Fin m → ℕ → ℝ) (M : Fin m → ℝ)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hq : ∀ j : Fin m, ∀ i < n j, |q j i| ≤ M j)
    (f : Fin m → H) :
    ‖S.generator
      (⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
        pressureMultiwellStepDuhamelDomain S m n τ h q f)‖ ≤
      ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  have hForcing := pressure_multiwell_step_duhamel_generator_bound S hSelf
    m n τ h hτ0 hStep q M hM hq f
  calc
    ‖S.generator
      (⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
        pressureMultiwellStepDuhamelDomain S m n τ h q f)‖ =
      ‖S t (S.generator p₀) +
        S.generator (pressureMultiwellStepDuhamelDomain S m n τ h q f)‖ := by
          rw [map_add, S.generator_operator]
    _ ≤ ‖S t (S.generator p₀)‖ +
      ‖S.generator (pressureMultiwellStepDuhamelDomain S m n τ h q f)‖ :=
        norm_add_le _ _
    _ ≤ ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ :=
      add_le_add (S.norm_apply_le t (S.generator p₀)) hForcing

end MultiwellStep

section ClosedGeneratorLimit

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A *strongly convergent pair* of approximating pressures and generator
values passes to the closed generator graph, retaining the uniform estimate.

The convergence of generator values is a separate hypothesis. It cannot be
inferred from their bounded norms alone. -/
theorem pressure_generator_bound_of_strong_graph_limit
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (u : ℕ → S.generatorDomain) (p g : H) (C : ℝ)
    (hp : Tendsto (fun k => (u k : H)) atTop (𝓝 p))
    (hg : Tendsto (fun k => S.generator (u k)) atTop (𝓝 g))
    (hBound : ∀ k, ‖S.generator (u k)‖ ≤ C) :
    ∃ hDomain : p ∈ S.generatorDomain,
      S.generator ⟨p, hDomain⟩ = g ∧ ‖g‖ ≤ C := by
  have hDomain : p ∈ S.generatorDomain :=
    S.mem_generatorDomain_of_tendsto_generator hp hg
  refine ⟨hDomain, S.generator_eq_of_tendsto_generator hp hg, ?_⟩
  have hNorm : Tendsto (fun k => ‖S.generator (u k)‖) atTop (𝓝 ‖g‖) :=
    (continuous_norm.tendsto g).comp hg
  exact le_of_tendsto hNorm (Filter.Eventually.of_forall hBound)

end ClosedGeneratorLimit

end ReservoirSeismicityControl
