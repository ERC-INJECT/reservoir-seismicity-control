import ReservoirSeismicityControl.PressurePositiveSemigroupDualRiesz
import ReservoirSeismicityControl.PressurePositiveSemigroupStepCFoundation
import ReservoirSeismicityControl.PressurePositiveSemigroupCanonicalBridge

/-!
# A5: uniformly bounded finite-step approximants imply the limit estimate

The previous compiled modules establish:
* the sharp A5 bound for every finite multiwell step input;
* the self-adjoint-generator dual/Riesz argument that passes that bound
  through strong convergence of pressures, without convergence of Ap_k.

This module combines the results into an explicit time-step limit theorem.
The step partitions and rates may depend on the approximation index.

IMPORTANT: `hLimit` is a genuine hypothesis. This theorem does NOT construct
step-function approximations to an arbitrary bounded measurable rate, nor
identify their strong limit with the Bochner Duhamel integral. It also
assumes the self-adjoint graph characterization of the generator. The
canonical specialization proves semigroup self-adjointness from the Neumann
resolvent construction, but still requires the generator graph property.
No time derivative of the rate, eigenbasis, or compact resolvent is assumed.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace BigOperators

section AbstractMultiwellLimit

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The full A5 estimate at a strong limit of uniformly bounded multiwell
step approximations. The number and lengths of intervals may change with k. -/
theorem pressure_multiwell_A5_of_step_limit
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (n : ℕ → Fin m → ℕ)
    (τ h : ℕ → Fin m → ℕ → NNReal)
    (hτ0 : ∀ k j, τ k j 0 = 0)
    (hStep : ∀ k j i, i < n k j →
      τ k j (i + 1) = τ k j i + h k j i)
    (q : ℕ → Fin m → ℕ → ℝ)
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hq : ∀ k j i, i < n k j → |q k j i| ≤ M j)
    (f : Fin m → H) (p : H)
    (hLimit : Tendsto
      (fun k : ℕ =>
        ((⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
          pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k) (q k) f :
          S.generatorDomain) : H))
      atTop (𝓝 p)) :
    ∃ hp : p ∈ S.generatorDomain,
      ‖S.generator ⟨p, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  let u : ℕ → S.generatorDomain := fun k =>
    ⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
      pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k) (q k) f
  have hConverges : Tendsto (fun k => (u k : H)) atTop (𝓝 p) := hLimit
  have hBound (k : ℕ) :
      ‖S.generator (u k)‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
    exact pressure_multiwell_step_duhamel_full_generator_bound
      S hSelf t p₀ m (n k) (τ k) (h k)
      (hτ0 k) (hStep k) (q k) M hM (hq k) f
  exact pressure_generator_bound_of_strong_pressure_limit
    S hGraph u p
    (‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖)
    hConverges hBound

end AbstractMultiwellLimit

section CanonicalMultiwellLimit

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- In the canonical weak Neumann construction the self-adjointness of
S(t) is already a theorem, not an extra assumption. The self-adjoint
*generator graph* and strong step-to-Duhamel convergence remain explicit. -/
theorem pressure_canonical_multiwell_A5_of_step_limit
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent
        lam j B₁ E hB₁ hForm₁ hE hLam))
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (hGraph :
      let S := pressureNeumannGeneratedSemigroup
        j B₁ E hB₁ hForm₁ hE hDense
      ∀ u g : H,
        (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
          ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = g)
    (t : NNReal)
    (p₀ : (pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense).generatorDomain)
    (m : ℕ) (n : ℕ → Fin m → ℕ)
    (τ h : ℕ → Fin m → ℕ → NNReal)
    (hτ0 : ∀ k j, τ k j 0 = 0)
    (hStep : ∀ k j i, i < n k j →
      τ k j (i + 1) = τ k j i + h k j i)
    (q : ℕ → Fin m → ℕ → ℝ)
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hq : ∀ k j i, i < n k j → |q k j i| ≤ M j)
    (f : Fin m → H) (p : H)
    (hLimit :
      let S := pressureNeumannGeneratedSemigroup
        j B₁ E hB₁ hForm₁ hE hDense
      Tendsto
        (fun k : ℕ =>
          ((⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
            pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k) (q k) f :
            S.generatorDomain) : H))
        atTop (𝓝 p)) :
    let S := pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense
    ∃ hp : p ∈ S.generatorDomain,
      ‖S.generator ⟨p, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  intro S
  exact pressure_multiwell_A5_of_step_limit S
    (pressure_canonical_semigroup_isSelfAdjoint
      j B₁ E hB₁ hForm₁ hE hDense hSymB)
    hGraph t p₀ m n τ h hτ0 hStep q M hM hq f p hLimit

end CanonicalMultiwellLimit

end ReservoirSeismicityControl
