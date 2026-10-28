import ReservoirSeismicityControl.PressurePositiveSemigroupCanonicalBridge

/-!
# Generator bound for finite stepwise Duhamel forcing

For a strongly continuous contraction semigroup S, every orbit integral
  ∫₀ʰ S(s) f ds
belongs to the generator domain, even if f is not in that domain. Thus a
finite linear combination of shifted orbit integrals belongs to the domain.
Its generator is exactly a sum of semigroup increments.

When the semigroup operators are self-adjoint, the previously verified
positive-partition theorem controls these increments with the SHARP constant
one, independently of the number and size of time steps. The last theorem
applies this conclusion to the canonical Neumann semigroup, where
self-adjointness has already been proved rather than assumed.

This module is the piecewise-constant-input part of (A5). It does NOT yet
extend the bound to arbitrary L∞-in-time inputs or establish the final
identification with the physical PDE pressure variable.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace BigOperators

section StepDuhamel

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A single time block, expressed through the semigroup's genuine
Bochner orbit integral, after a time shift. -/
theorem pressure_step_orbit_generator
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (f : H) (τ h : NNReal) :
    S.generator
      ⟨S τ (S.orbitIntegral f h),
        S.operator_mem_generatorDomain
          ⟨S.orbitIntegral f h, S.orbitIntegral_mem_generatorDomain f h⟩ τ⟩ =
      S (τ + h) f - S τ f := by
  let g : S.generatorDomain :=
    ⟨S.orbitIntegral f h, S.orbitIntegral_mem_generatorDomain f h⟩
  have hg : S.generator g = S h f - f := by
    exact S.generator_orbitIntegral f h
  calc
    S.generator
        ⟨S τ (S.orbitIntegral f h),
          S.operator_mem_generatorDomain
            ⟨S.orbitIntegral f h, S.orbitIntegral_mem_generatorDomain f h⟩ τ⟩ =
        S τ (S.generator g) := by
          exact S.generator_operator g τ
    _ = S τ (S h f - f) := by rw [hg]
    _ = S (τ + h) f - S τ f := by rw [map_sub, S.add_apply]

/-- The time-shifted orbit integral is exactly the difference of two
orbit integrals. This is the Bochner-integral time-window identity that
identifies each summand with the corresponding constant-input block. -/
theorem pressure_step_orbit_time_window
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (f : H) (τ h : NNReal) :
    S τ (S.orbitIntegral f h) =
      S.orbitIntegral f (τ + h) - S.orbitIntegral f τ := by
  simpa only [NNReal.coe_add, add_comm (h : ℝ) (τ : ℝ)] using
    S.operator_orbitIntegral f h τ

/-- The stepwise Duhamel term as an element of the generator domain.
The time variable τ is the elapsed *backward* time from the observation
instant, as in the finite semigroup-increment bound.

The coercion of this value to H is precisely
  ∑ i<n, qᵢ S(τᵢ) (∫₀^(hᵢ) S(s) f ds).
No assumption that f belongs to the generator domain is used. -/
noncomputable def pressureStepDuhamelDomain
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q : ℕ → ℝ) (f : H) :
    S.generatorDomain :=
  ∑ i ∈ Finset.range n,
    q i •
      (⟨S (τ i) (S.orbitIntegral f (h i)),
        S.operator_mem_generatorDomain
          ⟨S.orbitIntegral f (h i), S.orbitIntegral_mem_generatorDomain f (h i)⟩
          (τ i)⟩ : S.generatorDomain)

/-- The exact generator identity for the finite Duhamel step sum.
It is an equality, not merely a norm bound. -/
theorem pressure_step_duhamel_generator
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q : ℕ → ℝ) (f : H)
    (hStep : ∀ i < n, τ (i + 1) = τ i + h i) :
    S.generator (pressureStepDuhamelDomain S n τ h q f) =
      ∑ i ∈ Finset.range n, q i • (S (τ (i + 1)) f - S (τ i) f) := by
  unfold pressureStepDuhamelDomain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  calc
    S.generator
        ⟨S (τ i) (S.orbitIntegral f (h i)),
          S.operator_mem_generatorDomain
            ⟨S.orbitIntegral f (h i), S.orbitIntegral_mem_generatorDomain f (h i)⟩
            (τ i)⟩ =
        S (τ i + h i) f - S (τ i) f :=
          pressure_step_orbit_generator S f (τ i) (h i)
    _ = S (τ (i + 1)) f - S (τ i) f := by
      rw [hStep i (Finset.mem_range.mp hi)]

/-- The finite stepwise Duhamel term obeys the generator bound with
constant one, even for signed coefficients qᵢ. -/
theorem pressure_step_duhamel_generator_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (n : ℕ) (τ h : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + h i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M) (f : H) :
    ‖S.generator (pressureStepDuhamelDomain S n τ h q f)‖ ≤ M * ‖f‖ := by
  have hqneg : ∀ i < n, |(-q i)| ≤ M := by
    intro i hi
    simpa only [abs_neg] using hq i hi
  have hBound := pressure_C0_semigroup_partition_weighted_bound
    S hSelf n τ h hτ0 hStep (fun i => -q i) M hM hqneg f
  calc
    ‖S.generator (pressureStepDuhamelDomain S n τ h q f)‖ =
        ‖∑ i ∈ Finset.range n,
          (-q i) • (S (τ i) - S (τ (i + 1))) f‖ := by
      rw [pressure_step_duhamel_generator S n τ h q f hStep]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [sub_apply, smul_sub, neg_smul]
      abel
    _ ≤ M * ‖f‖ := hBound

/-- The initial homogeneous solution plus one stepwise forcing term:
this is the precise finite-input analogue of (A5). -/
theorem pressure_step_duhamel_full_generator_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (t : NNReal) (p₀ : S.generatorDomain)
    (n : ℕ) (τ h : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + h i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M) (f : H) :
    ‖S.generator
        (⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
          pressureStepDuhamelDomain S n τ h q f)‖ ≤
      ‖S.generator p₀‖ + M * ‖f‖ := by
  have hForcing := pressure_step_duhamel_generator_bound
    S hSelf n τ h hτ0 hStep q M hM hq f
  calc
    ‖S.generator
        (⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
          pressureStepDuhamelDomain S n τ h q f)‖ =
        ‖S t (S.generator p₀) +
          S.generator (pressureStepDuhamelDomain S n τ h q f)‖ := by
      rw [map_add, S.generator_operator]
    _ ≤ ‖S t (S.generator p₀)‖ +
          ‖S.generator (pressureStepDuhamelDomain S n τ h q f)‖ :=
        norm_add_le _ _
    _ ≤ ‖S.generator p₀‖ + M * ‖f‖ :=
        add_le_add (S.norm_apply_le t (S.generator p₀)) hForcing

end StepDuhamel

section CanonicalStepDuhamel

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Stepwise Duhamel A5 generator bound for the actually generated canonical
Neumann semigroup, with no extra semigroup self-adjointness assumption. -/
theorem pressure_canonical_step_duhamel_generator_bound
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent
        lam j B₁ E hB₁ hForm₁ hE hLam))
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (n : ℕ) (τ h : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + h i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M) (f : H) :
    let S := pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense
    ‖S.generator (pressureStepDuhamelDomain S n τ h q f)‖ ≤ M * ‖f‖ := by
  intro S
  exact pressure_step_duhamel_generator_bound S
    (pressure_canonical_semigroup_isSelfAdjoint
      j B₁ E hB₁ hForm₁ hE hDense hSymB)
    n τ h hτ0 hStep q M hM hq f

end CanonicalStepDuhamel

end ReservoirSeismicityControl
