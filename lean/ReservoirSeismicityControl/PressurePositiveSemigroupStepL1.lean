import ReservoirSeismicityControl.PressurePositiveSemigroupWeakGraph
import MarkovProcess.Semigroup.GeneratorClosed

/-!
# A5: quantitative L1 stability of finite step Duhamel terms

This module proves a norm estimate for the difference between two inputs
sampled on the SAME backward-time partition. Unlike the previously proved
A5 generator estimate, this estimate controls the PRESSURE itself by the
L1 distance between the two step inputs.

  ‖D(q) - D(r)‖ ≤ ‖f‖ ∑ᵢ |qᵢ-rᵢ| hᵢ.

The lemma is uniform in the partition and does not require any time
derivative of the input. It is the norm-convergence ingredient in the
passage from interval-step inputs to bounded measurable inputs.

This file does NOT claim the density of interval-step functions in L1,
or that the generator images converge strongly. The weak-compactness /
weak-graph step is still separate.
-/

namespace ReservoirSeismicityControl

open scoped BigOperators

section StepL1

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The value in H of a finite stepwise Duhamel forcing term. -/
noncomputable def pressureStepDuhamelValue
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q : ℕ → ℝ) (f : H) : H :=
  ∑ i ∈ Finset.range n, q i • S (τ i) (S.orbitIntegral f (h i))

/-- The value agrees with the coercion of the generator-domain element
from the already verified step Duhamel module. -/
theorem pressure_step_duhamel_value_eq_domain
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q : ℕ → ℝ) (f : H) :
    pressureStepDuhamelValue S n τ h q f =
      (pressureStepDuhamelDomain S n τ h q f : H) := by
  simp [pressureStepDuhamelValue, pressureStepDuhamelDomain]

/-- The step Duhamel value is linear in its scalar coefficients. -/
theorem pressure_step_duhamel_value_sub
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q r : ℕ → ℝ) (f : H) :
    pressureStepDuhamelValue S n τ h q f -
      pressureStepDuhamelValue S n τ h r f =
        pressureStepDuhamelValue S n τ h (fun i => q i - r i) f := by
  unfold pressureStepDuhamelValue
  rw [← Finset.sum_sub_distrib]
  simp only [sub_smul]

/-- A single step Duhamel value has norm at most the L1 mass of the
step rates, multiplied by the norm of the well profile. -/
theorem pressure_step_duhamel_value_l1_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q : ℕ → ℝ) (f : H) :
    ‖pressureStepDuhamelValue S n τ h q f‖ ≤
      ∑ i ∈ Finset.range n, |q i| * (‖f‖ * (h i : ℝ)) := by
  unfold pressureStepDuhamelValue
  calc
    ‖∑ i ∈ Finset.range n,
        q i • S (τ i) (S.orbitIntegral f (h i))‖ ≤
      ∑ i ∈ Finset.range n,
        ‖q i • S (τ i) (S.orbitIntegral f (h i))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,
        |q i| * (‖f‖ * (h i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((S.norm_apply_le (τ i) (S.orbitIntegral f (h i))).trans
          (S.norm_orbitIntegral_le f (h i)))
        (abs_nonneg (q i))

/-- Quantitative L1 stability of step Duhamel values for two inputs on
one partition. This estimate does not assume self-adjointness. -/
theorem pressure_step_duhamel_l1_stability
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (n : ℕ) (τ h : ℕ → NNReal) (q r : ℕ → ℝ) (f : H) :
    ‖pressureStepDuhamelValue S n τ h q f -
        pressureStepDuhamelValue S n τ h r f‖ ≤
      ∑ i ∈ Finset.range n, |q i - r i| * (‖f‖ * (h i : ℝ)) := by
  rw [pressure_step_duhamel_value_sub]
  exact pressure_step_duhamel_value_l1_bound S n τ h
    (fun i => q i - r i) f

end StepL1

end ReservoirSeismicityControl
