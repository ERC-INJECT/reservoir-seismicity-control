import ReservoirSeismicityControl.PressurePositiveSemigroupStepL1

/-!
# A5: L1 stability for finitely many well inputs

This module extends the compiled one-well L1 estimate to finitely many wells.
Each well may use its own backward-time partition. Two sets of rates compared
for a given well must use the same partition for that well.

No generator-domain or time-derivative assumption is imposed on the well
profiles or on the step coefficients.
-/

namespace ReservoirSeismicityControl

open scoped BigOperators

section MultiwellL1

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The forcing contribution to pressure from finitely many step inputs. -/
noncomputable def pressureMultiwellStepDuhamelValue
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal) (q : Fin m → ℕ → ℝ)
    (f : Fin m → H) : H :=
  ∑ j : Fin m, pressureStepDuhamelValue S (n j) (τ j) (h j) (q j) (f j)

/-- The multiwell forcing is controlled by the sum of the time-L1 sizes
of the step coefficients, weighted by the well-profile norms. -/
theorem pressure_multiwell_step_duhamel_value_l1_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal) (q : Fin m → ℕ → ℝ)
    (f : Fin m → H) :
    ‖pressureMultiwellStepDuhamelValue S m n τ h q f‖ ≤
      ∑ j : Fin m, ∑ i ∈ Finset.range (n j),
        |q j i| * (‖f j‖ * (h j i : ℝ)) := by
  unfold pressureMultiwellStepDuhamelValue
  calc
    ‖∑ j : Fin m,
        pressureStepDuhamelValue S (n j) (τ j) (h j) (q j) (f j)‖ ≤
      ∑ j : Fin m,
        ‖pressureStepDuhamelValue S (n j) (τ j) (h j) (q j) (f j)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin m, ∑ i ∈ Finset.range (n j),
          |q j i| * (‖f j‖ * (h j i : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pressure_step_duhamel_value_l1_bound S
        (n j) (τ j) (h j) (q j) (f j)

/-- For fixed time partitions, the pressure forcing is Lipschitz with
respect to each well's L1 discrepancy, even for signed well rates. -/
theorem pressure_multiwell_step_duhamel_l1_stability
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (m : ℕ) (n : Fin m → ℕ)
    (τ h : Fin m → ℕ → NNReal) (q r : Fin m → ℕ → ℝ)
    (f : Fin m → H) :
    ‖pressureMultiwellStepDuhamelValue S m n τ h q f -
      pressureMultiwellStepDuhamelValue S m n τ h r f‖ ≤
      ∑ j : Fin m, ∑ i ∈ Finset.range (n j),
        |q j i - r j i| * (‖f j‖ * (h j i : ℝ)) := by
  unfold pressureMultiwellStepDuhamelValue
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin m,
        (pressureStepDuhamelValue S (n j) (τ j) (h j) (q j) (f j) -
          pressureStepDuhamelValue S (n j) (τ j) (h j) (r j) (f j))‖ ≤
      ∑ j : Fin m,
        ‖pressureStepDuhamelValue S (n j) (τ j) (h j) (q j) (f j) -
          pressureStepDuhamelValue S (n j) (τ j) (h j) (r j) (f j)‖ :=
            norm_sum_le _ _
    _ ≤ ∑ j : Fin m, ∑ i ∈ Finset.range (n j),
          |q j i - r j i| * (‖f j‖ * (h j i : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pressure_step_duhamel_l1_stability S
        (n j) (τ j) (h j) (q j) (r j) (f j)

end MultiwellL1

end ReservoirSeismicityControl
