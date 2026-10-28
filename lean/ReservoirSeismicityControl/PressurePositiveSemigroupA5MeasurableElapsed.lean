import ReservoirSeismicityControl.PressurePositiveSemigroupStepBochnerIdentification
import ReservoirSeismicityControl.PressurePositiveSemigroupA5BochnerBridge

/-!
# A5 for arbitrary essentially bounded signed elapsed-time well rates

This combines the actual grid-averaged L1 approximants, the exact finite-step
Bochner identification, the semigroup L1 stability theorem, and the sharp
multiwell generator step-limit estimate. No input-derivative assumption occurs.

The self-adjoint generator graph characterization remains an explicit premise.
The transformation from physical forward time s to elapsed time t-s, and the
identification with the 3D physical Neumann generator, are separate tasks.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

section MeasurableElapsed

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Sharp A5 for finitely many arbitrarily measurable signed inputs in elapsed
(backward) time. All rate approximations, coefficient bounds, Bochner
integrability claims, and finite-step integral identifications are PROVED,
not postulated. The only non-constructive input is the arbitrary refining
time grid, whose hypotheses involve its geometry rather than the rates. -/
theorem pressure_multiwell_A5_measurable_elapsed
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H)
    (r : Fin m → ℝ → ℝ)
    (hr : ∀ j, Integrable (r j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |r j s| ≤ M j)
    (N : ℕ → ℕ) (τ h : ℕ → ℕ → NNReal)
    (hMono : ∀ k, Monotone (τ k))
    (hStrict : ∀ k i, i < N k → τ k i < τ k (i + 1))
    (hStart : ∀ k, τ k 0 = 0)
    (hEnd : ∀ k, τ k (N k) = t)
    (hStep : ∀ k i, i < N k → τ k (i + 1) = τ k i + h k i)
    (mesh : ℕ → ℝ)
    (hLength : ∀ k i, i < N k →
      (τ k (i + 1) : ℝ) - (τ k i : ℝ) ≤ mesh k)
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    ∃ hp : (S t (p₀ : H) +
        pressureMultiwellBochnerForcing S
          (volume.restrict (Set.Ico 0 (t : ℝ)))
          Real.toNNReal m f r) ∈ S.generatorDomain,
      ‖S.generator ⟨S t (p₀ : H) +
          pressureMultiwellBochnerForcing S
            (volume.restrict (Set.Ico 0 (t : ℝ)))
            Real.toNNReal m f r, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  let μT : Measure ℝ := volume.restrict (Set.Ico 0 (t : ℝ))
  let a : ℕ → ℕ → ℝ := fun k i => (τ k i : ℝ)
  let c : ℕ → Fin m → ℕ → ℝ := fun k j i =>
    ⨍ s, r j s ∂(μT.restrict (Set.Ico (a k i) (a k (i + 1))))
  let qStep : ℕ → Fin m → ℝ → ℝ := fun k j =>
    pressureTimeGridStepRate (N k) (a k) (c k j)
  have haMono (k : ℕ) : Monotone (a k) := by
    intro i i' hii'
    exact_mod_cast hMono k hii'
  have haStrict (k i : ℕ) (hi : i < N k) :
      a k i < a k (i + 1) := by
    exact_mod_cast hStrict k i hi
  have haStart (k : ℕ) : a k 0 = 0 := by
    simp [a, hStart k]
  have haEnd (k : ℕ) : a k (N k) = (t : ℝ) := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (hEnd k)
  have hCellSubset (k : ℕ) (i : Fin (N k)) :
      Set.Ico (a k i.val) (a k (i.val + 1)) ⊆ Set.Ico 0 (t : ℝ) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · calc
        0 = a k 0 := (haStart k).symm
        _ ≤ a k i.val := haMono k (Nat.zero_le _)
        _ ≤ s := hs.1
    · calc
        s < a k (i.val + 1) := hs.2
        _ ≤ a k (N k) := haMono k (Nat.succ_le_of_lt i.isLt)
        _ = (t : ℝ) := haEnd k
  have hCoeff (k : ℕ) (j : Fin m) (i : ℕ) (hi : i < N k) :
      |c k j i| ≤ M j := by
    exact pressure_time_grid_cell_average_bound
      (t : ℝ) (a k i) (a k (i + 1))
      (hCellSubset k ⟨i, hi⟩) (haStrict k i hi)
      (r j) (hr j) (M j) (hBound j)
  have hScalarStepInt (k : ℕ) (j : Fin m) :
      Integrable (qStep k j) μT :=
    pressure_time_grid_step_integrable (N k) (a k) (haMono k)
      (haStart k) (t : ℝ) (haEnd k) (c k j) (M j) (hCoeff k j)
  have hL1 (j : Fin m) :
      Tendsto (fun k => ∫ s, |qStep k j s - r j s| ∂μT)
        atTop (𝓝 0) := by
    have h := pressure_time_grid_actual_step_l1_tendsto
      (t : ℝ) N a haMono haStrict haStart haEnd mesh hLength hMesh
      (r j) (hr j) (M j) (hBound j)
    have hEq :
        (fun k => ∫ s, |qStep k j s - r j s| ∂μT) =
        (fun k => ∫ s, |r j s - qStep k j s| ∂μT) := by
      funext k
      apply integral_congr_ae
      filter_upwards with s
      rw [abs_sub_comm]
    rw [hEq]
    exact h
  have hKernelContinuous (j : Fin m) :
      Continuous (fun s : ℝ => S (Real.toNNReal s) (f j)) :=
    S.continuous_operator_toNNReal (f j)
  letI : IsFiniteMeasure μT := inferInstance
  have hOriginalVectorInt (j : Fin m) :
      Integrable (fun s => r j s • S (Real.toNNReal s) (f j)) μT := by
    have hMeas : AEStronglyMeasurable
        (fun s => r j s • S (Real.toNNReal s) (f j)) μT :=
      (hr j).aestronglyMeasurable.smul
        (hKernelContinuous j).aestronglyMeasurable
    have hVectorBound : ∀ᵐ s ∂μT,
        ‖r j s • S (Real.toNNReal s) (f j)‖ ≤ M j * ‖f j‖ := by
      filter_upwards [hBound j] with s hs
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |r j s| * ‖S (Real.toNNReal s) (f j)‖ ≤
            |r j s| * ‖f j‖ :=
          mul_le_mul_of_nonneg_left
            (S.norm_apply_le (Real.toNNReal s) (f j)) (abs_nonneg _)
        _ ≤ M j * ‖f j‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    exact Integrable.of_bound hMeas (M j * ‖f j‖) hVectorBound
  have hStepVectorInt (k : ℕ) (j : Fin m) :
      Integrable (fun s => qStep k j s • S (Real.toNNReal s) (f j)) μT := by
    have hMeas : AEStronglyMeasurable
        (fun s => qStep k j s • S (Real.toNNReal s) (f j)) μT :=
      (pressure_time_grid_step_measurable (N k) (a k) (c k j)).aestronglyMeasurable.smul
        (hKernelContinuous j).aestronglyMeasurable
    have hStepBound : ∀ᵐ s ∂μT, |qStep k j s| ≤ M j :=
      pressure_time_grid_step_ae_bound (N k) (a k) (haMono k)
        (haStart k) (t : ℝ) (haEnd k) (c k j) (M j) (hCoeff k j)
    have hVectorBound : ∀ᵐ s ∂μT,
        ‖qStep k j s • S (Real.toNNReal s) (f j)‖ ≤ M j * ‖f j‖ := by
      filter_upwards [hStepBound] with s hs
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |qStep k j s| * ‖S (Real.toNNReal s) (f j)‖ ≤
            |qStep k j s| * ‖f j‖ :=
          mul_le_mul_of_nonneg_left
            (S.norm_apply_le (Real.toNNReal s) (f j)) (abs_nonneg _)
        _ ≤ M j * ‖f j‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    exact Integrable.of_bound hMeas (M j * ‖f j‖) hVectorBound
  have hIdentify (k : ℕ) :
      (pressureMultiwellStepDuhamelDomain S m
        (fun _ => N k) (fun _ => τ k) (fun _ => h k)
        (c k) f : H) =
      pressureMultiwellBochnerForcing S μT Real.toNNReal m f (qStep k) := by
    unfold pressureMultiwellStepDuhamelDomain pressureMultiwellBochnerForcing
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact pressure_step_grid_bochner_identification
      S (N k) (τ k) (h k) (hMono k) (hStart k)
      (hStep k) t (hEnd k) (c k j) (M j) (hM j)
      (hCoeff k j) (f j)
  exact pressure_multiwell_A5_of_bochner_step_approximation
    S hSelf hGraph t p₀ m
    (fun k _ => N k) (fun k _ => τ k) (fun k _ => h k)
    (fun k _ => hStart k) (fun k _ => hStep k)
    c M hM hCoeff f μT Real.toNNReal qStep r
    hScalarStepInt hr hStepVectorInt hOriginalVectorInt hL1 hIdentify

end MeasurableElapsed

end ReservoirSeismicityControl
