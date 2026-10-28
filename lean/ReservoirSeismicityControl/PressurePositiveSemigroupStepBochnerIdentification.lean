import ReservoirSeismicityControl.PressurePositiveSemigroupGridStepApprox
import ReservoirSeismicityControl.PressurePositiveSemigroupStepDuhamel
import ReservoirSeismicityControl.PressurePositiveSemigroupA5BochnerBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# A5: identify concrete interval-step forcing with the orbit-integral step sum

This removes the `hIdentify` premise for the actual interval-step rates.
The time variable here is elapsed (backward) time: the input at elapsed
backward time `s` is the physical well rate at `t-s`.  The terminal change
of variables from physical forward time is a separate statement.

We use only strong continuity of the contraction semigroup, not any
assumption on the temporal derivative of the input.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators Interval

section OrbitWindow

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A shifted orbit integral is exactly the Bochner integral over its
elapsed-time cell `[τ, τ+h)`. -/
theorem pressure_step_orbit_equals_cell_bochner
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (f : H) (τ h : NNReal) :
    S τ (S.orbitIntegral f h) =
      ∫ s, S (Real.toNNReal s) f
        ∂(volume.restrict (Set.Ico (τ : ℝ) ((τ + h : NNReal) : ℝ))) := by
  let F : ℝ → H := fun s => S (Real.toNNReal s) f
  have hCont : Continuous F := S.continuous_operator_toNNReal f
  have hIntRight : IntervalIntegrable F volume 0 ((τ + h : NNReal) : ℝ) :=
    hCont.intervalIntegrable _ _
  have hIntLeft : IntervalIntegrable F volume 0 (τ : ℝ) :=
    hCont.intervalIntegrable _ _
  have hOrder : (τ : ℝ) ≤ ((τ + h : NNReal) : ℝ) := by
    rw [NNReal.coe_add]
    exact le_add_of_nonneg_right h.coe_nonneg
  calc
    S τ (S.orbitIntegral f h) =
        S.orbitIntegral f (τ + h) - S.orbitIntegral f τ :=
      pressure_step_orbit_time_window S f τ h
    _ = ∫ s in (τ : ℝ)..((τ + h : NNReal) : ℝ), F s := by
      simpa only [S.orbitIntegral_apply, NNReal.coe_add] using
        (intervalIntegral.integral_interval_sub_left hIntRight hIntLeft)
    _ = ∫ s in Set.Ico (τ : ℝ) ((τ + h : NNReal) : ℝ), F s ∂volume := by
      rw [intervalIntegral.integral_of_le hOrder]
      rw [Measure.restrict_congr_set (α := ℝ) (μ := volume) Ico_ae_eq_Ioc]
    _ = ∫ s, S (Real.toNNReal s) f
          ∂(volume.restrict (Set.Ico (τ : ℝ) ((τ + h : NNReal) : ℝ))) := rfl

end OrbitWindow

section GridIdentification

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The finite signed orbit sum equals the genuine Bochner integral of the
actual piecewise-constant input.  No identification assumption is present. -/
theorem pressure_step_grid_bochner_identification
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (N : ℕ) (τ h : ℕ → NNReal)
    (hMono : Monotone τ) (hStart : τ 0 = 0)
    (hStep : ∀ i < N, τ (i + 1) = τ i + h i)
    (t : NNReal) (hEnd : τ N = t)
    (c : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ i < N, |c i| ≤ M) (f : H) :
    (pressureStepDuhamelDomain S N τ h c f : H) =
      pressureBochnerForcing S
        (volume.restrict (Set.Ico 0 (t : ℝ))) Real.toNNReal f
        (pressureTimeGridStepRate N (fun i => (τ i : ℝ)) c) := by
  let a : ℕ → ℝ := fun i => (τ i : ℝ)
  let μT : Measure ℝ := volume.restrict (Set.Ico 0 (t : ℝ))
  let cells : Fin N → Set ℝ :=
    fun i => Set.Ico (a i.val) (a (i.val + 1))
  let r : ℝ → ℝ := pressureTimeGridStepRate N a c
  let F : ℝ → H := fun s => S (Real.toNNReal s) f
  have ha : Monotone a := fun _ _ hij => by
    exact_mod_cast hMono hij
  have ha0 : a 0 = 0 := by simp [a, hStart]
  have haN : a N = (t : ℝ) := congrArg (fun x : NNReal => (x : ℝ)) hEnd
  have hMeas : ∀ i : Fin N, MeasurableSet (cells i) :=
    fun i => measurableSet_Ico
  have hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)) :=
    pressure_monotone_time_grid_disjoint N a ha
  have hUnion : (⋃ i : Fin N, cells i) = Set.Ico 0 (t : ℝ) := by
    change (⋃ i : Fin N, Set.Ico (a i.val) (a (i.val + 1))) = _
    rw [pressure_monotone_time_grid_union N a ha, ha0, haN]
  have hMeasureCover : (∑ i : Fin N, μT.restrict (cells i)) = μT := by
    apply pressure_finite_cell_restrict_cover μT (Fin N) cells
      hMeas hDisjoint
    rw [hUnion]
    change (volume.restrict (Set.Ico 0 (t : ℝ))).restrict
      (Set.Ico 0 (t : ℝ)) = volume.restrict (Set.Ico 0 (t : ℝ))
    exact Measure.restrict_restrict_of_subset Set.Subset.rfl
  have hRateBound : ∀ᵐ s ∂μT, |r s| ≤ M := by
    exact pressure_time_grid_step_ae_bound N a ha ha0 (t : ℝ) haN c M hc
  have hKernelCont : Continuous F := S.continuous_operator_toNNReal f
  have hVectorMeas : AEStronglyMeasurable (fun s => r s • F s) μT :=
    (pressure_time_grid_step_measurable N a c).aestronglyMeasurable.smul
      hKernelCont.aestronglyMeasurable
  have hVectorBound : ∀ᵐ s ∂μT, ‖r s • F s‖ ≤ M * ‖f‖ := by
    filter_upwards [hRateBound] with s hs
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |r s| * ‖F s‖ ≤ |r s| * ‖f‖ :=
        mul_le_mul_of_nonneg_left
          (S.norm_apply_le (Real.toNNReal s) f) (abs_nonneg _)
      _ ≤ M * ‖f‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg f)
  letI : IsFiniteMeasure μT := inferInstance
  have hVectorInt : Integrable (fun s => r s • F s) μT :=
    Integrable.of_bound hVectorMeas (M * ‖f‖) hVectorBound
  have hEachInt (i : Fin N) : Integrable (fun s => r s • F s)
      (μT.restrict (cells i)) :=
    hVectorInt.mono_measure Measure.restrict_le_self
  have hCellSubset (i : Fin N) : cells i ⊆ Set.Ico 0 (t : ℝ) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · calc
        0 = a 0 := ha0.symm
        _ ≤ a i.val := ha (Nat.zero_le _)
        _ ≤ s := hs.1
    · calc
        s < a (i.val + 1) := hs.2
        _ ≤ a N := ha (Nat.succ_le_of_lt i.isLt)
        _ = (t : ℝ) := haN
  have hCellWindow (i : Fin N) :
      (∫ s, F s ∂(μT.restrict (cells i))) =
        S (τ i.val) (S.orbitIntegral f (h i.val)) := by
    have hRestrict : μT.restrict (cells i) = volume.restrict (cells i) := by
      exact Measure.restrict_restrict_of_subset (hCellSubset i)
    rw [hRestrict]
    change (∫ s, S (Real.toNNReal s) f
      ∂(volume.restrict (Set.Ico (τ i.val : ℝ) (τ (i.val + 1) : ℝ)))) = _
    rw [hStep i.val i.isLt]
    exact (pressure_step_orbit_equals_cell_bochner S f (τ i.val) (h i.val)).symm
  have hCellIntegral (i : Fin N) :
      (∫ s, r s • F s ∂(μT.restrict (cells i))) =
        c i.val • (S (τ i.val) (S.orbitIntegral f (h i.val))) := by
    calc
      (∫ s, r s • F s ∂(μT.restrict (cells i))) =
          ∫ s, c i.val • F s ∂(μT.restrict (cells i)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hMeas i)] with s hs
        have hRateCell : r s = c i.val :=
          pressure_time_grid_step_on_cell N a ha c i s hs
        rw [hRateCell]
      _ = c i.val • (∫ s, F s ∂(μT.restrict (cells i))) := by
        rw [integral_smul]
      _ = c i.val • (S (τ i.val) (S.orbitIntegral f (h i.val))) := by
        rw [hCellWindow i]
  have hIntegralSum :
      (∫ s, r s • F s ∂μT) =
        ∑ i : Fin N, c i.val • (S (τ i.val) (S.orbitIntegral f (h i.val))) := by
    calc
      (∫ s, r s • F s ∂μT) =
          ∫ s, r s • F s ∂(∑ i : Fin N, μT.restrict (cells i)) := by
            rw [hMeasureCover]
      _ = ∑ i : Fin N, ∫ s, r s • F s ∂(μT.restrict (cells i)) := by
        exact integral_finsetSum_measure (fun i _ => hEachInt i)
      _ = ∑ i : Fin N,
            c i.val • (S (τ i.val) (S.orbitIntegral f (h i.val))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hCellIntegral i
  unfold pressureBochnerForcing
  rw [show (∫ s, r s • F s ∂μT) =
      ∑ i : Fin N, c i.val • (S (τ i.val) (S.orbitIntegral f (h i.val))) from
      hIntegralSum]
  unfold pressureStepDuhamelDomain
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

end GridIdentification

end ReservoirSeismicityControl
