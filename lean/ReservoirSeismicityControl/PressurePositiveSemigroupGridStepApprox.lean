import ReservoirSeismicityControl.PressurePositiveSemigroupTimeGridBridge
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl (A5): actual measurable interval-step input

This file changes the earlier cellwise estimates into an actual function of time.
For a finite ordered grid, the function is the sum of signed coefficients
multiplied by indicators of half-open cells.

The main theorem proves an exact identity between the L1 error of this
piecewise-constant function and the sum of cellwise errors. Combining it
with `pressure_time_grid_measurable_average_l1_tendsto` will give the
strong L1 convergence required by the previously compiled Bochner bridge.
There is no regularity condition on the derivative of the input.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- Signed finite-grid step function. Its coefficients can be averages or
arbitrary real numbers, including negative values. -/
noncomputable def pressureTimeGridStepRate
    (N : ℕ) (a : ℕ → ℝ) (c : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin N,
    (Set.Ico (a i.val) (a (i.val + 1))).indicator
      (fun _ : ℝ => c i.val) s

/-- A step input equals its coefficient on its own cell. -/
theorem pressure_time_grid_step_on_cell
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a)
    (c : ℕ → ℝ) (i : Fin N) (s : ℝ)
    (hs : s ∈ Set.Ico (a i.val) (a (i.val + 1))) :
    pressureTimeGridStepRate N a c s = c i.val := by
  have hDisjoint := pressure_monotone_time_grid_disjoint N a ha
  unfold pressureTimeGridStepRate
  rw [Finset.sum_eq_single i]
  · simp [hs]
  · intro j hj hji
    have hdisj :
        Disjoint (Set.Ico (a j.val) (a (j.val + 1)))
          (Set.Ico (a i.val) (a (i.val + 1))) :=
      hDisjoint hji
    have hnot : s ∉ Set.Ico (a j.val) (a (j.val + 1)) := by
      intro hsj
      exact Set.disjoint_left.mp hdisj hsj hs
    simp [hnot]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Measurability is proved for the concrete step function, not postulated. -/
theorem pressure_time_grid_step_measurable
    (N : ℕ) (a : ℕ → ℝ) (c : ℕ → ℝ) :
    Measurable (pressureTimeGridStepRate N a c) := by
  unfold pressureTimeGridStepRate
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator measurableSet_Ico

/-- Essential boundedness of the finite-grid step function. The grid covers
`[0,T)`; its intervals need not cover all of `ℝ`. -/
theorem pressure_time_grid_step_ae_bound
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a)
    (hStart : a 0 = 0) (T : ℝ) (hEnd : a N = T)
    (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ i < N, |c i| ≤ M) :
    ∀ᵐ s ∂(volume.restrict (Set.Ico 0 T)),
      |pressureTimeGridStepRate N a c s| ≤ M := by
  filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
  have hUnion := pressure_monotone_time_grid_union N a ha
  rw [hStart, hEnd] at hUnion
  rw [← hUnion] at hs
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
  rw [pressure_time_grid_step_on_cell N a ha c i s hi]
  exact hc i.val i.isLt

/-- The actual step input is integrable over the observation interval.
No continuity of the original rate and no bounded derivative is needed. -/
theorem pressure_time_grid_step_integrable
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a)
    (hStart : a 0 = 0) (T : ℝ) (hEnd : a N = T)
    (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ i < N, |c i| ≤ M) :
    Integrable (pressureTimeGridStepRate N a c)
      (volume.restrict (Set.Ico 0 T)) := by
  letI : IsFiniteMeasure (volume.restrict (Set.Ico 0 T)) := inferInstance
  apply Integrable.of_bound
    (pressure_time_grid_step_measurable N a c).aestronglyMeasurable M
  simpa only [Real.norm_eq_abs] using
    pressure_time_grid_step_ae_bound N a ha hStart T hEnd c M hc

/-- A single finite-grid cell has the same measure whether restricted
first to `[0,T)` or directly from Lebesgue measure. -/
theorem pressure_time_grid_restrict_cell
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a)
    (hStart : a 0 = 0) (T : ℝ) (hEnd : a N = T)
    (i : Fin N) :
    (volume.restrict (Set.Ico 0 T)).restrict
        (Set.Ico (a i.val) (a (i.val + 1))) =
      volume.restrict (Set.Ico (a i.val) (a (i.val + 1))) := by
  apply Measure.restrict_restrict_of_subset
  intro s hs
  refine ⟨?_, ?_⟩
  · calc
      0 = a 0 := hStart.symm
      _ ≤ a i.val := ha (Nat.zero_le _)
      _ ≤ s := hs.1
  · calc
      s < a (i.val + 1) := hs.2
      _ ≤ a N := ha (Nat.succ_le_of_lt i.isLt)
      _ = T := hEnd

/-- The exact global error of the *actual* interval-step function equals
its summed local cell errors. There are no Bochner-semigroup assumptions.
This is the remaining measure-theoretic link from the verified cell-average
estimates to concrete approximating functions. -/
theorem pressure_time_grid_step_l1_error_eq_cell_sum
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a)
    (hStart : a 0 = 0) (T : ℝ) (hEnd : a N = T)
    (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ i < N, |c i| ≤ M)
    (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico 0 T))) :
    (∫ s, |q s - pressureTimeGridStepRate N a c s|
      ∂(volume.restrict (Set.Ico 0 T))) =
    ∑ i : Fin N,
      ∫ s, |q s - c i.val|
        ∂((volume.restrict (Set.Ico 0 T)).restrict
            (Set.Ico (a i.val) (a (i.val + 1)))) := by
  let μT : Measure ℝ := volume.restrict (Set.Ico 0 T)
  let cells : Fin N → Set ℝ :=
    fun i => Set.Ico (a i.val) (a (i.val + 1))
  have hMeas : ∀ i : Fin N, MeasurableSet (cells i) :=
    fun i => measurableSet_Ico
  have hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)) :=
    pressure_monotone_time_grid_disjoint N a ha
  have hUnion : (⋃ i : Fin N, cells i) = Set.Ico 0 T := by
    change (⋃ i : Fin N, Set.Ico (a i.val) (a (i.val + 1))) = _
    rw [pressure_monotone_time_grid_union N a ha, hStart, hEnd]
  have hCover : μT.restrict (⋃ i, cells i) = μT := by
    rw [hUnion]
    change (volume.restrict (Set.Ico 0 T)).restrict (Set.Ico 0 T) =
      volume.restrict (Set.Ico 0 T)
    exact Measure.restrict_restrict_of_subset Set.Subset.rfl
  have hMeasureCover : (∑ i : Fin N, μT.restrict (cells i)) = μT :=
    pressure_finite_cell_restrict_cover μT (Fin N) cells
      hMeas hDisjoint hCover
  have hStepInt : Integrable (pressureTimeGridStepRate N a c) μT :=
    pressure_time_grid_step_integrable N a ha hStart T hEnd c M hc
  have hDiffInt : Integrable
      (fun s => |q s - pressureTimeGridStepRate N a c s|) μT :=
    (hq.sub hStepInt).abs
  have hCellsInt (i : Fin N) : Integrable
      (fun s => |q s - pressureTimeGridStepRate N a c s|)
      (μT.restrict (cells i)) :=
    hDiffInt.mono_measure Measure.restrict_le_self
  calc
    (∫ s, |q s - pressureTimeGridStepRate N a c s| ∂μT) =
        ∫ s, |q s - pressureTimeGridStepRate N a c s|
          ∂(∑ i : Fin N, μT.restrict (cells i)) := by
            rw [hMeasureCover]
    _ = ∑ i : Fin N,
          ∫ s, |q s - pressureTimeGridStepRate N a c s|
            ∂(μT.restrict (cells i)) := by
          exact integral_finsetSum_measure (fun i _ => hCellsInt i)
    _ = ∑ i : Fin N, ∫ s, |q s - c i.val|
          ∂(μT.restrict (cells i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (hMeas i)] with s hs
          rw [pressure_time_grid_step_on_cell N a ha c i s hs]
    _ = ∑ i : Fin N, ∫ s, |q s - c i.val|
          ∂((volume.restrict (Set.Ico 0 T)).restrict
              (Set.Ico (a i.val) (a (i.val + 1)))) := rfl


/-- The actual *functions* formed from cell averages converge in `L¹` to any
integrable essentially bounded signed rate on `[0,T)`. This is the first
place where the previously verified time-grid estimates become a concrete
strong approximation statement, with no hypothesis about the convergence
of the step functions themselves. -/
theorem pressure_time_grid_actual_step_l1_tendsto
    (T : ℝ) (N : ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (hMono : ∀ k, Monotone (a k))
    (hStrict : ∀ k i, i < N k → a k i < a k (i + 1))
    (hStart : ∀ k, a k 0 = 0)
    (hEnd : ∀ k, a k (N k) = T)
    (mesh : ℕ → ℝ)
    (hLength : ∀ k i, i < N k → a k (i + 1) - a k i ≤ mesh k)
    (hMesh : Tendsto mesh atTop (𝓝 0))
    (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico 0 T)))
    (M : ℝ)
    (hBound : ∀ᵐ s ∂(volume.restrict (Set.Ico 0 T)), |q s| ≤ M) :
    Tendsto
      (fun k => ∫ s,
        |q s - pressureTimeGridStepRate (N k) (a k)
          (fun i => ⨍ r, q r
            ∂((volume.restrict (Set.Ico 0 T)).restrict
                (Set.Ico (a k i) (a k (i + 1))))) s|
        ∂(volume.restrict (Set.Ico 0 T)))
      atTop (𝓝 0) := by
  let c : ℕ → ℕ → ℝ := fun k i =>
    ⨍ r, q r ∂((volume.restrict (Set.Ico 0 T)).restrict
      (Set.Ico (a k i) (a k (i + 1))))
  have hSubset (k : ℕ) (i : Fin (N k)) :
      Set.Ico (a k i.val) (a k (i.val + 1)) ⊆ Set.Ico 0 T := by
    intro s hs
    refine ⟨?_, ?_⟩
    · calc
        0 = a k 0 := (hStart k).symm
        _ ≤ a k i.val := (hMono k) (Nat.zero_le _)
        _ ≤ s := hs.1
    · calc
        s < a k (i.val + 1) := hs.2
        _ ≤ a k (N k) := (hMono k) (Nat.succ_le_of_lt i.isLt)
        _ = T := hEnd k
  have hCoeff (k : ℕ) (i : ℕ) (hi : i < N k) :
      |c k i| ≤ M := by
    exact pressure_time_grid_cell_average_bound T (a k i) (a k (i + 1))
      (hSubset k ⟨i, hi⟩) (hStrict k i hi) q hq M hBound
  have hGlobalEq (k : ℕ) :
      (∫ s, |q s - pressureTimeGridStepRate (N k) (a k) (c k) s|
          ∂(volume.restrict (Set.Ico 0 T))) =
        ∑ i : Fin (N k),
          ∫ s, |q s - c k i.val|
            ∂((volume.restrict (Set.Ico 0 T)).restrict
                (Set.Ico (a k i.val) (a k (i.val + 1)))) :=
    pressure_time_grid_step_l1_error_eq_cell_sum
      (N k) (a k) (hMono k) (hStart k) T (hEnd k)
      (c k) M (hCoeff k) q hq
  have hGrid := pressure_time_grid_measurable_average_l1_tendsto
      T N a hMono hStrict hStart hEnd mesh hLength hMesh q hq
  have hFunctionsEq :
      (fun k => ∫ s,
        |q s - pressureTimeGridStepRate (N k) (a k) (c k) s|
          ∂(volume.restrict (Set.Ico 0 T))) =
      (fun k => ∑ i : Fin (N k),
        ∫ s, |q s - c k i.val|
          ∂((volume.restrict (Set.Ico 0 T)).restrict
              (Set.Ico (a k i.val) (a k (i.val + 1))))) := by
    funext k
    exact hGlobalEq k
  change Tendsto
    (fun k => ∫ s, |q s - pressureTimeGridStepRate (N k) (a k) (c k) s|
      ∂(volume.restrict (Set.Ico 0 T))) atTop (𝓝 0)
  rw [hFunctionsEq]
  exact hGrid

end ReservoirSeismicityControl
