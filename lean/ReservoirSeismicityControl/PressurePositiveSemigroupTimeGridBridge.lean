import ReservoirSeismicityControl.PressurePositiveSemigroupTimeIntervalCells
import ReservoirSeismicityControl.PressurePositiveSemigroupAverageBound
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Order.Interval.Set.Union

/-!
# ReservoirSeismicityControl (A5): full time-grid bridge for measurable rates

This module consolidates the interval geometry and L1 approximation argument.
It works for any sequence of finite, strictly ordered time grids with a
vanishing maximum cell length. The physical time measure is Lebesgue measure
restricted to `[0,T)`. It proves (i) the exact finite interval cover,
(ii) pairwise disjointness, (iii) nonzero cell measures, (iv) L1 convergence
of the interval averages for any integrable signed rate, and (v) preservation
of a uniform essential bound by each interval average.

The hypotheses on the grids concern their endpoints and maximum cell size,
not the regularity of the well rates. There is NO assumption on q's derivative.
The next substantive task is to identify these average-driven step functions
with the Bochner Duhamel integral and the semigroup partition formula.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- A finite monotone grid covers exactly the interval between its endpoints. -/
theorem pressure_monotone_time_grid_union
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a) :
    (⋃ i : Fin N, Set.Ico (a i.val) (a (i.val + 1))) =
      Set.Ico (a 0) (a N) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hlo : a 0 ≤ a i.val := ha (Nat.zero_le _)
    have hhi : a (i.val + 1) ≤ a N :=
      ha (Nat.succ_le_of_lt i.isLt)
    exact ⟨hlo.trans hi.1, hi.2.trans_le hhi⟩
  · intro x hx
    have h := Ico_subset_biUnion_Ico N a hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨hIndex, hiCell⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, Finset.mem_range.mp hIndex⟩, hiCell⟩

/-- Non-overlapping consecutive grid cells are pairwise disjoint. -/
theorem pressure_monotone_time_grid_disjoint
    (N : ℕ) (a : ℕ → ℝ) (ha : Monotone a) :
    Pairwise (fun (i j : Fin N) =>
      Disjoint (Set.Ico (a i.val) (a (i.val + 1)))
        (Set.Ico (a j.val) (a (j.val + 1)))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hij' : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
    exact pressure_time_Ico_disjoint (ha hij')
  · have hji' : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hji
    exact (pressure_time_Ico_disjoint (ha hji')).symm

/-- The whole interval-average approximation theorem for a genuine sequence
of finite time grids. There are no abstract cell-cover or cell-mass premises.
All measure identities and cell geometry are discharged here.

`N k` is the number of cells; `a k i` are grid knots. `mesh k` is a
nonnegative upper bound on cell length (it need not be the exact maximum).
The grid length need not be fixed across k, but endpoints remain 0 and T.
-/
theorem pressure_time_grid_measurable_average_l1_tendsto
    (T : ℝ)
    (N : ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (hMono : ∀ k, Monotone (a k))
    (hStrict : ∀ k i, i < N k → a k i < a k (i + 1))
    (hStart : ∀ k, a k 0 = 0)
    (hEnd : ∀ k, a k (N k) = T)
    (mesh : ℕ → ℝ)
    (hLength : ∀ k i, i < N k → a k (i + 1) - a k i ≤ mesh k)
    (hMesh : Tendsto mesh atTop (𝓝 0))
    (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico 0 T))) :
    Tendsto
      (fun k => ∑ i : Fin (N k),
        ∫ s, |q s - (⨍ r, q r
            ∂((volume.restrict (Set.Ico 0 T)).restrict
                (Set.Ico (a k i.val) (a k (i.val + 1)))))|
          ∂((volume.restrict (Set.Ico 0 T)).restrict
              (Set.Ico (a k i.val) (a k (i.val + 1)))))
      atTop (𝓝 0) := by
  let μT : Measure ℝ := volume.restrict (Set.Ico 0 T)
  letI : IsFiniteMeasure μT := inferInstance
  letI : μT.Regular :=
    Measure.Regular.restrict_of_measure_ne_top (by simp [Real.volume_Ico])
  let cells : ∀ k, Fin (N k) → Set ℝ :=
    fun k i => Set.Ico (a k i.val) (a k (i.val + 1))
  have hMeas (k : ℕ) (i : Fin (N k)) :
      MeasurableSet (cells k i) := measurableSet_Ico
  have hDisjoint (k : ℕ) :
      Pairwise (fun (i j : Fin (N k)) =>
        Disjoint (cells k i) (cells k j)) :=
    pressure_monotone_time_grid_disjoint (N k) (a k) (hMono k)
  have hUnion (k : ℕ) :
      (⋃ i : Fin (N k), cells k i) = Set.Ico 0 T := by
    change (⋃ i : Fin (N k),
      Set.Ico (a k i.val) (a k (i.val + 1))) = Set.Ico 0 T
    rw [pressure_monotone_time_grid_union (N k) (a k) (hMono k),
      hStart k, hEnd k]
  have hCover (k : ℕ) :
      μT.restrict (⋃ i, cells k i) = μT := by
    rw [hUnion k]
    change (volume.restrict (Set.Ico 0 T)).restrict (Set.Ico 0 T) =
      volume.restrict (Set.Ico 0 T)
    exact Measure.restrict_restrict_of_subset Set.Subset.rfl
  have hCellSubset (k : ℕ) (i : Fin (N k)) :
      cells k i ⊆ Set.Ico 0 T := by
    intro x hx
    change x ∈ Set.Ico (a k i.val) (a k (i.val + 1)) at hx
    refine ⟨?_, ?_⟩
    · calc
        0 = a k 0 := (hStart k).symm
        _ ≤ a k i.val := (hMono k) (Nat.zero_le _)
        _ ≤ x := hx.1
    · calc
        x < a k (i.val + 1) := hx.2
        _ ≤ a k (N k) := (hMono k) (Nat.succ_le_of_lt i.isLt)
        _ = T := hEnd k
  have hNonzero (k : ℕ) (i : Fin (N k)) :
      NeZero (μT.restrict (cells k i)) := by
    change NeZero ((volume.restrict (Set.Ico 0 T)).restrict
      (Set.Ico (a k i.val) (a k (i.val + 1))))
    rw [Measure.restrict_restrict_of_subset (hCellSubset k i)]
    exact pressure_time_Ico_nonzero _ _ (hStrict k i.val i.isLt)
  have hRadius (k : ℕ) (i : Fin (N k)) :
      ∀ x ∈ cells k i, dist x (a k i.val) ≤ mesh k := by
    intro x hx
    exact (pressure_time_Ico_left_radius hx).trans
      (hLength k i.val i.isLt)
  have hMain :=
    pressure_finite_measurable_cell_averages_l1_tendsto
      μT N cells hMeas hDisjoint hCover hNonzero q hq
      (fun k i => a k i.val) mesh hRadius hMesh
  exact hMain

/-- Every grid-cell average of a bounded signed rate respects the same
uniform bound. The representative q may be arbitrary on a null set. -/
theorem pressure_time_grid_cell_average_bound
    (T : ℝ) (a b : ℝ)
    (hSubset : Set.Ico a b ⊆ Set.Ico 0 T)
    (hab : a < b)
    (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico 0 T)))
    (M : ℝ)
    (hBound : ∀ᵐ s ∂(volume.restrict (Set.Ico 0 T)), |q s| ≤ M) :
    |⨍ s, q s ∂((volume.restrict (Set.Ico 0 T)).restrict (Set.Ico a b))| ≤ M := by
  let μT : Measure ℝ := volume.restrict (Set.Ico 0 T)
  have hEq : μT.restrict (Set.Ico a b) = volume.restrict (Set.Ico a b) := by
    exact Measure.restrict_restrict_of_subset hSubset
  have hIntCell : Integrable q (μT.restrict (Set.Ico a b)) :=
    hq.mono_measure Measure.restrict_le_self
  have hBoundCell : ∀ᵐ s ∂(μT.restrict (Set.Ico a b)), |q s| ≤ M :=
    ae_mono Measure.restrict_le_self hBound
  letI : IsFiniteMeasure (μT.restrict (Set.Ico a b)) := inferInstance
  letI : NeZero (μT.restrict (Set.Ico a b)) := by
    rw [hEq]
    exact pressure_time_Ico_nonzero a b hab
  exact pressure_average_preserves_signed_bound
    (μT.restrict (Set.Ico a b)) q M hIntCell hBoundCell

end ReservoirSeismicityControl
