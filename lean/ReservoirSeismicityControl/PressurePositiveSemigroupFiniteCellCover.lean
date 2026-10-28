import ReservoirSeismicityControl.PressurePositiveSemigroupMeasurableAverages
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# ReservoirSeismicityControl (A5): finite measurable time-cell cover

This module applies the verified L1 convergence theorem to restrictions
of a *single* finite regular time measure to finite measurable cells.
It proves the covering-measure identity, measure domination, and fixed
cell mass from a genuine disjoint measurable cover, rather than taking
these properties as abstract hypotheses. It is enough that the cells
cover the time measure almost everywhere: their union need not be all of ℝ.

The remaining geometric obligations are explicit: a choice of intervals,
nonzero cell measures, and shrinking cell radii. No temporal derivative
is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

/-- A finite disjoint measurable cover induces the correct decomposition
of the underlying time measure into restricted cell measures. -/
theorem pressure_finite_cell_restrict_cover
    (μ₀ : Measure ℝ) (ι : Type*) [Fintype ι]
    (cells : ι → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hCover : μ₀.restrict (⋃ i, cells i) = μ₀) :
    (∑ i : ι, μ₀.restrict (cells i)) = μ₀ := by
  calc
    (∑ i : ι, μ₀.restrict (cells i)) =
        Measure.sum (fun i : ι => μ₀.restrict (cells i)) :=
      (Measure.sum_fintype _).symm
    _ = μ₀.restrict (⋃ i, cells i) :=
      (μ₀.restrict_iUnion hDisjoint hMeas).symm
    _ = μ₀ := hCover

/-- The total real mass of the restricted cells is the mass of the
original finite time measure. -/
theorem pressure_finite_cell_real_mass
    (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀]
    (ι : Type*) [Fintype ι]
    (cells : ι → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hCover : μ₀.restrict (⋃ i, cells i) = μ₀) :
    (∑ i : ι, (μ₀.restrict (cells i)).real Set.univ) = μ₀.real Set.univ := by
  have hPairs :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) cells := by
    intro i hi j hj hij
    exact hDisjoint hij
  have hSum := measureReal_biUnion_finset
    (μ := μ₀) (s := (Finset.univ : Finset ι))
    (f := cells) hPairs (fun i _ => hMeas i)
  have hUnion : (⋃ i ∈ (Finset.univ : Finset ι), cells i) =
      (⋃ i, cells i) := by simp
  rw [hUnion] at hSum
  have hRealCover : μ₀.real (⋃ i, cells i) = μ₀.real Set.univ := by
    have hh := congrArg (fun ν : Measure ℝ => ν.real Set.univ) hCover
    simpa only [measureReal_restrict_apply_univ] using hh
  calc
    (∑ i : ι, (μ₀.restrict (cells i)).real Set.univ) =
        ∑ i : ι, μ₀.real (cells i) := by simp
    _ = μ₀.real (⋃ i, cells i) := by
      simpa using hSum.symm
    _ = μ₀.real Set.univ := hRealCover

/-- For disjoint measurable cells whose diameter shrinks, interval-cell
averages of any integrable signed input converge in the total L1 error.
The abstract cover, domination, and mass hypotheses have been discharged
using the geometry of a finite disjoint measurable partition.

It remains to instantiate `cells` with the chosen actual time intervals
and to verify their nonzero measures and radius bounds. -/
theorem pressure_finite_measurable_cell_averages_l1_tendsto
    (μ₀ : Measure ℝ) [μ₀.Regular] [IsFiniteMeasure μ₀]
    (n : ℕ → ℕ)
    (cells : ∀ k, Fin (n k) → Set ℝ)
    (hMeas : ∀ k i, MeasurableSet (cells k i))
    (hDisjoint : ∀ k, Pairwise (fun i j => Disjoint (cells k i) (cells k j)))
    (hCover : ∀ k, μ₀.restrict (⋃ i, cells k i) = μ₀)
    (hNonzero : ∀ k i, NeZero (μ₀.restrict (cells k i)))
    (q : ℝ → ℝ) (hq : Integrable q μ₀)
    (centers : ∀ k, Fin (n k) → ℝ)
    (mesh : ℕ → ℝ)
    (hRadius : ∀ k i, ∀ x ∈ cells k i,
      dist x (centers k i) ≤ mesh k)
    (hMesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ i : Fin (n k),
        ∫ x, |q x - (⨍ y, q y ∂(μ₀.restrict (cells k i)))|
          ∂(μ₀.restrict (cells k i)))
      atTop (𝓝 0) := by
  have hFinite (k : ℕ) (i : Fin (n k)) :
      IsFiniteMeasure (μ₀.restrict (cells k i)) := inferInstance
  have hMeasureCover (k : ℕ) :
      (∑ i : Fin (n k), μ₀.restrict (cells k i)) = μ₀ :=
    pressure_finite_cell_restrict_cover μ₀ (Fin (n k)) (cells k)
      (hMeas k) (hDisjoint k) (hCover k)
  have hDom (k : ℕ) (i : Fin (n k)) :
      μ₀.restrict (cells k i) ≤ μ₀ := Measure.restrict_le_self
  have hAeRadius (k : ℕ) (i : Fin (n k)) :
      ∀ᵐ x ∂(μ₀.restrict (cells k i)),
        dist x (centers k i) ≤ mesh k := by
    filter_upwards [ae_restrict_mem (hMeas k i)] with x hx
    exact hRadius k i x hx
  have hMass (k : ℕ) :
      (∑ i : Fin (n k), (μ₀.restrict (cells k i)).real Set.univ) =
        μ₀.real Set.univ :=
    pressure_finite_cell_real_mass μ₀ (Fin (n k)) (cells k)
      (hMeas k) (hDisjoint k) (hCover k)
  exact pressure_partition_integrable_average_l1_tendsto
    μ₀ n (fun k i => μ₀.restrict (cells k i))
    hFinite hNonzero hMeasureCover hDom q hq
    centers mesh hAeRadius (μ₀.real Set.univ) hMass hMesh

end ReservoirSeismicityControl
