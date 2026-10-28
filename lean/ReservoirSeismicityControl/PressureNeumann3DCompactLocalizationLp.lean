import ReservoirSeismicityControl.PressureNeumann3DCompactCutoffBounds
import ReservoirSeismicityControl.PressureNeumann3DRestrictedAmbientDensity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Small L² error when localizing a smooth field inside Ω

We do not postulate an approximation theorem. Instead, inner regularity
selects a compact subset K of the reservoir whose complement has small
measure. A smooth interior cutoff equal to one on K then yields the
required quantitative L² estimate.

The measure used here is the actual ambient measure restricted to Ω.
The subsequent identification with the subtype measure is a separate step.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory Set
open scoped Distributions ENNReal

variable (Ω : Opens pressureNeumannE3)
variable (ν : Measure pressureNeumannE3)
variable [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]

/-- A bounded open reservoir can be exhausted in measure by a compact
subset entirely contained in its interior. -/
theorem pressure_neumann_3d_compact_interior_small_complement
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ K : Set pressureNeumannE3,
      IsCompact K ∧ K ⊆ (Ω : Set pressureNeumannE3) ∧
        ν ((Ω : Set pressureNeumannE3) \ K) < δ := by
  have hΩfinite : ν (Ω : Set pressureNeumannE3) ≠ ∞ :=
    (hΩ.measure_lt_top (μ := ν)).ne
  obtain ⟨K, hKΩ, hKcompact, _, hKsmall⟩ :=
    Ω.isOpen.measurableSet.exists_isCompact_isClosed_sdiff_lt hΩfinite hδ
  exact ⟨K, hKcompact, hKΩ, hKsmall⟩

/-- Any compactly supported ambient smooth field can be localized
inside Ω with arbitrarily small L² error (computed using ν.restrict Ω).
The codomain may be either ℝ or the three-dimensional vector space. -/
theorem pressure_neumann_3d_smooth_compact_localization_eLpNorm
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : pressureNeumannE3 → F)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ ψ : pressureNeumann3DSmoothScalarTests Ω,
      eLpNorm (fun x => f x - ψ x • f x) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ε := by
  let μ : Measure pressureNeumannE3 := ν.restrict (Ω : Set pressureNeumannE3)
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨δ, hδpos, hδbound⟩ :=
    exists_eLpNorm_indicator_le (μ := μ) (p := (2 : ℝ≥0∞))
      (c := C) (by norm_num) hε
  have hδ : (δ : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hδpos).ne'
  obtain ⟨K, hKcompact, hKΩ, hKsmall⟩ :=
    pressure_neumann_3d_compact_interior_small_complement Ω ν hΩ hδ
  obtain ⟨ψ, hψOne, hψBox, _⟩ :=
    pressure_neumann_3d_exists_compact_interior_cutoff Ω hΩ K hKcompact hKΩ
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hμsmall : μ ((Ω : Set pressureNeumannE3) \ K) ≤ (δ : ℝ≥0∞) :=
    (Measure.restrict_apply_le _ _).trans hKsmall.le
  have hindicator :
      eLpNorm (((Ω : Set pressureNeumannE3) \ K).indicator
          (fun _ : pressureNeumannE3 => C)) 2 μ ≤ ε :=
    hδbound _ hμsmall
      (Ω.isOpen.measurableSet.diff hKclosed.measurableSet).nullMeasurableSet
  have hmeas : AEStronglyMeasurable (fun x => f x - ψ x • f x) μ :=
    (hf.continuous.sub (ψ.contDiff.continuous.smul hf.continuous)).aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ,
      ‖f x - ψ x • f x‖ ≤
        ‖((Ω : Set pressureNeumannE3) \ K).indicator
          (fun _ : pressureNeumannE3 => C) x‖ := by
    filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hxΩ
    by_cases hxK : x ∈ K
    · have hxNot : x ∉ ((Ω : Set pressureNeumannE3) \ K) := fun h => h.2 hxK
      simp [hψOne x hxK, Set.indicator_of_notMem hxNot]
    · have hxD : x ∈ ((Ω : Set pressureNeumannE3) \ K) := ⟨hxΩ, hxK⟩
      rw [Set.indicator_of_mem hxD]
      have heq : f x - ψ x • f x = (1 - ψ x) • f x := by
        rw [sub_smul, one_smul]
      have hCnonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [(hψBox x).2])]
      have hcoef : 1 - ψ x ≤ (1 : ℝ) := by
        linarith [(hψBox x).1]
      have hbound : (1 - ψ x) * ‖f x‖ ≤ C := by
        calc
          (1 - ψ x) * ‖f x‖ ≤ 1 * ‖f x‖ :=
            mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
          _ = ‖f x‖ := one_mul _
          _ ≤ C := hC x
      simpa only [Real.norm_eq_abs, abs_of_nonneg hCnonneg] using hbound
  exact ⟨ψ, (eLpNorm_mono_ae hmeas hpoint).trans hindicator⟩

end ReservoirSeismicityControl
