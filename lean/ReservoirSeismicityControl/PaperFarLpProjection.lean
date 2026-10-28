import ReservoirSeismicityControl.PaperFarSpatialIndicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Stage 68 — Spatial indicator as a bounded operator on the actual L² quotient

Stage 67 established the pointwise and L²-seminorm properties of spatial
cutoffs. Here the cutoff is defined on `MeasureTheory.Lp ℝ 2 μ`, the space of
almost-everywhere classes, and is upgraded to a continuous linear map.

The cutoff is a norm contraction and an idempotent operator. We do not yet
assert its self-adjointness in the Hilbert-space inner product. Connecting
this concrete map to the abstract `P` of Stage 66 requires that final
inner-product bridge.

No control-input derivative is assumed or used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Indicator multiplication on the L² space of a general measure space. -/
noncomputable def paperFarLpCutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) : Lp ℝ (2 : ENNReal) μ :=
  MemLp.toLp (far.indicator (f : Ω → ℝ))
    ((Lp.memLp f).indicator hfar.nullMeasurableSet)

/-- Its representative equals the spatial indicator almost everywhere. -/
theorem paper_far_lp_cutoff_coeFn
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    (paperFarLpCutoff μ far hfar f : Ω → ℝ) =ᵐ[μ]
      far.indicator (f : Ω → ℝ) := by
  exact MemLp.coeFn_toLp ((Lp.memLp f).indicator hfar.nullMeasurableSet)

/-- Cutoff multiplication does not increase the norm on the L² quotient. -/
theorem paper_far_lp_cutoff_norm_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    ‖paperFarLpCutoff μ far hfar f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [paper_far_lp_cutoff_coeFn μ far hfar f] with x hx
  rw [hx]
  by_cases h : x ∈ far
  · simp only [Set.indicator_of_mem h]
    exact le_rfl
  · simp only [Set.indicator_of_notMem h, norm_zero]
    exact norm_nonneg _

/-- Indicator multiplication is additive on L² classes. -/
theorem paper_far_lp_cutoff_add
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f g : Lp ℝ (2 : ENNReal) μ) :
    paperFarLpCutoff μ far hfar (f + g) =
      paperFarLpCutoff μ far hfar f + paperFarLpCutoff μ far hfar g := by
  apply Lp.ext
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ far hfar (f + g),
       paper_far_lp_cutoff_coeFn μ far hfar f,
       paper_far_lp_cutoff_coeFn μ far hfar g,
       Lp.coeFn_add (paperFarLpCutoff μ far hfar f)
         (paperFarLpCutoff μ far hfar g),
       Lp.coeFn_add f g] with x hfg hf hg hsum harg
  rw [hfg, hsum]
  simp only [Pi.add_apply]
  rw [hf, hg]
  by_cases hx : x ∈ far
  · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using harg
  · simp only [Set.indicator_of_notMem hx, add_zero]

/-- Indicator multiplication respects real scalar multiplication. -/
theorem paper_far_lp_cutoff_smul
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (c : ℝ) (f : Lp ℝ (2 : ENNReal) μ) :
    paperFarLpCutoff μ far hfar (c • f) =
      c • paperFarLpCutoff μ far hfar f := by
  apply Lp.ext
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ far hfar (c • f),
       paper_far_lp_cutoff_coeFn μ far hfar f,
       Lp.coeFn_smul c f,
       Lp.coeFn_smul c (paperFarLpCutoff μ far hfar f)]
    with x hleft hright harg hout
  rw [hleft, hout]
  simp only [Pi.smul_apply]
  rw [hright]
  by_cases hx : x ∈ far
  · simpa only [Set.indicator_of_mem hx, Pi.smul_apply] using harg
  · simp only [Set.indicator_of_notMem hx, smul_zero]

/-- Idempotence survives passage to equivalence classes. -/
theorem paper_far_lp_cutoff_idempotent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    paperFarLpCutoff μ far hfar (paperFarLpCutoff μ far hfar f) =
      paperFarLpCutoff μ far hfar f := by
  apply Lp.ext
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ far hfar
         (paperFarLpCutoff μ far hfar f),
       paper_far_lp_cutoff_coeFn μ far hfar f]
    with x hleft hright
  rw [hleft, hright]
  by_cases hx : x ∈ far
  · simp [Set.indicator_of_mem hx, hright]
  · simp [Set.indicator_of_notMem hx]

/-- Indicator multiplication as an L² linear map. -/
noncomputable def paperFarLpCutoffLinear
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far) :
    Lp ℝ (2 : ENNReal) μ →ₗ[ℝ] Lp ℝ (2 : ENNReal) μ where
  toFun := paperFarLpCutoff μ far hfar
  map_add' := paper_far_lp_cutoff_add μ far hfar
  map_smul' := paper_far_lp_cutoff_smul μ far hfar

/-- The actual continuous linear cutoff, with operator norm at most one. -/
noncomputable def paperFarLpProjection
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far) :
    Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ :=
  (paperFarLpCutoffLinear μ far hfar).mkContinuous 1 (by
    intro f
    change ‖paperFarLpCutoff μ far hfar f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using paper_far_lp_cutoff_norm_le μ far hfar f)

/-- The continuous linear map is exactly the indicator cutoff. -/
theorem paper_far_lp_projection_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    paperFarLpProjection μ far hfar f = paperFarLpCutoff μ far hfar f := by
  rfl

/-- The concrete L² cutoff is a projection: P(Pf)=Pf. -/
theorem paper_far_lp_projection_idempotent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    paperFarLpProjection μ far hfar (paperFarLpProjection μ far hfar f) =
      paperFarLpProjection μ far hfar f := by
  simpa only [paper_far_lp_projection_apply] using
    paper_far_lp_cutoff_idempotent μ far hfar f

/-- Explicit contraction certificate for the concrete projection. -/
theorem paper_far_lp_projection_norm_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : MeasurableSet far)
    (f : Lp ℝ (2 : ENNReal) μ) :
    ‖paperFarLpProjection μ far hfar f‖ ≤ ‖f‖ := by
  rw [paper_far_lp_projection_apply]
  exact paper_far_lp_cutoff_norm_le μ far hfar f

end ReservoirSeismicityControl
