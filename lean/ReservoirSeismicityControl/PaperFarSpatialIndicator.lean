import ReservoirSeismicityControl.PaperFarProjectedNeumannBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stage 67 — Concrete spatial localization for far-field observations

Appendix A.3 uses a spatial cutoff to separate the observation weight
from well sources. Stage 66 used an abstract self-adjoint localization
operator on a Hilbert space. This file constructs its underlying
*measurable function* localization by an indicator of the far region.

Proved here:
* The cutoff is idempotent.
* It is symmetric in the real integral pairing.
* It vanishes on a disjoint well support; disjoint cutoffs are orthogonal.
* It preserves the L² condition and is contractive in the L² seminorm.

These are properties of spatial indicator localization, not yet the
construction of a continuous linear projection on the quotient L² space.
The latter operator-level bridge, construction of the actual analytic
Neumann semigroup, and its Davies--Gaffney derivative estimates remain
separate PDE formalization obligations. No bound on Q' or Q'' is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Restrict a real-valued spatial function to a measurable far region.
Outside the region, the result is zero. -/
noncomputable def paperFarSpatialCutoff
    {Ω : Type*} (far : Set Ω) (f : Ω → ℝ) : Ω → ℝ :=
  far.indicator f

/-- Applying the far cutoff twice has the same effect as applying it once. -/
theorem paper_far_spatial_cutoff_idempotent
    {Ω : Type*} (far : Set Ω) (f : Ω → ℝ) :
    paperFarSpatialCutoff far (paperFarSpatialCutoff far f) =
      paperFarSpatialCutoff far f := by
  classical
  funext x
  by_cases hx : x ∈ far
  · simp [paperFarSpatialCutoff, Set.indicator_of_mem hx]
  · simp [paperFarSpatialCutoff, Set.indicator_of_notMem hx]

/-- Pointwise symmetry of multiplication by the far-region indicator. -/
theorem paper_far_spatial_cutoff_pairing_pointwise
    {Ω : Type*} (far : Set Ω) (f g : Ω → ℝ) (x : Ω) :
    paperFarSpatialCutoff far f x * g x =
      f x * paperFarSpatialCutoff far g x := by
  classical
  by_cases hx : x ∈ far
  · simp [paperFarSpatialCutoff, Set.indicator_of_mem hx]
  · simp [paperFarSpatialCutoff, Set.indicator_of_notMem hx]

/-- Self-adjointness in the real integral pairing. This identity uses
only equality of the integrands, so no extra integrability premise is
needed for the equality under the standard Bochner integral convention. -/
theorem paper_far_spatial_cutoff_pairing
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (f g : Ω → ℝ) :
    (∫ x, paperFarSpatialCutoff far f x * g x ∂μ) =
      (∫ x, f x * paperFarSpatialCutoff far g x ∂μ) := by
  have hfun :
      (fun x : Ω => paperFarSpatialCutoff far f x * g x) =
        (fun x : Ω => f x * paperFarSpatialCutoff far g x) := by
    funext x
    exact paper_far_spatial_cutoff_pairing_pointwise far f g x
  exact congrArg (fun h : Ω → ℝ => ∫ x, h x ∂μ) hfun

/-- The far-region cutoff annihilates a function at every well point,
provided the well region is disjoint from the far region. -/
theorem paper_far_spatial_cutoff_zero_on_well
    {Ω : Type*} (far well : Set Ω) (hdisj : Disjoint far well)
    (f : Ω → ℝ) (x : Ω) (hx : x ∈ well) :
    paperFarSpatialCutoff far f x = 0 := by
  classical
  have hn : x ∉ far := by
    intro hfar
    exact Set.disjoint_left.mp hdisj hfar hx
  simp [paperFarSpatialCutoff, Set.indicator_of_notMem hn]

/-- Disjoint spatial cutoffs have zero integral pairing. In particular,
well-supported forcing and a far-supported observation do not overlap. -/
theorem paper_far_spatial_cutoff_disjoint_pairing
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far well : Set Ω) (hdisj : Disjoint far well)
    (f g : Ω → ℝ) :
    (∫ x, paperFarSpatialCutoff far f x *
      paperFarSpatialCutoff well g x ∂μ) = 0 := by
  classical
  have hzero :
      (fun x : Ω => paperFarSpatialCutoff far f x *
        paperFarSpatialCutoff well g x) =
        (fun _ : Ω => (0 : ℝ)) := by
    funext x
    by_cases hx : x ∈ far
    · have hn : x ∉ well := by
        intro hw
        exact Set.disjoint_left.mp hdisj hx hw
      simp [paperFarSpatialCutoff,
        Set.indicator_of_mem hx, Set.indicator_of_notMem hn]
    · simp [paperFarSpatialCutoff, Set.indicator_of_notMem hx]
  simp only [hzero, integral_zero]

/-- An indicator cutoff cannot increase the L² seminorm of a spatial
function. This is the function-level counterpart of the contraction
needed when constructing the Stage 66 Hilbert-space projection. -/
theorem paper_far_spatial_cutoff_eLpNorm_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : NullMeasurableSet far μ)
    (f : Ω → ℝ) :
    eLpNorm (paperFarSpatialCutoff far f) (2 : ENNReal) μ ≤
      eLpNorm f (2 : ENNReal) μ := by
  change eLpNorm (far.indicator f) (2 : ENNReal) μ ≤
    eLpNorm f (2 : ENNReal) μ
  exact MeasureTheory.eLpNorm_indicator_le f hfar

/-- Spatial restriction of an L² function remains in L². -/
theorem paper_far_spatial_cutoff_memLp
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (far : Set Ω) (hfar : NullMeasurableSet far μ)
    (f : Ω → ℝ) (hf : MemLp f (2 : ENNReal) μ) :
    MemLp (paperFarSpatialCutoff far f) (2 : ENNReal) μ := by
  change MemLp (far.indicator f) (2 : ENNReal) μ
  exact MeasureTheory.MemLp.indicator hfar hf

end ReservoirSeismicityControl
