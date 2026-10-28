import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDMaximalSemigroup20261027
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# Physical n_d-dimensional reservoir measure and smooth density transfer

The preceding maximal weak-gradient and A3 semigroup constructions accept an
arbitrary measure μ on a subtype Ω. This module fixes μ to the actual pullback
of an ambient reservoir measure on an open Ω ⊆ ℝ^{n_d}, proving the exact
measure/Bochner-L² transport and the smooth-test density transfer uniformly
in n_d. It uses the single manuscript restriction n_d ∈ {1,2,3}.

For actual smooth density the *standard interior approximation* of arbitrary
L² fields by compactly supported smooth functions is an explicit external
analytic result, not silently invented. Its applicability to the physical
ambient measure is to be checked using the domain/measure hypotheses.
No previously passing module or theorem statement is modified.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped ENNReal Distributions

variable {n_d : ℕ}

/-- Physical reservoir measure on the SUBTYPE of an open n_d-dimensional
region, obtained from the given ambient spatial measure. -/
noncomputable def pressureNDRestrictedMeasure
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d)) :
    Measure (Ω : Set (Paper2026.PaperSpatial n_d)) :=
  ν.comap Subtype.val

/-- Exact mass of the restricted subtype. -/
theorem pressure_nd_restricted_measure_univ
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d)) :
    pressureNDRestrictedMeasure Ω ν Set.univ =
      ν (Ω : Set (Paper2026.PaperSpatial n_d)) := by
  unfold pressureNDRestrictedMeasure
  rw [comap_subtype_coe_apply Ω.isOpen.measurableSet]
  simp

/-- A bounded n_d-dimensional reservoir has finite physical L² measure
provided the ambient measure is finite on compact sets. -/
theorem pressure_nd_restricted_measure_finite
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set (Paper2026.PaperSpatial n_d))) :
    IsFiniteMeasure (pressureNDRestrictedMeasure Ω ν) := by
  refine ⟨?_⟩
  rw [pressure_nd_restricted_measure_univ]
  exact hΩ.measure_lt_top

/-- Embedding the reservoir subtype into ambient space pushes the physical
measure to the restriction of the ambient measure. -/
theorem pressure_nd_subtype_measure_preserving
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d)) :
    MeasurePreserving
      (Subtype.val : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) →
        Paper2026.PaperSpatial n_d)
      (pressureNDRestrictedMeasure Ω ν)
      (ν.restrict (Ω : Set (Paper2026.PaperSpatial n_d))) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  exact map_comap_subtype_coe Ω.isOpen.measurableSet ν

/-- The physical L² norm is unchanged when restricted ambient functions
are read on the reservoir subtype. -/
theorem pressure_nd_subtype_eLpNorm_eq
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Paper2026.PaperSpatial n_d → F)
    (hf : AEStronglyMeasurable f (ν.restrict (Ω : Set _))) :
    eLpNorm (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) => f x.val)
        2 (pressureNDRestrictedMeasure Ω ν) =
      eLpNorm f 2 (ν.restrict (Ω : Set _)) := by
  change eLpNorm (f ∘ (Subtype.val : ↥(Ω : Set _) → Paper2026.PaperSpatial n_d))
    2 (pressureNDRestrictedMeasure Ω ν) = _
  exact eLpNorm_comp_measurePreserving hf
    (pressure_nd_subtype_measure_preserving Ω ν)

/-- Extend an L² field by zero away from the reservoir. -/
noncomputable def pressureNDSubtypeZeroExtend
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F]
    (u : Lp F 2 (pressureNDRestrictedMeasure Ω ν)) :
    Paper2026.PaperSpatial n_d → F := by
  classical
  exact fun x =>
    if hx : x ∈ (Ω : Set (Paper2026.PaperSpatial n_d)) then
      (u ⟨x, hx⟩ : F)
    else 0

@[simp]
theorem pressure_nd_subtype_zero_extend_apply
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F]
    (u : Lp F 2 (pressureNDRestrictedMeasure Ω ν))
    (x : ↥(Ω : Set (Paper2026.PaperSpatial n_d))) :
    pressureNDSubtypeZeroExtend Ω ν F u x.val = u x := by
  simp [pressureNDSubtypeZeroExtend, x.property]

/-- Zero extension gives an actual L² representative for the ambient
restricted measure in every spatial dimension. -/
theorem pressure_nd_subtype_zero_extend_memLp
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F 2 (pressureNDRestrictedMeasure Ω ν)) :
    MemLp (pressureNDSubtypeZeroExtend Ω ν F u) 2
      (ν.restrict (Ω : Set _)) := by
  let μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)) :=
    pressureNDRestrictedMeasure Ω ν
  let f : Paper2026.PaperSpatial n_d → F :=
    pressureNDSubtypeZeroExtend Ω ν F u
  have hfun : (f ∘ (Subtype.val : ↥(Ω : Set _) → Paper2026.PaperSpatial n_d)) =
      (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) => (u x : F)) := by
    funext x
    exact pressure_nd_subtype_zero_extend_apply Ω ν F u x
  have hEmb : MeasurableEmbedding
      (Subtype.val : ↥(Ω : Set _) → Paper2026.PaperSpatial n_d) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hmap : μ.map
      (Subtype.val : ↥(Ω : Set _) → Paper2026.PaperSpatial n_d) =
      ν.restrict (Ω : Set _) :=
    map_comap_subtype_coe Ω.isOpen.measurableSet ν
  have hAS : AEStronglyMeasurable f (ν.restrict (Ω : Set _)) := by
    rw [← hmap]
    exact hEmb.aestronglyMeasurable_map_iff.mpr (by
      rw [hfun]
      exact Lp.aestronglyMeasurable u)
  change eLpNorm f 2 (ν.restrict (Ω : Set _)) < ∞
  rw [← eLpNorm_comp_measurePreserving hAS
    (pressure_nd_subtype_measure_preserving Ω ν), hfun]
  exact Lp.memLp u

/-- Turn the STANDARD interior smooth approximation on the ambient measure
into an approximation on the actual physical reservoir subtype.
No independent subtype density premise is required. -/
theorem pressure_nd_subtype_smooth_approx_of_ambient
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hAmbientApprox : ∀ (f : Paper2026.PaperSpatial n_d → F),
      MemLp f 2 (ν.restrict (Ω : Set _)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ φ : TestFunction Ω F ⊤,
          eLpNorm (f - (φ : Paper2026.PaperSpatial n_d → F)) 2
            (ν.restrict (Ω : Set _)) ≤ ENNReal.ofReal ε)
    (u : Lp F 2 (pressureNDRestrictedMeasure Ω ν))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : TestFunction Ω F ⊤,
      eLpNorm (fun x : ↥(Ω : Set _) => u x - φ x.val) 2
        (pressureNDRestrictedMeasure Ω ν) ≤ ENNReal.ofReal ε := by
  let f : Paper2026.PaperSpatial n_d → F :=
    pressureNDSubtypeZeroExtend Ω ν F u
  have hf : MemLp f 2 (ν.restrict (Ω : Set _)) :=
    pressure_nd_subtype_zero_extend_memLp Ω ν F u
  obtain ⟨φ, happrox⟩ := hAmbientApprox f hf hε
  refine ⟨φ, ?_⟩
  have hAS : AEStronglyMeasurable
      (f - (φ : Paper2026.PaperSpatial n_d → F))
      (ν.restrict (Ω : Set _)) :=
    hf.aestronglyMeasurable.sub φ.contDiff.continuous.aestronglyMeasurable
  have hfun : (fun x : ↥(Ω : Set _) => u x - φ x.val) =
      (f - (φ : Paper2026.PaperSpatial n_d → F)) ∘ Subtype.val := by
    funext x
    change u x - φ x.val =
      pressureNDSubtypeZeroExtend Ω ν F u x.val - φ x.val
    rw [pressure_nd_subtype_zero_extend_apply Ω ν F u x]
  rw [hfun, eLpNorm_comp_measurePreserving hAS
    (pressure_nd_subtype_measure_preserving Ω ν)]
  exact happrox

/-- A genuine smooth L² test map is dense whenever the standard interior
approximation theorem applies. Unlike the earlier Neumann semigroup lemma,
this takes no abstract `DenseRange` hypothesis. -/
theorem pressure_nd_smooth_L2_dense_of_subtype_approx
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (μ : Measure (Ω : Set (Paper2026.PaperSpatial n_d)))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E : TestFunction Ω F ⊤ → Lp F 2 μ)
    (hRep : ∀ φ : TestFunction Ω F ⊤,
      ∀ᵐ x ∂μ, (E φ x : F) = φ x.val)
    (hApprox : ∀ (u : Lp F 2 μ) {ε : ℝ}, 0 < ε →
      ∃ φ : TestFunction Ω F ⊤,
        eLpNorm (fun x : ↥(Ω : Set _) => u x - φ x.val)
          2 μ ≤ ENNReal.ofReal ε) :
    DenseRange E := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  obtain ⟨φ, hφ⟩ := hApprox u (half_pos hε)
  refine ⟨φ, ?_⟩
  have hPoint :
      (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) =>
        (u x : F) - ((E φ : Lp F 2 μ) x : F)) =ᵐ[μ]
      (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) =>
        (u x : F) - φ x.val) := by
    filter_upwards [hRep φ] with x hx
    rw [hx]
  have hNorm :
      eLpNorm (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) =>
        (u x : F) - ((E φ : Lp F 2 μ) x : F)) 2 μ =
        eLpNorm (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) =>
          (u x : F) - φ x.val) 2 μ := by
    exact eLpNorm_congr_ae hPoint
  rw [Lp.dist_def]
  change (eLpNorm (fun x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) =>
    (u x : F) - ((E φ : Lp F 2 μ) x : F)) 2 μ).toReal < ε
  rw [hNorm]
  calc
    (eLpNorm (fun x : ↥(Ω : Set _) => u x - φ x.val) 2 μ).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono (by simp) hφ
    _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
    _ < ε := half_lt_self hε

/-- Physical smooth-test density with ONLY ambient approximation and correct
L² representatives as inputs. This applies with F = ℝ (scalar tests) and
F = EuclideanSpace ℝ (Fin n_d) (vector tests). -/
theorem pressure_nd_physical_smooth_tests_dense
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (ν : Measure (Paper2026.PaperSpatial n_d))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E : TestFunction Ω F ⊤ →
        Lp F 2 (pressureNDRestrictedMeasure Ω ν))
    (hRep : ∀ φ : TestFunction Ω F ⊤,
      ∀ᵐ x ∂(pressureNDRestrictedMeasure Ω ν), (E φ x : F) = φ x.val)
    (hAmbientApprox : ∀ (f : Paper2026.PaperSpatial n_d → F),
      MemLp f 2 (ν.restrict (Ω : Set _)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ φ : TestFunction Ω F ⊤,
          eLpNorm (f - (φ : Paper2026.PaperSpatial n_d → F)) 2
            (ν.restrict (Ω : Set _)) ≤ ENNReal.ofReal ε) :
    DenseRange E := by
  exact pressure_nd_smooth_L2_dense_of_subtype_approx Ω
    (pressureNDRestrictedMeasure Ω ν) F E hRep
    (pressure_nd_subtype_smooth_approx_of_ambient Ω ν F hAmbientApprox)

end ReservoirSeismicityControl
