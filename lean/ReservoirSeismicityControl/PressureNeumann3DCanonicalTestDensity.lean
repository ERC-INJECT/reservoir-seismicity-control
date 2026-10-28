import ReservoirSeismicityControl.PressureNeumann3DSubtypeDensityTransfer
import ReservoirSeismicityControl.PressureNeumann3DCanonicalDensityReduction

/-!
# Density of canonical smooth tests in the physical reservoir L² spaces

The previous quantitative approximation result has already established that
an arbitrary L² field on the reservoir subtype is approximated by smooth
test fields with support compactly contained in Ω. Here we turn that
quantitative statement into Mathlib's `DenseRange` for the canonical
L² embedding (not for an abstract or assumed embedding).

No density hypotheses are introduced. The ambient measure is required
to be finite on compact sets and inner regular, and Ω to be bounded.

This closes the *vector-test* density obligation from the analytic core.
Density of the maximal weak-pressure domain remains separate.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions ENNReal

/-- Quantitative L² approximation of smooth tests implies dense range of
    their canonical embedding. This helper is independent of the reservoir
    measure's particular construction. -/
theorem pressure_neumann_3d_smooth_L2_dense_of_approx
    (Ω : Opens pressureNeumannE3)
    (μ : Measure ↥(Ω : Set pressureNeumannE3))
    [IsFiniteMeasure μ]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hApprox : ∀ (u : Lp F 2 μ) {ε : ℝ}, 0 < ε →
      ∃ φ : TestFunction Ω F ⊤,
        eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val)
          2 μ ≤ ENNReal.ofReal ε) :
    DenseRange (pressureNeumann3DSmoothToL2CLM Ω μ F :
      TestFunction Ω F ⊤ → Lp F 2 μ) := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  obtain ⟨φ, hφ⟩ := hApprox u (half_pos hε)
  refine ⟨φ, ?_⟩
  have hAE := pressure_neumann_3d_smooth_toL2_ae Ω μ F φ
  have hPoint :
      (fun x : ↥(Ω : Set pressureNeumannE3) =>
        u x - (pressureNeumann3DSmoothToL2CLM Ω μ F φ : Lp F 2 μ) x)
        =ᵐ[μ]
      (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val) := by
    filter_upwards [hAE] with x hx
    rw [hx]
  have hNorm :
      eLpNorm
        ((u : ↥(Ω : Set pressureNeumannE3) → F) -
          ((pressureNeumann3DSmoothToL2CLM Ω μ F φ : Lp F 2 μ) :
            ↥(Ω : Set pressureNeumannE3) → F)) 2 μ =
        eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val) 2 μ := by
    apply eLpNorm_congr_ae
    exact hPoint
  rw [Lp.dist_def, hNorm]
  calc
    (eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => u x - φ x.val) 2 μ).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_mono (by simp) hφ
    _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
    _ < ε := half_lt_self hε

/-- The canonical vector test function embedding on a bounded 3D reservoir
    is dense in the subtype vector L² space. -/
theorem pressure_neumann_3d_canonical_vector_tests_dense
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    DenseRange (pressureNeumann3DRestrictedVectorL2Embed Ω ν hΩ :
      pressureNeumann3DSmoothVectorTests Ω →
        pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
          (pressureNeumann3DRestrictedMeasure Ω ν)) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  change DenseRange
    (pressureNeumann3DSmoothToL2CLM Ω
      (pressureNeumann3DRestrictedMeasure Ω ν) pressureNeumannE3 :
        pressureNeumann3DSmoothVectorTests Ω →
          pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
            (pressureNeumann3DRestrictedMeasure Ω ν))
  apply pressure_neumann_3d_smooth_L2_dense_of_approx
  intro u ε hε
  exact pressure_neumann_3d_subtype_interior_vector_approx Ω ν hΩ u hε

/-- The scalar test embedding on the restricted subtype measure.
    Defining it separately makes the finite-measure instance available
    when the embedding is constructed, before a density theorem is stated. -/
noncomputable def pressureNeumann3DRestrictedScalarL2Embed
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    pressureNeumann3DSmoothScalarTests Ω →L[ℝ]
      pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω ν) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  exact pressureNeumann3DSmoothToL2CLM Ω
    (pressureNeumann3DRestrictedMeasure Ω ν) ℝ

/-- The canonical smooth scalar test embedding is likewise dense in scalar
    L² of the reservoir subtype. This does NOT by itself prove weak-H¹
    density, which also requires embedding smooth scalar tests into the
    maximal weak-gradient domain. -/
theorem pressure_neumann_3d_canonical_scalar_tests_dense
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3)) :
    DenseRange (pressureNeumann3DRestrictedScalarL2Embed Ω ν hΩ :
      pressureNeumann3DSmoothScalarTests Ω →
        pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
          (pressureNeumann3DRestrictedMeasure Ω ν)) := by
  letI := pressure_neumann_3d_restricted_measure_finite Ω ν hΩ
  change DenseRange (pressureNeumann3DSmoothToL2CLM Ω
    (pressureNeumann3DRestrictedMeasure Ω ν) ℝ :
      pressureNeumann3DSmoothScalarTests Ω →
        pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3)
          (pressureNeumann3DRestrictedMeasure Ω ν))
  apply pressure_neumann_3d_smooth_L2_dense_of_approx
  intro u ε hε
  exact pressure_neumann_3d_subtype_interior_scalar_approx Ω ν hΩ u hε

end ReservoirSeismicityControl
