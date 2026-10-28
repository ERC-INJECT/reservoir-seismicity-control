import ReservoirSeismicityControl.PressureNeumann3DSmoothLocalization
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compact interior cutoff functions on a bounded three-dimensional reservoir

For every compact K contained in a bounded open reservoir Ω, produce an
actual smooth, compactly supported test function ψ in Ω such that
0 ≤ ψ ≤ 1 everywhere and ψ = 1 on K.  In particular, its topological
support is a positive distance from the complement of Ω locally, since
that support lies inside Ω and is compact.

This uses only the established smooth Urysohn lemma and the shrinking of
neighborhoods of compact sets in a metric space. No analytic density or
integration-by-parts assumption is introduced.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace Set Filter
open scoped Distributions Topology

variable (Ω : Opens pressureNeumannE3)

/-- A single interior test function equal to one on any prescribed compact
subset of a bounded open reservoir. Its support is strictly inside Ω. -/
theorem pressure_neumann_3d_exists_compact_interior_cutoff
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set pressureNeumannE3)) :
    ∃ ψ : pressureNeumann3DSmoothScalarTests Ω,
      (∀ x ∈ K, ψ x = 1) ∧
      (∀ x : pressureNeumannE3, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      tsupport (ψ : pressureNeumannE3 → ℝ) ⊆ (Ω : Set pressureNeumannE3) := by
  obtain ⟨V, hVopen, hKV, hVΩ⟩ :=
    hK.exists_isOpen_closure_subset (Ω.isOpen.mem_nhdsSet.mpr hKΩ)
  obtain ⟨f, hfSmooth, hfRange, hfSupport, hfOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      hVopen hK.isClosed hKV
  have hClosedVcompact : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hΩ.subset hVΩ)
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hClosedVcompact
    rw [hfSupport]
    exact subset_closure
  have hfInside : tsupport f ⊆ (Ω : Set pressureNeumannE3) := by
    change closure (Function.support f) ⊆ (Ω : Set pressureNeumannE3)
    simpa only [hfSupport] using hVΩ
  let ψ : pressureNeumann3DSmoothScalarTests Ω :=
    ⟨f, hfSmooth, hfCompact, hfInside⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    exact (hfOne x).mp hx
  · intro x
    exact hfRange (mem_range_self x)
  · exact hfInside

/-- Compact localization leaves a smooth ambient scalar function unchanged
at every point of the chosen compact subset. -/
theorem pressure_neumann_3d_compact_localization_scalar
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set pressureNeumannE3))
    (f : pressureNeumannE3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∃ g : pressureNeumann3DSmoothScalarTests Ω,
      ∀ x ∈ K, g x = f x := by
  obtain ⟨ψ, hψ, _, _⟩ :=
    pressure_neumann_3d_exists_compact_interior_cutoff Ω hΩ K hK hKΩ
  refine ⟨pressureNeumann3DLocalizeScalar Ω ψ f hf, ?_⟩
  intro x hx
  rw [pressure_neumann_3d_localize_scalar_apply, hψ x hx, one_mul]

/-- Compact localization leaves a smooth ambient vector field unchanged
at every point of the chosen compact subset. -/
theorem pressure_neumann_3d_compact_localization_vector
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set pressureNeumannE3))
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∃ g : pressureNeumann3DSmoothVectorTests Ω,
      ∀ x ∈ K, g x = f x := by
  obtain ⟨ψ, hψ, _, _⟩ :=
    pressure_neumann_3d_exists_compact_interior_cutoff Ω hΩ K hK hKΩ
  refine ⟨pressureNeumann3DLocalizeVector Ω ψ f hf, ?_⟩
  intro x hx
  rw [pressure_neumann_3d_localize_vector_apply, hψ x hx, one_smul]

end ReservoirSeismicityControl
