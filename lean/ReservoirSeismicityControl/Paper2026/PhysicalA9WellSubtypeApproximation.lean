import ReservoirSeismicityControl.Paper2026.PhysicalA9SupportedWellApproximation
import ReservoirSeismicityControl.PressureNeumann3DSubtypeDensityTransfer
import Mathlib.Tactic

/-!
Appendix A.3 (A9): transfer the ALREADY PROVED, geometry-preserving
3D well approximation from the ambient restricted L² norm to the
ACTUAL reservoir-subtype L² norm.

The previous module constructs smooth functions supported in the near
collar U and estimates their centered error on (volume.restrict Ω).
The physical Neumann semigroup uses L² on the subtype Ω, not ambient L².
We use the existing exact equality of these two eLp norms, and carry
through the support of the approximation ERROR (not of f = B/β - const).

This theorem does NOT assert that the tests belong to D(A). That local
elliptic inclusion is a standard cited regularity result to be applied
separately; it is not an assumption hidden inside the theorem below.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal

/-- Reclassify a compactly supported smooth test in U as a compactly
supported smooth test in the larger reservoir Ω. The underlying function
and its spatial support do not change. -/
noncomputable def paperA9ExtendInteriorTest
    (Ω U : Opens pressureNeumannE3)
    (hUΩ : (U : Set pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3))
    (ψ : pressureNeumann3DSmoothScalarTests U) :
    pressureNeumann3DSmoothScalarTests Ω :=
  ⟨(ψ : pressureNeumannE3 → ℝ), ψ.contDiff, ψ.hasCompactSupport,
    ψ.tsupport_subset.trans hUΩ⟩

@[simp] theorem paperA9ExtendInteriorTest_apply
    (Ω U : Opens pressureNeumannE3)
    (hUΩ : (U : Set pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3))
    (ψ : pressureNeumann3DSmoothScalarTests U)
    (x : pressureNeumannE3) :
    paperA9ExtendInteriorTest Ω U hUΩ ψ x = ψ x := rfl

/-- Exact localization after lifting the near test into the reservoir
smooth-test space. -/
theorem paperA9ExtendInteriorTest_tsupport
    (Ω U : Opens pressureNeumannE3)
    (hUΩ : (U : Set pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3))
    (ψ : pressureNeumann3DSmoothScalarTests U) :
    tsupport (paperA9ExtendInteriorTest Ω U hUΩ ψ :
      pressureNeumannE3 → ℝ) ⊆ (U : Set pressureNeumannE3) := by
  change tsupport (ψ : pressureNeumannE3 → ℝ) ⊆
    (U : Set pressureNeumannE3)
  exact ψ.tsupport_subset

/-- The approximants from the already compiled localized-well theorem
also approximate the centered physical forcing in the reservoir's L²
space (the space on which the Neumann semigroup acts). This is a new
physical-space identification, not another ambient density lemma.

In particular, the constant pressure-mean correction cancels *inside*
the error; this is why the support of the error is in U although the
centered forcing itself is not supported in U. -/
theorem paper_A9_physical_3d_centered_well_subtype_approximation
    (Ω U : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (hU : Bornology.IsBounded (U : Set pressureNeumannE3))
    (hUΩ : (U : Set pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKU : K ⊆ (U : Set pressureNeumannE3))
    (B : pressureNeumannE3 → ℝ)
    (hB : MemLp B 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    (hBsupport : Function.support B ⊆ K)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω,
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆
        (U : Set pressureNeumannE3) ∧
      eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        (B x.val - c) - ((φ : pressureNeumannE3 → ℝ) x.val - c)) 2
        (pressureNeumann3DRestrictedMeasure Ω ν) ≤ ENNReal.ofReal ε ∧
      Function.support (fun x : pressureNeumannE3 =>
        (B x - c) - ((φ : pressureNeumannE3 → ℝ) x - c)) ⊆
        (U : Set pressureNeumannE3) := by
  classical
  obtain ⟨ψ, hψSupport, hψNorm, hψError⟩ :=
    paper_A9_physical_3d_localized_centered_well_approximation
      Ω U ν hΩ hU K hK hKU B hB hBsupport c hε
  let φ : pressureNeumann3DSmoothScalarTests Ω :=
    paperA9ExtendInteriorTest Ω U hUΩ ψ
  let F : pressureNeumannE3 → ℝ :=
    fun x => (B x - c) - ((ψ : pressureNeumannE3 → ℝ) x - c)
  have hF : F = B - (ψ : pressureNeumannE3 → ℝ) := by
    funext x
    dsimp [F]
    ring
  have hAS : AEStronglyMeasurable F
      (ν.restrict (Ω : Set pressureNeumannE3)) := by
    rw [hF]
    exact hB.aestronglyMeasurable.sub
      ψ.contDiff.continuous.aestronglyMeasurable
  have hTransfer :
      eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => F x.val) 2
        (pressureNeumann3DRestrictedMeasure Ω ν) =
      eLpNorm F 2 (ν.restrict (Ω : Set pressureNeumannE3)) :=
    pressure_neumann_3d_subtype_eLpNorm_eq Ω ν ℝ F hAS
  refine ⟨φ, ?_, ?_, ?_⟩
  · exact paperA9ExtendInteriorTest_tsupport Ω U hUΩ ψ
  · change eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) => F x.val) 2
      (pressureNeumann3DRestrictedMeasure Ω ν) ≤ ENNReal.ofReal ε
    rw [hTransfer]
    exact hψNorm
  · change Function.support F ⊆ (U : Set pressureNeumannE3)
    exact hψError

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_3d_centered_well_subtype_approximation
