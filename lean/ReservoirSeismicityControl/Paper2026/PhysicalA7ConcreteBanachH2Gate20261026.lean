import ReservoirSeismicityControl.Paper2026.PhysicalA7ConcreteTestBridge20261026
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic

/-!
# A7: the actual complete spatial weak-H² graph (not an arbitrary Banach space)

The physical near-well Sobolev class is realized as a CLOSED SUBSPACE of the
complete 13-component L² jet space. Every weak identity is checked against
actual compactly supported smooth tests and their coordinate derivatives.
Completeness and the canonical continuous embedding into L² are inherited
from the closed-submodule construction, rather than assumed as hypotheses.

This replaces the arbitrary Banach space `H` in the earlier A7 closure.
It does not claim nonlinear multiplication/exponential/positive-inversion
calculus, factor mollification from A3, or scalar/Bochner Fubini: these are
separate genuine remaining physical dependencies, not assumptions on R.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence
open scoped InnerProductSpace

private abbrev Spatial3 := Fin 3 → ℝ
private abbrev LocalL2 (U : Set Spatial3) := PhysicalThreeL2 U

/-- Value + three first derivatives + nine mixed second derivatives. -/
abbrev A7PhysicalJet (U : Set Spatial3) :=
  LocalL2 U × (Fin 3 → LocalL2 U) × (Fin 3 → Fin 3 → LocalL2 U)

/-- The first distributional residual vanishes precisely when the physical
coordinate integration-by-parts identity holds. -/
private noncomputable def a7FirstResidual
    (U : Set Spatial3) (i : Fin 3) (φ : A7SmoothCompactTest U) :
    A7PhysicalJet U →L[ℝ] ℝ where
  toFun := fun z =>
    (innerSL ℝ (a7TestDerivativeL2 U i φ)) z.1 +
      (innerSL ℝ (a7TestL2 U φ)) (z.2.1 i)
  map_add' := by
    intro x y
    change (innerSL ℝ (a7TestDerivativeL2 U i φ)) (x.1 + y.1) +
        (innerSL ℝ (a7TestL2 U φ)) (x.2.1 i + y.2.1 i) =
        ((innerSL ℝ (a7TestDerivativeL2 U i φ)) x.1 +
          (innerSL ℝ (a7TestL2 U φ)) (x.2.1 i)) +
        ((innerSL ℝ (a7TestDerivativeL2 U i φ)) y.1 +
          (innerSL ℝ (a7TestL2 U φ)) (y.2.1 i))
    simp only [map_add]
    ring
  map_smul' := by
    intro c x
    change (innerSL ℝ (a7TestDerivativeL2 U i φ)) (c • x.1) +
        (innerSL ℝ (a7TestL2 U φ)) (c • x.2.1 i) =
        c • ((innerSL ℝ (a7TestDerivativeL2 U i φ)) x.1 +
          (innerSL ℝ (a7TestL2 U φ)) (x.2.1 i))
    simp only [map_smul, smul_eq_mul]
    ring
  cont := by
    have h0 : Continuous (fun z : A7PhysicalJet U => z.1) := by fun_prop
    have h1 : Continuous (fun z : A7PhysicalJet U => z.2.1 i) := by fun_prop
    exact ((innerSL ℝ (a7TestDerivativeL2 U i φ)).continuous.comp h0).add
      ((innerSL ℝ (a7TestL2 U φ)).continuous.comp h1)

/-- The second distributional residual is also a continuous linear map. -/
private noncomputable def a7SecondResidual
    (U : Set Spatial3) (i j : Fin 3) (φ : A7SmoothCompactTest U) :
    A7PhysicalJet U →L[ℝ] ℝ where
  toFun := fun z =>
    (innerSL ℝ (a7TestDerivativeL2 U j φ)) (z.2.1 i) +
      (innerSL ℝ (a7TestL2 U φ)) (z.2.2 i j)
  map_add' := by
    intro x y
    change (innerSL ℝ (a7TestDerivativeL2 U j φ))
          (x.2.1 i + y.2.1 i) +
        (innerSL ℝ (a7TestL2 U φ)) (x.2.2 i j + y.2.2 i j) =
        ((innerSL ℝ (a7TestDerivativeL2 U j φ)) (x.2.1 i) +
          (innerSL ℝ (a7TestL2 U φ)) (x.2.2 i j)) +
        ((innerSL ℝ (a7TestDerivativeL2 U j φ)) (y.2.1 i) +
          (innerSL ℝ (a7TestL2 U φ)) (y.2.2 i j))
    simp only [map_add]
    ring
  map_smul' := by
    intro c x
    change (innerSL ℝ (a7TestDerivativeL2 U j φ)) (c • x.2.1 i) +
        (innerSL ℝ (a7TestL2 U φ)) (c • x.2.2 i j) =
        c • ((innerSL ℝ (a7TestDerivativeL2 U j φ)) (x.2.1 i) +
          (innerSL ℝ (a7TestL2 U φ)) (x.2.2 i j))
    simp only [map_smul, smul_eq_mul]
    ring
  cont := by
    have h1 : Continuous (fun z : A7PhysicalJet U => z.2.1 i) := by fun_prop
    have h2 : Continuous (fun z : A7PhysicalJet U => z.2.2 i j) := by fun_prop
    exact ((innerSL ℝ (a7TestDerivativeL2 U j φ)).continuous.comp h1).add
      ((innerSL ℝ (a7TestL2 U φ)).continuous.comp h2)

/-- Every physical C∞ compact-support weak constraint is a CLOSED kernel.
Their joint intersection is a genuine closed linear subspace, with no
external assumption of completeness or a separately postulated norm. -/
noncomputable def a7PhysicalH2ClosedSubspace (U : Set Spatial3) :
    ClosedSubmodule ℝ (A7PhysicalJet U) :=
  (⨅ (i : Fin 3), ⨅ (φ : A7SmoothCompactTest U),
      ClosedSubmodule.comap (a7FirstResidual U i φ) (⊥ : ClosedSubmodule ℝ ℝ)) ⊓
  (⨅ (i : Fin 3), ⨅ (j : Fin 3), ⨅ (φ : A7SmoothCompactTest U),
      ClosedSubmodule.comap (a7SecondResidual U i j φ) (⊥ : ClosedSubmodule ℝ ℝ))

/-- The *concrete* spatial H² graph is a Banach space. It carries the
norm induced by the complete L² product of its thirteen weak-derivative
components. `CompleteSpace` and `NormedSpace` are inherited instances. -/
abbrev A7PhysicalH2 (U : Set Spatial3) := ↥(a7PhysicalH2ClosedSubspace U)

/-- A field belongs to the genuine closed Sobolev graph if and only if the
three + nine weak identities hold for every concrete compact test. -/
theorem a7_mem_physical_H2_iff (U : Set Spatial3)
    (z : A7PhysicalJet U) :
    z ∈ a7PhysicalH2ClosedSubspace U ↔
      (∀ i (φ : A7SmoothCompactTest U),
        (innerSL ℝ (a7TestDerivativeL2 U i φ)) z.1 =
          -(innerSL ℝ (a7TestL2 U φ)) (z.2.1 i)) ∧
      (∀ i j (φ : A7SmoothCompactTest U),
        (innerSL ℝ (a7TestDerivativeL2 U j φ)) (z.2.1 i) =
          -(innerSL ℝ (a7TestL2 U φ)) (z.2.2 i j)) := by
  simp only [a7PhysicalH2ClosedSubspace, ClosedSubmodule.mem_inf,
    ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro i φ
      have h := h1 i φ
      dsimp [a7FirstResidual] at h
      exact (eq_neg_iff_add_eq_zero).2 h
    · intro i j φ
      have h := h2 i j φ
      dsimp [a7SecondResidual] at h
      exact (eq_neg_iff_add_eq_zero).2 h
  · rintro ⟨h1, h2⟩
    constructor
    · intro i φ
      change (innerSL ℝ (a7TestDerivativeL2 U i φ)) z.1 +
        (innerSL ℝ (a7TestL2 U φ)) (z.2.1 i) = 0
      rw [h1 i φ]
      ring
    · intro i j φ
      change (innerSL ℝ (a7TestDerivativeL2 U j φ)) (z.2.1 i) +
        (innerSL ℝ (a7TestL2 U φ)) (z.2.2 i j) = 0
      rw [h2 i j φ]
      ring

/-- Convert the previously proved actual A3 weak product/primitive to an
element of a complete concrete H² Banach space, without adding any weak
derivative premises. -/
noncomputable def a7ConcreteWeakToBanach (U : Set Spatial3)
    (A : A7ConcreteWeakH2 U) : A7PhysicalH2 U := by
  refine ⟨(A.value, A.first, A.second), ?_⟩
  apply (a7_mem_physical_H2_iff U _).2
  exact a7_concrete_weak_derivative_identities U A

/-- The canonical *continuous linear* embedding into the actual local L².
Injectivity requires the usual uniqueness of distributional derivatives;
that standard Sobolev result is not proved in this module. -/
noncomputable def a7PhysicalH2Embedding (U : Set Spatial3) :
    A7PhysicalH2 U →L[ℝ] LocalL2 U :=
  (ContinuousLinearMap.fst ℝ (LocalL2 U)
    ((Fin 3 → LocalL2 U) × (Fin 3 → Fin 3 → LocalL2 U))).comp
    (Submodule.subtypeL (a7PhysicalH2ClosedSubspace U).toSubmodule)

theorem a7PhysicalH2Embedding_of_weak (U : Set Spatial3)
    (A : A7ConcreteWeakH2 U) :
    a7PhysicalH2Embedding U (a7ConcreteWeakToBanach U A) = A.value := by
  rfl

/-- Canonical L² embedding is norm-nonincreasing for the inherited
13-component product norm. This is NOT an independent embedding assumption. -/
theorem a7PhysicalH2Embedding_norm_le (U : Set Spatial3)
    (A : A7PhysicalH2 U) :
    ‖a7PhysicalH2Embedding U A‖ ≤ ‖A‖ := by
  change ‖(A : A7PhysicalJet U).1‖ ≤ ‖(A : A7PhysicalJet U)‖
  exact norm_fst_le (A : A7PhysicalJet U)

/-- The new physical H² space is complete, via closedness of all real
compact-test distributional constraints, not by hypothesis. -/
theorem a7PhysicalH2_is_complete (U : Set Spatial3) :
    CompleteSpace (A7PhysicalH2 U) := inferInstance

#print axioms a7_mem_physical_H2_iff
#print axioms a7PhysicalH2Embedding_of_weak
#print axioms a7PhysicalH2Embedding_norm_le

end ReservoirSeismicityControl.Paper2026
