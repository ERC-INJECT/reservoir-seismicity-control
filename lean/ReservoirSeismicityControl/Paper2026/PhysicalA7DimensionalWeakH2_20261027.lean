import ReservoirSeismicityControl.Paper2026.SpatialDimensions20261027
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic

/-!
# Dimension-parametric concrete weak-H² graph for n_d in {1,2,3}

Generalizes the closed 1+3+9 L² jet *construction*, without modifying the
already passing 3D implementations. At n_d=d the graph has 1+d+d²
components, and is defined by actual weak integration-by-parts identities
against smooth compactly supported tests on U ⊆ (Fin d → ℝ).

This is the common analytic *space*, not a new proof of the A7 Y/R estimates:
those results are already dimension-abstract and require standard H²
composition, product and quotient results as agreed external inputs.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

private noncomputable abbrev LocalL2 (n_d : ℕ) (U : Set (PaperSpatial n_d)) :=
  Lp ℝ 2 (volume.restrict U)

/-- Standard coordinate direction, for arbitrary n_d. -/
noncomputable def paperCoordinateDirection {n_d : ℕ} (i : Fin n_d) :
    PaperSpatial n_d := fun j => if j = i then 1 else 0

/-- Genuine compactly supported smooth tests with their L² realizations. -/
structure A7DimensionalSmoothTest (n_d : ℕ)
    (U : Set (PaperSpatial n_d)) where
  field : PaperSpatial n_d → ℝ
  smooth : ContDiff ℝ ⊤ field
  compact_support : IsCompact (tsupport field)
  support_inside : tsupport field ⊆ U
  square_integrable : MemLp field (2 : ENNReal) (volume.restrict U)
  derivative_square_integrable : ∀ i : Fin n_d,
    MemLp (fun x => (fderiv ℝ field x) (paperCoordinateDirection i))
      (2 : ENNReal) (volume.restrict U)

noncomputable def a7DimensionalTestL2 (n_d : ℕ)
    (U : Set (PaperSpatial n_d))
    (φ : A7DimensionalSmoothTest n_d U) : LocalL2 n_d U :=
  φ.square_integrable.toLp

noncomputable def a7DimensionalTestDerivativeL2 (n_d : ℕ)
    (U : Set (PaperSpatial n_d)) (i : Fin n_d)
    (φ : A7DimensionalSmoothTest n_d U) : LocalL2 n_d U :=
  (φ.derivative_square_integrable i).toLp

/-- Value, n_d first derivatives and n_d² mixed derivatives. -/
abbrev A7DimensionalJet (n_d : ℕ) (U : Set (PaperSpatial n_d)) :=
  LocalL2 n_d U × (Fin n_d → LocalL2 n_d U) ×
    (Fin n_d → Fin n_d → LocalL2 n_d U)

private noncomputable def a7DimensionalFirstResidual
    (n_d : ℕ) (U : Set (PaperSpatial n_d))
    (i : Fin n_d) (φ : A7DimensionalSmoothTest n_d U) :
    A7DimensionalJet n_d U →L[ℝ] ℝ where
  toFun := fun z =>
    (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) z.1 +
      (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.1 i)
  map_add' := by
    intro x y
    change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) (x.1 + y.1) +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.1 i + y.2.1 i) =
        ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) x.1 +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.1 i)) +
        ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) y.1 +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (y.2.1 i))
    simp only [map_add]
    ring
  map_smul' := by
    intro c x
    change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) (c • x.1) +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (c • x.2.1 i) =
        c • ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) x.1 +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.1 i))
    simp only [map_smul, smul_eq_mul]
    ring
  cont := by
    have h0 : Continuous (fun z : A7DimensionalJet n_d U => z.1) := by fun_prop
    have h1 : Continuous (fun z : A7DimensionalJet n_d U => z.2.1 i) := by fun_prop
    exact ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)).continuous.comp h0).add
      ((innerSL ℝ (a7DimensionalTestL2 n_d U φ)).continuous.comp h1)

private noncomputable def a7DimensionalSecondResidual
    (n_d : ℕ) (U : Set (PaperSpatial n_d))
    (i j : Fin n_d) (φ : A7DimensionalSmoothTest n_d U) :
    A7DimensionalJet n_d U →L[ℝ] ℝ where
  toFun := fun z =>
    (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (z.2.1 i) +
      (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.2 i j)
  map_add' := by
    intro x y
    change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ))
          (x.2.1 i + y.2.1 i) +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.2 i j + y.2.2 i j) =
        ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (x.2.1 i) +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.2 i j)) +
        ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (y.2.1 i) +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (y.2.2 i j))
    simp only [map_add]
    ring
  map_smul' := by
    intro c x
    change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (c • x.2.1 i) +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (c • x.2.2 i j) =
        c • ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (x.2.1 i) +
          (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (x.2.2 i j))
    simp only [map_smul, smul_eq_mul]
    ring
  cont := by
    have h1 : Continuous (fun z : A7DimensionalJet n_d U => z.2.1 i) := by fun_prop
    have h2 : Continuous (fun z : A7DimensionalJet n_d U => z.2.2 i j) := by fun_prop
    exact ((innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)).continuous.comp h1).add
      ((innerSL ℝ (a7DimensionalTestL2 n_d U φ)).continuous.comp h2)

/-- Closed joint graph of the n_d + n_d² distributional constraints. -/
noncomputable def a7DimensionalH2ClosedSubspace
    (n_d : ℕ) (U : Set (PaperSpatial n_d)) :
    ClosedSubmodule ℝ (A7DimensionalJet n_d U) :=
  (⨅ (i : Fin n_d), ⨅ (φ : A7DimensionalSmoothTest n_d U),
      ClosedSubmodule.comap (a7DimensionalFirstResidual n_d U i φ)
        (⊥ : ClosedSubmodule ℝ ℝ)) ⊓
  (⨅ (i : Fin n_d), ⨅ (j : Fin n_d),
      ⨅ (φ : A7DimensionalSmoothTest n_d U),
      ClosedSubmodule.comap (a7DimensionalSecondResidual n_d U i j φ)
        (⊥ : ClosedSubmodule ℝ ℝ))

/-- Concrete H² graph, complete for every n_d (in particular 1,2,3). -/
abbrev A7DimensionalH2 (n_d : ℕ) (U : Set (PaperSpatial n_d)) :=
  ↥(a7DimensionalH2ClosedSubspace n_d U)

/-- Exact weak-derivative characterization of the graph. -/
theorem a7_dimensional_mem_H2_iff
    (n_d : ℕ) (U : Set (PaperSpatial n_d))
    (z : A7DimensionalJet n_d U) :
    z ∈ a7DimensionalH2ClosedSubspace n_d U ↔
      (∀ i (φ : A7DimensionalSmoothTest n_d U),
        (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) z.1 =
          -(innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.1 i)) ∧
      (∀ i j (φ : A7DimensionalSmoothTest n_d U),
        (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (z.2.1 i) =
          -(innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.2 i j)) := by
  simp only [a7DimensionalH2ClosedSubspace, ClosedSubmodule.mem_inf,
    ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro i φ
      have h := h1 i φ
      dsimp [a7DimensionalFirstResidual] at h
      exact (eq_neg_iff_add_eq_zero).2 h
    · intro i j φ
      have h := h2 i j φ
      dsimp [a7DimensionalSecondResidual] at h
      exact (eq_neg_iff_add_eq_zero).2 h
  · rintro ⟨h1, h2⟩
    constructor
    · intro i φ
      change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U i φ)) z.1 +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.1 i) = 0
      rw [h1 i φ]
      ring
    · intro i j φ
      change (innerSL ℝ (a7DimensionalTestDerivativeL2 n_d U j φ)) (z.2.1 i) +
        (innerSL ℝ (a7DimensionalTestL2 n_d U φ)) (z.2.2 i j) = 0
      rw [h2 i j φ]
      ring

/-- Projection from the actual H² graph into local L². -/
noncomputable def a7DimensionalH2Embedding
    (n_d : ℕ) (U : Set (PaperSpatial n_d)) :
    A7DimensionalH2 n_d U →L[ℝ] LocalL2 n_d U :=
  (ContinuousLinearMap.fst ℝ (LocalL2 n_d U)
    ((Fin n_d → LocalL2 n_d U) ×
      (Fin n_d → Fin n_d → LocalL2 n_d U))).comp
    (Submodule.subtypeL (a7DimensionalH2ClosedSubspace n_d U).toSubmodule)

theorem a7DimensionalH2Embedding_norm_le
    (n_d : ℕ) (U : Set (PaperSpatial n_d))
    (A : A7DimensionalH2 n_d U) :
    ‖a7DimensionalH2Embedding n_d U A‖ ≤ ‖A‖ := by
  change ‖(A : A7DimensionalJet n_d U).1‖ ≤
    ‖(A : A7DimensionalJet n_d U)‖
  exact norm_fst_le (A : A7DimensionalJet n_d U)

theorem a7DimensionalH2_is_complete
    (n_d : ℕ) (U : Set (PaperSpatial n_d)) :
    CompleteSpace (A7DimensionalH2 n_d U) := inferInstance

/-- This single construction can be specialized to each paper dimension. -/
example (U₁ : Set (PaperSpatial 1)) : CompleteSpace (A7DimensionalH2 1 U₁) :=
  a7DimensionalH2_is_complete 1 U₁
example (U₂ : Set (PaperSpatial 2)) : CompleteSpace (A7DimensionalH2 2 U₂) :=
  a7DimensionalH2_is_complete 2 U₂
example (U₃ : Set (PaperSpatial 3)) : CompleteSpace (A7DimensionalH2 3 U₃) :=
  a7DimensionalH2_is_complete 3 U₃

#print axioms a7_dimensional_mem_H2_iff
#print axioms a7DimensionalH2Embedding_norm_le

end ReservoirSeismicityControl.Paper2026
