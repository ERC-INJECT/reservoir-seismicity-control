import Mathlib

/-!
# Spatial dimension convention for the ReservoirSeismicityControl 2026 manuscript

The manuscript restricts n_d to {1,2,3}. All dimension-dependent
constructions should be indexed by n_d and any use of dimension <=3
should require an explicit membership certificate. Existing 3D proofs
remain usable by specializing n_d := 3.
-/

namespace ReservoirSeismicityControl.Paper2026

/-- Precisely the spatial dimensions admitted in the paper. -/
def paperSpatialDimensions : Finset ℕ := {1, 2, 3}

/-- Use this one proposition throughout dimension-dependent modules. -/
def PaperSpatialDimension (n_d : ℕ) : Prop :=
  n_d ∈ paperSpatialDimensions

theorem paperSpatialDimension_iff (n_d : ℕ) :
    PaperSpatialDimension n_d ↔ n_d = 1 ∨ n_d = 2 ∨ n_d = 3 := by
  simp [PaperSpatialDimension, paperSpatialDimensions]

theorem paperSpatialDimension_one : PaperSpatialDimension 1 := by
  simp [PaperSpatialDimension, paperSpatialDimensions]

theorem paperSpatialDimension_two : PaperSpatialDimension 2 := by
  simp [PaperSpatialDimension, paperSpatialDimensions]

theorem paperSpatialDimension_three : PaperSpatialDimension 3 := by
  simp [PaperSpatialDimension, paperSpatialDimensions]

theorem paperSpatialDimension_pos {n_d : ℕ}
    (h : PaperSpatialDimension n_d) : 0 < n_d := by
  rcases (paperSpatialDimension_iff n_d).mp h with h | h | h <;> omega

theorem paperSpatialDimension_le_three {n_d : ℕ}
    (h : PaperSpatialDimension n_d) : n_d ≤ 3 := by
  rcases (paperSpatialDimension_iff n_d).mp h with h | h | h <;> omega

/-- Euclidean coordinates in the selected spatial dimension. -/
abbrev PaperSpatial (n_d : ℕ) := Fin n_d → ℝ

/-- A dimension carrying the manuscript's admissibility certificate. -/
abbrev PaperDimension := { n_d : ℕ // PaperSpatialDimension n_d }

end ReservoirSeismicityControl.Paper2026
