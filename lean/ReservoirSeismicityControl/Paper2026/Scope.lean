import Mathlib.Tactic

/-!
# Paper 2026 — exact scope changes

The latest manuscript treats spatial dimensions n_d ∈ {1, 2, 3} and a
KNOWN, SPATIALLY CONSTANT sign s ∈ {-1, 1} in the SR equation.
The normalized SR tracking error includes the same sign s, so the direct
SR control coefficient is positive because s * s = 1.

This module proves that scalar sign cancellation only. It makes NO claim
that existing 3D-specific spatial proofs already cover n_d = 1 or n_d = 2.
-/

namespace ReservoirSeismicityControl.Paper2026

/-- The spatial dimensions admitted by the final manuscript. -/
def admissibleSpatialDimension (n_d : ℕ) : Prop :=
  n_d = 1 ∨ n_d = 2 ∨ n_d = 3

/-- The paper's known global SR sign: injection-promoting or extraction-promoting. -/
def admissibleSRSign (s : ℝ) : Prop :=
  s = -1 ∨ s = 1

theorem sr_sign_square (s : ℝ) (hs : admissibleSRSign s) :
    s * s = 1 := by
  rcases hs with h | h
  · simp [h]
  · simp [h]

/-- Eq. (3) with error definition (12): both sign factors cancel in B(t) (15). -/
theorem signed_sr_input_coefficient (s sensitivity : ℝ)
    (hs : admissibleSRSign s) :
    s * (s * sensitivity) = sensitivity := by
  calc
    s * (s * sensitivity) = (s * s) * sensitivity := by ring
    _ = sensitivity := by simp [sr_sign_square s hs]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.sr_sign_square
#print axioms ReservoirSeismicityControl.Paper2026.signed_sr_input_coefficient
