import ReservoirSeismicityControl.Algebra
import ReservoirSeismicityControl.Definitions

/-!
# Appendix A.4: nominal uncertainty and normalized perturbation

The scalar compressibility condition is proved in Algebra.lean.

Remaining genuinely matrix-valued targets:
1. Disjoint row supports give diagonal G=B B₀⁺.
2. Well sensitivity averages have strictly positive global bounds.
3. Proper SR scaling yields ‖G-I‖ < 1.
4. The derivative of G⁻¹ Ψ is bounded using Ψ, Ψ', G' and ‖G⁻¹‖.

There are NO claims here that the full matrix argument has been checked.
-/

namespace ReservoirSeismicityControl

/-- If positive SR sensitivities stay between fixed values, the midpoint
    normalization has a strict contraction margin. -/
theorem sr_midpoint_margin
    (hmin hmax : ℝ) (hmin_pos : 0 < hmin)
    (hmax_ge : hmin ≤ hmax) :
    (hmax - hmin) / (hmax + hmin) < 1 := by
  have hden : 0 < hmax + hmin := by linarith
  apply (div_lt_iff₀ hden).2
  linarith

/-- Scalar coefficient uncertainty for the pressure-only case. -/
theorem pressure_only_uncertainty
    (β β₀ : ℝ) (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (hupper : β₀ < 2 * β) :
    |β₀ / β - 1| < 1 :=
  beta_mismatch_lt_one β β₀ hβ hβ₀ hupper

end ReservoirSeismicityControl
