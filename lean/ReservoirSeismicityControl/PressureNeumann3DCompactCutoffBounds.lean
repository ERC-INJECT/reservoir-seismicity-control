import ReservoirSeismicityControl.PressureNeumann3DCompactCutoffs

/-!
# Quantitative pointwise estimate for compact localization

For a smooth ambient vector field f, the bounded-reservoir compact cutoff
ψ has 0 ≤ ψ ≤ 1 and ψ = 1 on the prescribed compact K. Therefore
its smooth interior localization g = ψ f satisfies

* g = f on K,
* ‖f(x) - g(x)‖ ≤ ‖f(x)‖ everywhere.

In particular, the error is supported outside K and is pointwise
dominated by f there. This is the bound needed in the later L²
localization argument. No L²-density assertion is made in this file.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace
open scoped Distributions

variable (Ω : Opens pressureNeumannE3)

/-- Smooth compact localization agrees on K and has pointwise error
bounded by the unlocalized vector field. -/
theorem pressure_neumann_3d_compact_vector_localization_error_bound
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set pressureNeumannE3))
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∃ g : pressureNeumann3DSmoothVectorTests Ω,
      (∀ x ∈ K, g x = f x) ∧
      (∀ x : pressureNeumannE3, ‖f x - g x‖ ≤ ‖f x‖) := by
  obtain ⟨ψ, hOne, hBox, _⟩ :=
    pressure_neumann_3d_exists_compact_interior_cutoff Ω hΩ K hK hKΩ
  refine ⟨pressureNeumann3DLocalizeVector Ω ψ f hf, ?_, ?_⟩
  · intro x hx
    rw [pressure_neumann_3d_localize_vector_apply, hOne x hx, one_smul]
  · intro x
    rw [pressure_neumann_3d_localize_vector_apply]
    have heq : f x - ψ x • f x = (1 - ψ x) • f x := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(hBox x).2])]
    calc
      (1 - ψ x) * ‖f x‖ ≤ 1 * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (by linarith [(hBox x).1]) (norm_nonneg _)
      _ = ‖f x‖ := one_mul _

end ReservoirSeismicityControl
