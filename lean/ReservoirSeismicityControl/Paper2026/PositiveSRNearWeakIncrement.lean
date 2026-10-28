import ReservoirSeismicityControl.Paper2026.PositiveSRNearWeakBound
import Mathlib.Tactic

/-!
# P3, Appendix A.3 — actual near-field finite increments

For the physical normalized signed-SR near weight `w_near = ζ w`,
this module proves the finite-increment identity

  <w_near(s), A p(s)> - <w_near(t), A p(t)>
    = <w_near(s)-w_near(t), A p(s)>
      + <A w_near(t), p(s)-p(t)>.

Only symmetry of the UNBOUNDED Neumann operator on its explicit domain
is used. In particular, neither a derivative of `A p` nor a derivative
of the well flux Q is introduced. This is the algebraic identity underlying
the weak derivative formula in Appendix A.3; passage to the time-derivative
limit and the local H² -> D(A) applicability are still OPEN.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Exact A.3 near-observation increment, with the previously verified
physical normalized signed-SR weight, not an arbitrary test function.
The `D(A)` membership hypotheses are explicit physical applicability
conditions of the cited local elliptic regularity theorem. -/
theorem paper_sr_near_observation_increment
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : Lp ℝ 2 μ)⟫_ℝ = ⟪(u : Lp ℝ 2 μ), A v⟫_ℝ)
    (pressure : ℝ → Lp ℝ 2 μ)
    (hpD : ∀ τ, pressure τ ∈ D)
    (hwD : ∀ τ, paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ ∈ D)
    (t s : ℝ) :
    ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff s, A ⟨pressure s, hpD s⟩⟫_ℝ -
      ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t, A ⟨pressure t, hpD t⟩⟫_ℝ =
    ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff s -
       paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t, A ⟨pressure s, hpD s⟩⟫_ℝ +
    ⟪A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t, hwD t⟩,
      pressure s - pressure t⟫_ℝ := by
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ
  have hs : ⟪w t, A ⟨pressure s, hpD s⟩⟫_ℝ =
      ⟪A ⟨w t, hwD t⟩, pressure s⟫_ℝ :=
    (hSymm ⟨w t, hwD t⟩ ⟨pressure s, hpD s⟩).symm
  have ht : ⟪w t, A ⟨pressure t, hpD t⟩⟫_ℝ =
      ⟪A ⟨w t, hwD t⟩, pressure t⟫_ℝ :=
    (hSymm ⟨w t, hwD t⟩ ⟨pressure t, hpD t⟩).symm
  change ⟪w s, A ⟨pressure s, hpD s⟩⟫_ℝ -
      ⟪w t, A ⟨pressure t, hpD t⟩⟫_ℝ =
    ⟪w s - w t, A ⟨pressure s, hpD s⟩⟫_ℝ +
    ⟪A ⟨w t, hwD t⟩, pressure s - pressure t⟫_ℝ
  rw [inner_sub_left, inner_sub_right, ← hs, ← ht]
  abel

/-- Quantitative finite-increment inequality for the SAME physical
observation. This is the correct estimate from which the A.3 weak
product rule can be obtained via standard difference-quotient limits;
that analytic limit is not claimed by the present lemma. -/
theorem paper_sr_near_observation_increment_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : Lp ℝ 2 μ)⟫_ℝ = ⟪(u : Lp ℝ 2 μ), A v⟫_ℝ)
    (pressure : ℝ → Lp ℝ 2 μ)
    (hpD : ∀ τ, pressure τ ∈ D)
    (hwD : ∀ τ, paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ ∈ D)
    (t s : ℝ) :
    |⟪paperSRNearDiffusionWeight μ region hregion Kγ R
         gamma10 R0star cutoff s, A ⟨pressure s, hpD s⟩⟫_ℝ -
       ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
         gamma10 R0star cutoff t, A ⟨pressure t, hpD t⟩⟫_ℝ| ≤
    ‖paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff s -
      paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t‖ * ‖A ⟨pressure s, hpD s⟩‖ +
    ‖A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t, hwD t⟩‖ *
      ‖pressure s - pressure t‖ := by
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ
  have hfirst : |⟪w s - w t, A ⟨pressure s, hpD s⟩⟫_ℝ| ≤
      ‖w s - w t‖ * ‖A ⟨pressure s, hpD s⟩‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (w s - w t) (A ⟨pressure s, hpD s⟩))
  have hsecond : |⟪A ⟨w t, hwD t⟩, pressure s - pressure t⟫_ℝ| ≤
      ‖A ⟨w t, hwD t⟩‖ * ‖pressure s - pressure t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ)
        (A ⟨w t, hwD t⟩) (pressure s - pressure t))
  have hinc := paper_sr_near_observation_increment
    μ region hregion Kγ R gamma10 R0star cutoff D A hSymm
    pressure hpD hwD t s
  change |⟪w s, A ⟨pressure s, hpD s⟩⟫_ℝ -
      ⟪w t, A ⟨pressure t, hpD t⟩⟫_ℝ| ≤ _
  rw [hinc]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_increment_bound
