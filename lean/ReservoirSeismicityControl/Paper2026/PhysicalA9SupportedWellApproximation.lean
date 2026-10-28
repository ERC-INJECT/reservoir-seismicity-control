import ReservoirSeismicityControl.PressureNeumann3DRestrictedInteriorTestApprox
import ReservoirSeismicityControl.PressureNeumann3DCompactCutoffs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
Appendix A.3 (A9): localized approximation of the ACTUAL compactly supported
3D well profile, measured in the L² norm of the WHOLE reservoir.

This is not the already proved unrestricted C_c^∞ density theorem.  A fixed
cutoff equal to one on the physical well support ensures that the smooth
approximants, and the approximation errors after subtracting the same
constant pressure-mean correction, remain in the prescribed near collar U.

Still separate: transport from ambient restricted L² to reservoir subtype L²,
identification of compact interior tests with D(A) for the physical Neumann
operator, and application of the off-diagonal semigroup estimate.  None of
those results are silently included in the hypothesis below.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal

/-- A physical well supported on compact `K ⊂ U` admits a smooth approximation
supported entirely in `U`, while its error is measured over the full
reservoir `Ω`.  The arbitrary constant `c` is the mean-zero correction in
`f_j = B_j / β - c`; it cancels in the error and introduces no far support.

All approximation and cutoff theorems are already proved in the recovered
Neumann modules; only the localized global-error identification is new. -/
theorem paper_A9_physical_3d_localized_centered_well_approximation
    (Ω U : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (hU : Bornology.IsBounded (U : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKU : K ⊆ (U : Set pressureNeumannE3))
    (B : pressureNeumannE3 → ℝ)
    (hB : MemLp B 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    (hBsupport : Function.support B ⊆ K)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothScalarTests U,
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆ (U : Set pressureNeumannE3) ∧
      eLpNorm (fun x : pressureNeumannE3 =>
          (B x - c) - ((φ : pressureNeumannE3 → ℝ) x - c)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal ε ∧
      Function.support (fun x : pressureNeumannE3 =>
          (B x - c) - ((φ : pressureNeumannE3 → ℝ) x - c)) ⊆
        (U : Set pressureNeumannE3) := by
  classical
  obtain ⟨g, hgApprox⟩ :=
    pressure_neumann_3d_restricted_interior_scalar_approx Ω ν hΩ B hB hε
  obtain ⟨ψ, hψOne, hψBox, _⟩ :=
    pressure_neumann_3d_exists_compact_interior_cutoff U hU K hK hKU
  let φ : pressureNeumann3DSmoothScalarTests U :=
    pressureNeumann3DLocalizeScalar U ψ
      (g : pressureNeumannE3 → ℝ) g.contDiff
  have hφ (x : pressureNeumannE3) :
      (φ : pressureNeumannE3 → ℝ) x = ψ x * (g : pressureNeumannE3 → ℝ) x :=
    pressure_neumann_3d_localize_scalar_apply U ψ
      (g : pressureNeumannE3 → ℝ) g.contDiff x
  have hψB (x : pressureNeumannE3) : ψ x * B x = B x := by
    by_cases hx : x ∈ K
    · rw [hψOne x hx, one_mul]
    · have hBx : B x = 0 := by
        by_contra hn
        exact hx (hBsupport hn)
      simp [hBx]
  have hpoint (x : pressureNeumannE3) :
      ‖B x - (φ : pressureNeumannE3 → ℝ) x‖ ≤
        ‖B x - (g : pressureNeumannE3 → ℝ) x‖ := by
    have herr : B x - (φ : pressureNeumannE3 → ℝ) x =
        ψ x * (B x - (g : pressureNeumannE3 → ℝ) x) := by
      rw [hφ, mul_sub, hψB]
    rw [herr, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (hψBox x).1]
    calc
      ψ x * ‖B x - (g : pressureNeumannE3 → ℝ) x‖ ≤
          1 * ‖B x - (g : pressureNeumannE3 → ℝ) x‖ :=
        mul_le_mul_of_nonneg_right (hψBox x).2 (norm_nonneg _)
      _ = _ := one_mul _
  have hMeas : AEStronglyMeasurable
      (B - (φ : pressureNeumannE3 → ℝ))
      (ν.restrict (Ω : Set pressureNeumannE3)) :=
    hB.aestronglyMeasurable.sub φ.contDiff.continuous.aestronglyMeasurable
  have hNorm :
      eLpNorm (B - (φ : pressureNeumannE3 → ℝ)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal ε := by
    exact (eLpNorm_mono_ae hMeas
      (Filter.Eventually.of_forall hpoint)).trans hgApprox
  have hCenter :
      (fun x : pressureNeumannE3 => (B x - c) -
        ((φ : pressureNeumannE3 → ℝ) x - c)) =
      B - (φ : pressureNeumannE3 → ℝ) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  refine ⟨φ, φ.tsupport_subset, ?_, ?_⟩
  · rw [hCenter]
    exact hNorm
  · rw [hCenter]
    intro x hx
    by_contra hxU
    have hxK : x ∉ K := fun hk => hxU (hKU hk)
    have hBx : B x = 0 := by
      by_contra hn
      exact hxK (hBsupport hn)
    have hφx : (φ : pressureNeumannE3 → ℝ) x = 0 := by
      by_contra hn
      exact hxU (φ.tsupport_subset
        (subset_tsupport (φ : pressureNeumannE3 → ℝ) hn))
    have hz : (B - (φ : pressureNeumannE3 → ℝ)) x = 0 := by
      simp [hBx, hφx]
    exact hx hz

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_3d_localized_centered_well_approximation
