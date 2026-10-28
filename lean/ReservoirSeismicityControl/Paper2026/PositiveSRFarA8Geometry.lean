import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection

/-!
# P3 / Appendix A.3 (A8): one smooth cutoff for all finite well supports

The paper's far observation uses the smooth weight `(1-ζ)w`, while the
published Davies–Gaffney bounds are applied to an off-diagonal projection.
This module verifies that a *single* cutoff which equals one on a
`dsep`-neighborhood of every well implies the required separation for
all finite well sources and that the earlier smooth-kernel estimate can be
instantiated with the canonical far set `{ζ ≠ 1}`.

It does not reprove the external semigroup estimates, construct a smooth
cutoff, or assert the hypotheses of the external results unconditionally.
Positive-lag projected-orbit and second-orbit bounds are explicit,
substantive external applicability premises. There is no `Qdot` premise.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The geometric hypothesis for the *one cutoff used for every well*
instantiates the previously proved separation estimate simultaneously
for all well supports. The bound `dsep > 0` is the paper's stipulated
strict separation; it is not inferred from arbitrary disjoint supports. -/
theorem paper_sr_far_cutoff_all_wells_separated
    {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (ζ : X → ℝ) (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1) :
    ∀ (j : Fin n) (x : X), x ∈ {x : X | ζ x ≠ 1} →
      ∀ (y : X), y ∈ well j → dsep ≤ dist x y := by
  intro j
  exact paper_sr_far_nonunit_cutoff_separation ζ (well j) dsep (hnear j)

/-- (A8) applicability reduction for the actual smooth SR weight and
all reservoir wells. The geometric separation is a Lean conclusion;
the two displayed projected-orbit estimates are precisely the analytic
Davies–Gaffney/semigroup hypotheses to be checked for the physical
Neumann generator, **not** newly postulated mathematical results.

The scalar kernel estimates are obtained by the already verified
smooth-projection and Hilbert-space pairing proofs. -/
theorem paper_sr_smooth_far_A8_from_all_well_cutoff
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1)
    (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j s)‖ ≤ B₁ j s) :
    (∀ (j : Fin n) (x : X), x ∈ {x : X | ζ x ≠ 1} →
      ∀ (y : X), y ∈ well j → dsep ≤ dist x y) ∧
    (∀ (t : ℝ) (j : Fin n) (s : ℝ), 0 < s →
      let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
        ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
      |paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
        cutoff V E hsep orbit t j s| ≤ Lw * B₀ j s ∧
      |ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff)
        second t j s| ≤ Lw * B₁ j s) := by
  constructor
  · exact paper_sr_far_cutoff_all_wells_separated ζ well dsep hnear
  · intro t j s hs
    exact paper_sr_smooth_far_projected_kernel_bounds
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
      cutoff hCγ hK hR hderiv hrate ζ {x : X | ζ x ≠ 1} hfar
      hcutoff
      (by
        intro x hx
        by_contra hne
        exact hx hne)
      V E hsep orbit second B₀ B₁ hB₀ hB₁
      hProjectedOrbit hProjectedSecond t j s hs

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_cutoff_all_wells_separated
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_from_all_well_cutoff
