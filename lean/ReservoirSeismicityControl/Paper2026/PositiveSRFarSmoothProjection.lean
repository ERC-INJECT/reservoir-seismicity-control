import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothKernel
import ReservoirSeismicityControl.PaperFarLpSelfAdjoint
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 — localizing the actual smooth far observation

For the paper's fixed smooth cutoff ζ, the far SR weight is `(1-ζ)w`.
The earlier projected-kernel certificates used the sharp indicator of a
far region. These are NOT interchangeable weights. Instead, if ζ = 1
outside that far region, the smooth weight is FIXED by the sharp
projection. We prove this from the spatial representative of multiplication
by ζ and then apply the pre-existing projected Neumann estimates.

The cutoff multiplier identity is the standard L² multiplication
construction, represented as an explicit applicability condition.
The positive source/far-support separation and projected-orbit bounds
remain the hypotheses of the cited Davies–Gaffney result; we do not
reprove that theorem or assert those estimates without its hypotheses.
No derivatives of Q are used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The smooth far weight `(1-ζ)w` is supported in the measurable far
region, hence is fixed by the *actual* L² indicator projection. The
conditions mean precisely that `cutoff` acts as multiplication by ζ on
the physical SR weights, and ζ equals one outside the far region. -/
theorem paper_sr_smooth_far_projection_fixed
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ) (far : Set X) (hfar : MeasurableSet far)
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (hζfar : ∀ x : X, x ∉ far → ζ x = 1)
    (t : ℝ) :
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) =
    paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t := by
  let w : Lp ℝ 2 μ :=
    paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t
  have hsupport : ∀ᵐ x ∂μ, x ∉ far →
      ((paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) x : ℝ) = 0 := by
    filter_upwards [Lp.coeFn_sub w (cutoff w), hcutoff t]
      with x hsub hmul
    intro hx
    have hpoint : ((cutoff w) x : ℝ) = ζ x * ((w x : ℝ)) := by
      exact hmul
    change ((w - cutoff w : Lp ℝ 2 μ) x : ℝ) = 0
    rw [hsub]
    change ((w x : ℝ) - ((cutoff w) x : ℝ)) = 0
    rw [hpoint, hζfar x hx]
    ring
  exact ReservoirSeismicityControl.paper_far_lp_projection_eq_of_support
    μ far hfar _ hsupport

/-- With the canonical far set `{x | ζ x ≠ 1}`, the support condition
`ζ=1` outside that set is automatic. The only remaining identification
is that `cutoff` is the paper's multiplication operator on L². -/
theorem paper_sr_smooth_far_projection_nonunit_set
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (t : ℝ) :
    ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) =
    paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t := by
  exact paper_sr_smooth_far_projection_fixed
    μ region hregion Kγ R gamma10 R0star cutoff
    ζ {x : X | ζ x ≠ 1} hfar hcutoff
    (by
      intro x hx
      by_contra hne
      exact hx hne) t

/-- The geometric implication required to APPLY Davies–Gaffney: if the
paper's smooth cutoff is identically one throughout a `dsep`-neighborhood
of each well support, its nonunit region is at least `dsep` away from the
well. This proves only the geometric implication, not the existence of ζ
or any semigroup estimate. -/
theorem paper_sr_far_nonunit_cutoff_separation
    {X : Type*} [PseudoMetricSpace X]
    (ζ : X → ℝ) (well : Set X) (dsep : ℝ)
    (hnear : ∀ (x y : X), y ∈ well → dist x y < dsep → ζ x = 1) :
    ∀ x ∈ {x : X | ζ x ≠ 1}, ∀ y ∈ well, dsep ≤ dist x y := by
  intro x hx y hy
  by_contra hnot
  exact hx (hnear x y hy (lt_of_not_ge hnot))

/-- Projected-orbit and projected-second-orbit estimates from the cited
semigroup result give both scalar far-kernel bounds for the *smooth*
physical SR weight. This removes the free far-support and observation-
norm hypotheses from the earlier abstract projected-kernel certificate.

The orbit inequalities remain the explicitly identified external
Davies–Gaffney inputs; their applicability to the physical Neumann
operator and the paper's positive spatial separation is not asserted here. -/
theorem paper_sr_smooth_far_projected_kernel_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
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
    (ζ : X → ℝ) (far : Set X) (hfar : MeasurableSet far)
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (hζfar : ∀ x : X, x ∉ far → ζ x = 1)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j s)‖ ≤
        B₁ j s)
    (t : ℝ) (j : Fin n) (s : ℝ) (hs : 0 < s) :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
      ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
    |paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
      cutoff V E hsep orbit t j s| ≤ Lw * B₀ j s ∧
    |ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
      (paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff)
      second t j s| ≤ Lw * B₁ j s := by
  let weight : ℝ → Lp ℝ 2 μ :=
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  have hfixed : ∀ τ : ℝ,
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar (weight τ) = weight τ := by
    intro τ
    exact paper_sr_smooth_far_projection_fixed
      μ region hregion Kγ R gamma10 R0star cutoff
      ζ far hfar hcutoff hζfar τ
  have hweight : ∀ τ : ℝ, ‖weight τ‖ ≤ Lw := by
    intro τ
    exact (paper_sr_diffusion_near_far_norm_bounds
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR cutoff
      hCγ hK hR hderiv hrate).2 τ
  constructor
  · change |ReservoirSeismicityControl.paperFarWeakNeumannKernel V E hsep
        weight orbit t j s| ≤ Lw * B₀ j s
    exact ReservoirSeismicityControl.paper_far_weak_neumann_kernel_from_projected_orbit
      V E hsep (ReservoirSeismicityControl.paperFarLpProjection μ far hfar)
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint μ far hfar)
      weight orbit Lw B₀ hfixed hweight hB₀ hProjectedOrbit t j s hs
  · exact ReservoirSeismicityControl.paper_far_weak_neumann_rate_from_projected_second
      (ReservoirSeismicityControl.paperFarLpProjection μ far hfar)
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint μ far hfar)
      weight second Lw B₁ hfixed hweight hB₁ hProjectedSecond t j s hs

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_fixed
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projected_kernel_bounds

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_projection_nonunit_set
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_nonunit_cutoff_separation
