import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9BoundedFlux
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# P3 / Appendix A.3 (A9): moving observation and projected pressure

The already proved smooth-cutoff projection identity makes the physical
far observation equal to its pairing with the projected pressure `P (Ap t)`.
The already proved strong L² SR-weight derivative can therefore be combined
with the *projected pressure* derivative by Mathlib's inner-product rule.

Crucially, `hProjectedRate` below is NOT the conclusion (A9): it is the
strong-L² differentiability of the far-projected pressure field. Its proof
from the mild Neumann evolution for bounded measurable fluxes is the precise
remaining external semigroup applicability obligation. This theorem does
NOT assume differentiability of the full unprojected `Ap`, nor of Q.

No new physics or model assumption is introduced. In particular, this file
must NOT be described as completing A9 until `hProjectedRate` has been
obtained from the physical projected semigroup formula and the A8 kernel
bounds, and its rate has been identified with the A9 causal convolution.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Physical moving SR far-observation derivative via the actual smooth
cutoff, the actual sharp far projection and the published (external)
projected-semigroup differentiability result. No derivative of Q occurs.
The premise is on the *projected L² state*, not on the desired scalar
observation derivative. -/
theorem paper_sr_far_A9_moving_weight_from_projected_pressure_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
    (Ap projectedRate : ℝ → Lp ℝ 2 μ)
    (hR : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hProjectedRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap τ))
        (projectedRate t) t) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t -
           cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t),
           ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)⟫_ℝ +
         ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
             gamma10 R0star cutoff t, projectedRate t⟫_ℝ) t := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let w : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff τ
  let wdot : ℝ → Lp ℝ 2 μ := fun τ =>
    paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star τ -
      cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot gamma10 R0star τ)
  have hfixed : ∀ τ, P (w τ) = w τ := by
    intro τ
    exact paper_sr_smooth_far_projection_nonunit_set
      μ region hregion Kγ R gamma10 R0star cutoff
      ζ hfar hcutoff τ
  have hObs :
      (fun τ => ⟪w τ, Ap τ⟫_ℝ) =
      (fun τ => ⟪w τ, P (Ap τ)⟫_ℝ) := by
    funext τ
    exact ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
        μ {x : X | ζ x ≠ 1} hfar)
      (w τ) (Ap τ) (hfixed τ)
  filter_upwards [hR, hProjectedRate] with t hRt hPt
  have hw := (paper_sr_diffusion_near_far_hasDerivAt
    μ region hregion Kγ R Rdot gamma10 R0star cutoff t hRt).2
  have hPair := (hw.inner ℝ hPt)
  change HasDerivAt
    (fun τ => ⟪w τ, Ap τ⟫_ℝ)
    (⟪wdot t, P (Ap t)⟫_ℝ + ⟪w t, projectedRate t⟫_ℝ) t
  rw [hObs]
  convert hPair using 1
  exact add_comm _ _

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_far_A9_moving_weight_from_projected_pressure_ae
