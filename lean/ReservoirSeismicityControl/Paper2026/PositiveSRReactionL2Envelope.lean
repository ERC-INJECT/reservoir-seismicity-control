import ReservoirSeismicityControl.Paper2026.PositiveSRReactionRegional

/-!
# P3 / Appendix A.3: actual regional reaction L² rate envelope

Appendix A.3 differentiates `γ₂ R (R-R*)` and separates its derivative into
`γ₂,t R (R-R*)` and the multiplication operator `γ₂ (2 R-R*)` applied to `R_t`.

This module REMOVES the independent `‖Fdot‖ ≤ C` hypothesis from the already
verified regional reaction certificate. It derives that norm estimate from the
corresponding forcing, bounded multiplier, and physical `R_t : L²` estimates.

The remaining hypotheses are deliberately identified as applicability checks:
  * `hDecomp`: the two physical terms represent the product-rule rate in L²;
  * `hForcing`: the coefficient-rate part has the A3 finite-volume bound;
  * `hMultiplier`: multiplication by `γ₂(2R-R*)` has the A3 operator bound;
  * `hRRate`: the physical SR time derivative has the uniform (A7) L² bound;
  * `hStrong`: strong L² differentiation of the reaction field, and
    `hRateRep`: its actual spatial representative from Appendix A.3.

No `Q_t` hypothesis, new analytic axiom, or stability result is used.
The time variable and signed normalization follow the manuscript exactly.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The A.3 decomposition gives the L² rate estimate by a single operator
norm inequality. This is the *specific* rate bound required by the regional
reaction integral, not a postulated bound on its time derivative. -/
theorem physical_sr_reaction_L2_rate_from_components_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (Fdot forcing Rdot : ℝ → Lp ℝ 2 μ)
    (K : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cforcing Cmult CRdot : ℝ)
    (hDecomp : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Fdot t = forcing t + K t (Rdot t))
    (hForcing : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖forcing t‖ ≤ Cforcing)
    (hMultiplier : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖K t‖ ≤ Cmult)
    (hRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CRdot) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Fdot t‖ ≤ Cforcing + Cmult * CRdot := by
  filter_upwards [hDecomp, hForcing, hMultiplier, hRRate]
    with t hFt hAt hKt hRt
  have hCR : 0 ≤ CRdot := (norm_nonneg (Rdot t)).trans hRt
  calc
    ‖Fdot t‖ = ‖forcing t + K t (Rdot t)‖ := by rw [hFt]
    _ ≤ ‖forcing t‖ + ‖K t (Rdot t)‖ := norm_add_le _ _
    _ ≤ ‖forcing t‖ + ‖K t‖ * ‖Rdot t‖ :=
      add_le_add (le_refl _) ((K t).le_opNorm (Rdot t))
    _ ≤ ‖forcing t‖ + ‖K t‖ * CRdot :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hRt (norm_nonneg (K t)))
    _ ≤ Cforcing + Cmult * CRdot :=
      add_le_add hAt (mul_le_mul_of_nonneg_right hKt hCR)

/-- Appendix A.3 regional reaction integral and derivative estimate with the
L² bound *derived from* the physical product-rule decomposition, rather than
assumed independently. The actual regional sign `-s/(γ₁₀ R₀*)` is retained.

A3 and (A7) must still be checked to obtain `hForcing`, `hMultiplier`, and
`hRRate`; `hStrong` and the representative equations are likewise explicit.
No estimate for the entire `Ψ` is assumed or claimed here. -/
theorem physical_sr_reaction_regional_ae_from_L2_components
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (hpositive : 0 < μ.real region)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (F Fdot forcing Rdot : ℝ → Lp ℝ 2 μ)
    (K : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cforcing Cmult CRdot : ℝ)
    (hrep : ∀ τ, ∀ᵐ x ∂(μ.restrict region),
      ((F τ) x : ℝ) = gamma2 τ x * R τ x * (R τ x - Rstar x))
    (hRateRep : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂(μ.restrict region),
        ((Fdot t) x : ℝ) =
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hStrong : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt F (Fdot t) t)
    (hDecomp : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Fdot t = forcing t + K t (Rdot t))
    (hForcing : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖forcing t‖ ≤ Cforcing)
    (hMultiplier : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖K t‖ ≤ Cmult)
    (hRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CRdot) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRRegionalReaction μ region gamma2 R Rstar sign gamma10 R0star)
        ((-sign / (gamma10 * R0star)) *
          ((∫ x in region,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real region)) t ∧
      |(-sign / (gamma10 * R0star)) *
        ((∫ x in region,
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
          μ.real region)| ≤
        |(-sign / (gamma10 * R0star))| *
          (((μ.real region) ^ (1 / (2 : ℝ)) *
            (Cforcing + Cmult * CRdot)) / μ.real region) := by
  have hL2 : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Fdot t‖ ≤ Cforcing + Cmult * CRdot :=
    physical_sr_reaction_L2_rate_from_components_ae μ
      Fdot forcing Rdot K Cforcing Cmult CRdot
      hDecomp hForcing hMultiplier hRRate
  exact physical_sr_reaction_regional_ae μ region hs hfinite hpositive
    gamma2 gamma2Rate R RRate Rstar sign gamma10 R0star
    (Cforcing + Cmult * CRdot) F Fdot hrep hRateRep hStrong hL2

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_L2_rate_from_components_ae
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_L2_components
