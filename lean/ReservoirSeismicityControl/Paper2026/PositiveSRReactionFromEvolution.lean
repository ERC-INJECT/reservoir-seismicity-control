import ReservoirSeismicityControl.Paper2026.PositiveSRReactionL2Envelope
import ReservoirSeismicityControl.SeismicityPhysicalL2RateBridge

/-!
# P3 / Appendix A.3: SR reaction rate from the signed strong L² evolution

The manuscript's (A7) rate estimate follows from the pressure-to-SR
strong L² equation. We reuse that established estimate to remove the
independent `‖Rdot‖ ≤ CRdot` premise of the actual signed regional reaction
integral certificate in `PositiveSRReactionL2Envelope`.

For s in {-1, 1}, the coefficient and sign of the pressure-to-SR coupling
are represented by `Kpressure`. The physical identification of this
operator with multiplication by `-s gamma1 R`, of `srReaction` with
`gamma2 R (R-Rstar)`, and of `Fdot` with the product-rule reaction rate
remains explicit; none of those PDE/ODE applicability conditions is
silently deduced from an arbitrary operator.

The independent SR L²-rate hypothesis is removed, without introducing a
well-rate derivative or a Q_t hypothesis. The reaction-field strong L²
product rule and A3 coefficient bounds are still physical obligations.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The signed, normalized physical SR regional reaction certificate, with
its rate bounded directly by the strong SR equation as in (A7).

This removes `hRRate` from the regional reaction interface. The inputs
`hPressureBound`, `hUDotBound`, `hSRReactionBound`, `hSRODE` are the same
strong pressure-to-SR evolution inputs already used in P5/B19. -/
theorem physical_sr_reaction_regional_ae_from_sr_evolution
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (hpositive : 0 < μ.real region)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (F Fdot forcing Rdot Udot srReaction : ℝ → Lp ℝ 2 μ)
    (Kreact Kpressure : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cforcing CreactMultiplier Cpressure CU CsrReaction : ℝ)
    (hrep : ∀ τ, ∀ᵐ x ∂(μ.restrict region),
      ((F τ) x : ℝ) = gamma2 τ x * R τ x * (R τ x - Rstar x))
    (hRateRep : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂(μ.restrict region),
        ((Fdot t) x : ℝ) =
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hStrong : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt F (Fdot t) t)
    (hDecomp : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Fdot t = forcing t + Kreact t (Rdot t))
    (hForcing : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖forcing t‖ ≤ Cforcing)
    (hReactionMultiplier : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Kreact t‖ ≤ CreactMultiplier)
    (hPressureBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Kpressure t‖ ≤ Cpressure)
    (hUDotBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Udot t‖ ≤ CU)
    (hSRReactionBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖srReaction t‖ ≤ CsrReaction)
    (hSRODE : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Rdot t = -(Kpressure t (Udot t)) - srReaction t) :
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
            (Cforcing + CreactMultiplier * (Cpressure * CU + CsrReaction))) /
            μ.real region) := by
  have hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ Cpressure * CU + CsrReaction :=
    ReservoirSeismicityControl.sr_rate_L2_from_pressure_ae μ Udot Rdot srReaction Kpressure
      Cpressure CU CsrReaction
      hPressureBound hUDotBound hSRReactionBound hSRODE
  exact physical_sr_reaction_regional_ae_from_L2_components
    μ region hs hfinite hpositive
    gamma2 gamma2Rate R RRate Rstar
    sign gamma10 R0star
    F Fdot forcing Rdot Kreact
    Cforcing CreactMultiplier (Cpressure * CU + CsrReaction)
    hrep hRateRep hStrong hDecomp hForcing hReactionMultiplier hSRRate

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae_from_sr_evolution
