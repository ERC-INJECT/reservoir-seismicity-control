import ReservoirSeismicityControl.Paper2026.PositiveSRReactionRate
import ReservoirSeismicityControl.WellMeanDerivative
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: the actual regional SR reaction Lebesgue integral

Appendix A.3 contains the normalized regional reaction contribution
  -s/(gamma10 * R0star) * (1/|V_R|) * integral_(V_R) gamma2 R (R-Rstar).
This module passes the existing pointwise product rule through the ACTUAL
regional spatial Lebesgue integral, using the already verified continuous
L2 integration functional (WellIntegralL2 / WellMeanDerivative).

The analytical inputs that still require verification from A3 and (A7) are
made explicit: the reaction integrand has a strongly differentiable L2
representative, its derivative has the stated physical representative,
and its L2 norm is bounded. The last input is precisely where the paper
uses spatial coefficient bounds and Holder's inequality. It is NOT an
independent hypothesis about the regional perturbation's derivative.

The sign and the fixed normalization are explicit. There is no Qdot input.
These statements are valid for any measure space, including spatial
reservoirs in each of the permitted dimensions n_d = 1, 2, 3.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- A.3: the actual signed, normalized, finite-volume reaction contribution. -/
noncomputable def physicalSRRegionalReaction
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ) (t : ℝ) : ℝ :=
  (-sign / (gamma10 * R0star)) *
    ((∫ x in region,
        gamma2 t x * R t x * (R t x - Rstar x) ∂μ) / μ.real region)

/-- A.3: the exact physical derivative integrand, prior to spatial integration. -/
def physicalSRReactionRateIntegrand
    {X : Type*}
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  gamma2Rate t x * R t x * (R t x - Rstar x) +
    gamma2 t x * (2 * R t x - Rstar x) * RRate t x

/-- Direct application of the PASSED pointwise product rule at a physical
spatial location; no independent pointwise derivative formula is assumed. -/
theorem physical_sr_reaction_pointwise_derivative
    {X : Type*}
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ) (t : ℝ)
    (hgamma : ∀ x, HasDerivAt (fun τ => gamma2 τ x) (gamma2Rate t x) t)
    (hR : ∀ x, HasDerivAt (fun τ => R τ x) (RRate t x) t) :
    ∀ x, HasDerivAt
      (fun τ => gamma2 τ x * R τ x * (R τ x - Rstar x))
      (physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x) t := by
  intro x
  exact sr_reaction_integrand_hasDerivAt
    (fun τ => gamma2 τ x) (fun τ => R τ x)
    (Rstar x) (gamma2Rate t x) (RRate t x) t
    (hgamma x) (hR x)

/-- The already verified L2 integral is exactly the actual set integral
when its representative agrees almost everywhere with the physical field. -/
theorem physical_sr_reaction_setIntegral_eq_L2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (f : X → ℝ) (F : Lp ℝ 2 μ)
    (hrep : ∀ᵐ x ∂(μ.restrict region), (F x : ℝ) = f x) :
    (∫ x in region, f x ∂μ) =
      ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite F := by
  rw [ReservoirSeismicityControl.well_integral_L2_eq_set_integral]
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  rw [← hx]
  simp [Real.inner_apply]

/-- Differentiate the actual signed SR regional reaction integral, without
postulating the desired regional derivative. The input is the strong L2
regularity of the physical reaction integrand; the continuous L2 integral
has already been proved to commute with differentiation.

`hRateRep` identifies its derivative with A.3's verified product-rule rate.
This is where the physical A3/A7 regularity still has to be supplied. -/
theorem physical_sr_reaction_regional_hasDerivAt
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (F Fdot : ℝ → Lp ℝ 2 μ) (t : ℝ)
    (hrep : ∀ τ, ∀ᵐ x ∂(μ.restrict region),
      ((F τ) x : ℝ) = gamma2 τ x * R τ x * (R τ x - Rstar x))
    (hRateRep : ∀ᵐ x ∂(μ.restrict region),
      ((Fdot t) x : ℝ) =
        physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hF : HasDerivAt F (Fdot t) t) :
    HasDerivAt
      (physicalSRRegionalReaction μ region gamma2 R Rstar
        sign gamma10 R0star)
      ((-sign / (gamma10 * R0star)) *
        ((∫ x in region,
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
          μ.real region)) t := by
  have heq :
      physicalSRRegionalReaction μ region gamma2 R Rstar
          sign gamma10 R0star =
        (fun τ => (-sign / (gamma10 * R0star)) *
          (ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite (F τ) /
            μ.real region)) := by
    funext τ
    simp only [physicalSRRegionalReaction]
    rw [physical_sr_reaction_setIntegral_eq_L2 μ region hs hfinite
      (fun x => gamma2 τ x * R τ x * (R τ x - Rstar x))
      (F τ) (hrep τ)]
  have hRateEq :
      (∫ x in region,
        physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) =
      ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite (Fdot t) :=
    physical_sr_reaction_setIntegral_eq_L2 μ region hs hfinite
      (physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t)
      (Fdot t) hRateRep
  rw [heq, hRateEq]
  exact ((ReservoirSeismicityControl.well_integral_L2_hasDerivAt μ region hs hfinite
    F (Fdot t) t hF).div_const (μ.real region)).const_mul
      (-sign / (gamma10 * R0star))

/-- A.3 regional integral estimate from the actual L2 rate field. This
is Cauchy--Schwarz for a finite-volume region, with the EXACT signed
normalization of (14). It does not require an L-infinity bound on R_t. -/
theorem physical_sr_reaction_regional_rate_bound
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (hpositive : 0 < μ.real region)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (Fdot : Lp ℝ 2 μ) (t C : ℝ)
    (hRateRep : ∀ᵐ x ∂(μ.restrict region),
      (Fdot x : ℝ) =
        physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hL2 : ‖Fdot‖ ≤ C) :
    |(-sign / (gamma10 * R0star)) *
        ((∫ x in region,
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
          μ.real region)| ≤
      |(-sign / (gamma10 * R0star))| *
        (((μ.real region) ^ (1 / (2 : ℝ)) * C) / μ.real region) := by
  rw [physical_sr_reaction_setIntegral_eq_L2 μ region hs hfinite
    (physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t)
    Fdot hRateRep]
  have hmean_abs :
      |ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite Fdot / μ.real region| =
        |ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite Fdot| / μ.real region := by
    rw [abs_div, abs_of_pos hpositive]
  have hfactor : 0 ≤ (μ.real region) ^ (1 / (2 : ℝ)) := by positivity
  have hmean :
      |ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite Fdot| / μ.real region ≤
        ((μ.real region) ^ (1 / (2 : ℝ)) * C) / μ.real region := by
    calc
      _ ≤ ((μ.real region) ^ (1 / (2 : ℝ)) * ‖Fdot‖) / μ.real region :=
        div_le_div_of_nonneg_right
          (ReservoirSeismicityControl.well_integral_L2_bound μ region hs hfinite Fdot)
          hpositive.le
      _ ≤ ((μ.real region) ^ (1 / (2 : ℝ)) * C) / μ.real region :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL2 hfactor) hpositive.le
  calc
    _ = |(-sign / (gamma10 * R0star))| *
        (|ReservoirSeismicityControl.wellIntegralL2 μ region hs hfinite Fdot| / μ.real region) := by
      rw [abs_mul, hmean_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (abs_nonneg _)

/-- On the a.e. regular physical times used in Theorems 1--2, the actual
regional reaction contribution has the signed derivative in A.3 and a
uniform rate bound. No assumption on the DERIVATIVE of the regional
perturbation is present: it is derived from the physical L2 field. -/
theorem physical_sr_reaction_regional_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (hpositive : 0 < μ.real region)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star C : ℝ)
    (F Fdot : ℝ → Lp ℝ 2 μ)
    (hrep : ∀ τ, ∀ᵐ x ∂(μ.restrict region),
      ((F τ) x : ℝ) = gamma2 τ x * R τ x * (R τ x - Rstar x))
    (hRateRep : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂(μ.restrict region),
        ((Fdot t) x : ℝ) =
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hF : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt F (Fdot t) t)
    (hL2 : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Fdot t‖ ≤ C) :
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
          (((μ.real region) ^ (1 / (2 : ℝ)) * C) / μ.real region) := by
  filter_upwards [hRateRep, hF, hL2] with t hRt hFt hBt
  exact ⟨physical_sr_reaction_regional_hasDerivAt μ region hs hfinite
      gamma2 gamma2Rate R RRate Rstar sign gamma10 R0star
      F Fdot t hrep hRt hFt,
    physical_sr_reaction_regional_rate_bound μ region hs hfinite hpositive
      gamma2 gamma2Rate R RRate Rstar sign gamma10 R0star
      (Fdot t) t C hRt hBt⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_pointwise_derivative
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_setIntegral_eq_L2
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_rate_bound
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_ae
