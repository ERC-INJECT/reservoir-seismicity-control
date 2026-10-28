import ReservoirSeismicityControl.Paper2026.PositiveSRReactionFromEvolution
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: assemble the actual SR reaction over finite output regions

The manuscript passes from the signed reaction integral in each SR output
region to a bound for the finite-dimensional perturbation.  This file proves
that *finite-dimensional passage* for the actual normalized spatial reaction
integrals.  It reuses the locally passed regional L² evolution certificate;
no well-rate derivative, Q̇, off-diagonal estimate, or stability theorem is
introduced here.

The embedding maps are explicit finite-dimensional identifications of the
SR-region components with the output coordinates.  Their identification with
the coordinate injections of equation (14) must still be discharged when the
entire Psi vector is assembled.  The bound on the VALUE of the reaction term
(rather than its derivative) remains an independent A3 applicability check.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped BigOperators

/-- The actual signed SR reaction part of the finite-output perturbation.
The maps `embed` place each physical SR output-region integral into its
corresponding component of the full pressure/SR output vector. -/
noncomputable def physicalSRFiniteReactionPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (t : ℝ) : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r,
    embed i (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
      sign gamma10 R0star t)

/-- Finite-output derivative expression from the exact Appendix A.3
reaction-rate integrand, not an independently postulated rate. -/
noncomputable def physicalSRFiniteReactionRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (t : ℝ) : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r,
    embed i ((-sign / (gamma10 * R0star)) *
      ((∫ x in regions i,
        physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
        μ.real (regions i)))

/-- P3 finite-region assembly: the a.e. signed scalar derivative estimates
imply the corresponding *vector* derivative identity and norm estimate.
This is the precise finite-dimensional step after Appendix A.3's spatial
Hölder estimate. It does not assume a derivative of the vector perturbation. -/
theorem physical_sr_finite_reaction_ae_from_regions
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (Lregion : Fin r → ℝ)
    (hRegions : ∀ i : Fin r, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
          sign gamma10 R0star)
        ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i))) t ∧
      |(-sign / (gamma10 * R0star)) *
        ((∫ x in regions i,
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
          μ.real (regions i))| ≤ Lregion i) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
          sign gamma10 R0star embed)
        (physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate R RRate
          Rstar sign gamma10 R0star embed t) t ∧
      ‖physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate R RRate
          Rstar sign gamma10 R0star embed t‖ ≤
        ∑ i : Fin r, ‖embed i‖ * Lregion i := by
  classical
  have hAll : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ i : Fin r,
        HasDerivAt
          (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
            sign gamma10 R0star)
          ((-sign / (gamma10 * R0star)) *
            ((∫ x in regions i,
              physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
              μ.real (regions i))) t ∧
        |(-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i))| ≤ Lregion i := by
    have hFinite (s : Finset (Fin r)) :
        ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
          ∀ i ∈ s,
            HasDerivAt
              (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
                sign gamma10 R0star)
              ((-sign / (gamma10 * R0star)) *
                ((∫ x in regions i,
                  physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
                  μ.real (regions i))) t ∧
            |(-sign / (gamma10 * R0star)) *
              ((∫ x in regions i,
                physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
                μ.real (regions i))| ≤ Lregion i := by
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with t
          simp
      | @insert a s ha ih =>
          filter_upwards [hRegions a, ih] with t hat hst i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hat
          · exact hst i his
    filter_upwards [hFinite Finset.univ] with t ht i
    exact ht i (Finset.mem_univ i)
  filter_upwards [hAll] with t ht
  have hDeriv (i : Fin r) :
      HasDerivAt
        (fun τ => embed i (physicalSRRegionalReaction μ (regions i)
          gamma2 R Rstar sign gamma10 R0star τ))
        (embed i ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i)))) t :=
    ((embed i).hasFDerivAt.comp_hasDerivAt t (ht i).1)
  have hVector : HasDerivAt
      (physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
        sign gamma10 R0star embed)
      (physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate R RRate
        Rstar sign gamma10 R0star embed t) t := by
    -- Unfold just the two paper-specific finite-region definitions.
    -- This is the standard finite-sum derivative, already used elsewhere
    -- in the ReservoirSeismicityControl Lean project (e.g. PaperPhysicalDemandGainRates).
    change HasDerivAt
      (fun τ => ∑ i : Fin r,
        embed i (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
          sign gamma10 R0star τ))
      (∑ i : Fin r,
        embed i ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i)))) t
    apply HasDerivAt.fun_sum
    intro i _
    exact hDeriv i
  have hRate : ‖physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate
      R RRate Rstar sign gamma10 R0star embed t‖ ≤
      ∑ i : Fin r, ‖embed i‖ * Lregion i := by
    unfold physicalSRFiniteReactionRate
    calc
      ‖∑ i : Fin r, embed i ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i)))‖
        ≤ ∑ i : Fin r, ‖embed i ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i)))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin r, ‖embed i‖ *
          |(-sign / (gamma10 * R0star)) *
            ((∫ x in regions i,
              physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
              μ.real (regions i))| := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Real.norm_eq_abs] using
          (embed i).le_opNorm ((-sign / (gamma10 * R0star)) *
            ((∫ x in regions i,
              physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
              μ.real (regions i)))
      _ ≤ ∑ i : Fin r, ‖embed i‖ * Lregion i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (ht i).2 (norm_nonneg (embed i))
  exact ⟨hVector, hRate⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_regions

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- P3, Appendix A.3: the physical signed SR evolution implies the finite
output-region reaction DERIVATIVE bound. This theorem eliminates the
independently postulated collection of regional reaction-derivative
certificates in `physical_sr_finite_reaction_ae_from_regions` by using the
already proved physical `Rdot` estimate and regional Lebesgue integration.

The product-rule representation/strong-L² regularity and coefficient-rate
forcing/multiplier bounds are explicit remaining A3 applicability checks.
They are NOT premises asserting that the final vector derivative is bounded.
-/
theorem physical_sr_finite_reaction_ae_from_evolution
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hs : ∀ i, MeasurableSet (regions i))
    (hfinite : ∀ i, μ (regions i) ≠ ⊤)
    (hpositive : ∀ i, 0 < μ.real (regions i))
    (gamma2 gamma2Rate R RRate : ℝ → X → ℝ)
    (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (F Fdot forcing : Fin r → ℝ → Lp ℝ 2 μ)
    (Kreact : Fin r → ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Rdot Udot srReaction : ℝ → Lp ℝ 2 μ)
    (Kpressure : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cforcing CreactMultiplier : Fin r → ℝ)
    (Cpressure CU CsrReaction : ℝ)
    (hrep : ∀ i τ, ∀ᵐ x ∂(μ.restrict (regions i)),
      ((F i τ) x : ℝ) = gamma2 τ x * R τ x * (R τ x - Rstar x))
    (hRateRep : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ᵐ x ∂(μ.restrict (regions i)),
        ((Fdot i t) x : ℝ) =
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x)
    (hStrong : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt (F i) (Fdot i t) t)
    (hDecomp : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      Fdot i t = forcing i t + Kreact i t (Rdot t))
    (hForcing : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖forcing i t‖ ≤ Cforcing i)
    (hReactionMultiplier : ∀ i, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Kreact i t‖ ≤ CreactMultiplier i)
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
        (physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
          sign gamma10 R0star embed)
        (physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate R RRate
          Rstar sign gamma10 R0star embed t) t ∧
      ‖physicalSRFiniteReactionRate μ regions gamma2 gamma2Rate R RRate
          Rstar sign gamma10 R0star embed t‖ ≤
        ∑ i : Fin r, ‖embed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((μ.real (regions i)) ^ (1 / (2 : ℝ)) *
              (Cforcing i + CreactMultiplier i *
                (Cpressure * CU + CsrReaction))) / μ.real (regions i))) := by
  have hRegions : ∀ i : Fin r, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
          sign gamma10 R0star)
        ((-sign / (gamma10 * R0star)) *
          ((∫ x in regions i,
            physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
            μ.real (regions i))) t ∧
      |(-sign / (gamma10 * R0star)) *
        ((∫ x in regions i,
          physicalSRReactionRateIntegrand gamma2 gamma2Rate R RRate Rstar t x ∂μ) /
          μ.real (regions i))| ≤
        |(-sign / (gamma10 * R0star))| *
          (((μ.real (regions i)) ^ (1 / (2 : ℝ)) *
            (Cforcing i + CreactMultiplier i *
              (Cpressure * CU + CsrReaction))) / μ.real (regions i)) := by
    intro i
    exact physical_sr_reaction_regional_ae_from_sr_evolution
      μ (regions i) (hs i) (hfinite i) (hpositive i)
      gamma2 gamma2Rate R RRate Rstar
      sign gamma10 R0star
      (F i) (Fdot i) (forcing i) Rdot Udot srReaction
      (Kreact i) Kpressure
      (Cforcing i) (CreactMultiplier i) Cpressure CU CsrReaction
      (hrep i) (hRateRep i) (hStrong i) (hDecomp i)
      (hForcing i) (hReactionMultiplier i)
      hPressureBound hUDotBound hSRReactionBound hSRODE
  exact physical_sr_finite_reaction_ae_from_regions
    μ regions gamma2 gamma2Rate R RRate Rstar sign gamma10 R0star
    embed
    (fun i => |(-sign / (gamma10 * R0star))| *
      (((μ.real (regions i)) ^ (1 / (2 : ℝ)) *
        (Cforcing i + CreactMultiplier i * (Cpressure * CU + CsrReaction))) /
        μ.real (regions i)))
    hRegions

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_ae_from_evolution
