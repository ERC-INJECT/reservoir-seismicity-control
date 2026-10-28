import ReservoirSeismicityControl.Paper2026.PositiveSRReactionA3Coefficients
import ReservoirSeismicityControl.WellIntegralL2
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: A3 coefficient envelopes in the physical L² space

This is the finite-volume Hölder step, applied to the actual A3 reaction
and rate coefficients. It replaces the freely assumed reaction-value,
coefficient-forcing, and multiplication-operator norm bounds with their
explicit A3/A7 constants. The necessary L² representatives and operator
identifications are retained explicitly, not treated as new PDE assumptions.

The spatial integral and norm are taken over a measurable set of finite
measure, independently of the spatial dimension n_d in {1,2,3}. The rate
multiplier estimate does not assume R_t is essentially bounded.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- Finite-volume L² envelope: the norm of a region-supported field is
controlled by its essential amplitude times the square root of the volume.
Uses Mathlib's already available constant-indicator L² norm identity. -/
theorem physical_sr_indicator_L2_of_ae_bound
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (f : X → ℝ) (F : Lp ℝ 2 μ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrep : ∀ᵐ x ∂μ, (F x : ℝ) = s.indicator f x)
    (hbound : ∀ᵐ x ∂μ, x ∈ s → |f x| ≤ C) :
    ‖F‖ ≤ C * (μ.real s) ^ (1 / (2 : ℝ)) := by
  have hindicator :
      ‖F‖ ≤ ‖indicatorConstLp (2 : ENNReal) hs hfinite C‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hrep, hbound,
      (indicatorConstLp_coeFn (μ := μ) (p := (2 : ENNReal))
        (hs := hs) (hμs := hfinite) (c := C))]
      with x hx hb hind
    rw [hx, hind]
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, Real.norm_eq_abs]
      simpa only [abs_of_nonneg hC] using hb hxs
    · simp only [Set.indicator_of_notMem hxs, norm_zero]
      exact le_rfl
  have hnorm :
      ‖indicatorConstLp (2 : ENNReal) hs hfinite C‖ =
        C * (μ.real s) ^ (1 / (2 : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hC] using
      (MeasureTheory.norm_indicatorConstLp
        (μ := μ) (p := (2 : ENNReal))
        (hs := hs) (hμs := hfinite) (c := C)
        (by norm_num) (by norm_num))
  calc
    ‖F‖ ≤ ‖indicatorConstLp (2 : ENNReal) hs hfinite C‖ := hindicator
    _ = C * (μ.real s) ^ (1 / (2 : ℝ)) := hnorm

/-- The multiplier bound for the physical A.3 product-rule coefficient.
Unlike a pointwise R_t estimate, this works for any L² input. -/
theorem physical_sr_A3_multiplier_opNorm
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (coeff : X → ℝ)
    (K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : ∀ᵐ x ∂μ, x ∈ s → |coeff x| ≤ C)
    (hrep : ∀ f : Lp ℝ 2 μ,
      ∀ᵐ x ∂μ, ((K f) x : ℝ) =
        s.indicator (fun y => coeff y * (f y : ℝ)) x) :
    ‖K‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound K hC
  intro f
  have hpt : ‖K f‖ ≤ ‖C • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hcoeff, hrep f, Lp.coeFn_smul C f]
      with x hc hr hsmul
    rw [hr, hsmul]
    by_cases hxs : x ∈ s
    · simpa [Set.indicator_of_mem hxs, smul_eq_mul,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using
          (mul_le_mul_of_nonneg_right (hc hxs) (abs_nonneg (f x : ℝ)))
    · simp only [Set.indicator_of_notMem hxs, norm_zero]
      exact norm_nonneg _
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hpt

/-- Appendix A.3: A3/A7 pointwise bounds produce the three L² inputs
for the finite-region physical reaction certificate. Only representative
identifications with the actual signed model remain; no separate norm
bounds on F, forcing or K are assumed. -/
theorem physical_sr_A3_actual_reaction_L2_bounds
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (gamma2 gamma2Rate R Rstar : X → ℝ)
    (gamma2M Lgamma2t RM RstarM : ℝ)
    (hgamma2M : 0 ≤ gamma2M) (hLgamma2t : 0 ≤ Lgamma2t)
    (hRM : 0 ≤ RM) (hRstarM : 0 ≤ RstarM)
    (F forcing : Lp ℝ 2 μ)
    (K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hgamma : ∀ᵐ x ∂μ, x ∈ s →
      0 ≤ gamma2 x ∧ gamma2 x ≤ gamma2M ∧
      |gamma2Rate x| ≤ Lgamma2t)
    (hR : ∀ᵐ x ∂μ, x ∈ s → 0 ≤ R x ∧ R x ≤ RM)
    (hRstar : ∀ᵐ x ∂μ, x ∈ s →
      0 ≤ Rstar x ∧ Rstar x ≤ RstarM)
    (hValueRep : ∀ᵐ x ∂μ, (F x : ℝ) =
      s.indicator (fun y =>
        gamma2 y * R y * (R y - Rstar y)) x)
    (hForcingRep : ∀ᵐ x ∂μ, (forcing x : ℝ) =
      s.indicator (fun y =>
        gamma2Rate y * R y * (R y - Rstar y)) x)
    (hMultiplierRep : ∀ f : Lp ℝ 2 μ,
      ∀ᵐ x ∂μ, ((K f) x : ℝ) =
        s.indicator (fun y =>
          gamma2 y * (2 * R y - Rstar y) * (f y : ℝ)) x) :
    ‖F‖ ≤ gamma2M * RM * (RM + RstarM) *
      (μ.real s) ^ (1 / (2 : ℝ)) ∧
    ‖forcing‖ ≤ Lgamma2t * RM * (RM + RstarM) *
      (μ.real s) ^ (1 / (2 : ℝ)) ∧
    ‖K‖ ≤ gamma2M * (2 * RM + RstarM) := by
  have hthree : ∀ᵐ x ∂μ, x ∈ s →
      |gamma2 x * R x * (R x - Rstar x)| ≤
        gamma2M * RM * (RM + RstarM) ∧
      |gamma2Rate x * R x * (R x - Rstar x)| ≤
        Lgamma2t * RM * (RM + RstarM) ∧
      |gamma2 x * (2 * R x - Rstar x)| ≤
        gamma2M * (2 * RM + RstarM) := by
    filter_upwards [hgamma, hR, hRstar] with x hγ hρ hstar hx
    rcases hγ hx with ⟨hγ0, hγM, hγrate⟩
    rcases hρ hx with ⟨hR0, hRM⟩
    rcases hstar hx with ⟨hstar0, hstarM⟩
    exact physical_sr_reaction_A3_three_coefficients
      (gamma2 x) (gamma2Rate x) (R x) (Rstar x)
      gamma2M Lgamma2t RM RstarM
      hγ0 hγM hγrate hR0 hRM hstar0 hstarM
  have hnonneg :
      0 ≤ gamma2M * RM * (RM + RstarM) ∧
      0 ≤ Lgamma2t * RM * (RM + RstarM) ∧
      0 ≤ gamma2M * (2 * RM + RstarM) := by
    constructor
    · positivity
    constructor <;> positivity
  constructor
  · apply physical_sr_indicator_L2_of_ae_bound μ s hs hfinite
      (fun y => gamma2 y * R y * (R y - Rstar y)) F
      (gamma2M * RM * (RM + RstarM)) hnonneg.1 hValueRep
    filter_upwards [hthree] with x hx hxs
    exact (hx hxs).1
  constructor
  · apply physical_sr_indicator_L2_of_ae_bound μ s hs hfinite
      (fun y => gamma2Rate y * R y * (R y - Rstar y)) forcing
      (Lgamma2t * RM * (RM + RstarM)) hnonneg.2.1 hForcingRep
    filter_upwards [hthree] with x hx hxs
    exact (hx hxs).2.1
  · apply physical_sr_A3_multiplier_opNorm μ s
      (fun y => gamma2 y * (2 * R y - Rstar y)) K
      (gamma2M * (2 * RM + RstarM)) hnonneg.2.2
    · filter_upwards [hthree] with x hx hxs
      exact (hx hxs).2.2
    · exact hMultiplierRep

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_indicator_L2_of_ae_bound
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_A3_multiplier_opNorm
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_A3_actual_reaction_L2_bounds
