import ReservoirSeismicityControl.PressureModalIncrement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Appendix A.1 — modal secants from integrated rate equations

At a fixed mode, the scalar identity
  p_k(t) - p_k(s) = ∫ τ in s..t, v_k(τ)
plus an almost-everywhere bound on v_k controls the difference quotient.
No pointwise differentiability of p_k and no derivative of the well rates
are used. Combining the bound with the Hilbert-space result from Stage 20
gives a pressure increment estimate.

The integrated modal identities and a.e. bounds are still *hypotheses* here.
They must be derived for the Neumann PDE with bounded measurable well rates.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A real integrand uniformly bounded in absolute value almost everywhere
has interval integral bounded by the interval length times that constant.
This applies to measurable bounded forcing, including jump discontinuities. -/
theorem pressure_interval_integral_bound_ae
    (rate : ℝ → ℝ) (s t C : ℝ)
    (hbound : ∀ᵐ τ : ℝ ∂volume, |rate τ| ≤ C) :
    |∫ τ in s..t, rate τ| ≤ C * |t - s| := by
  have hnorm : ∀ᵐ τ : ℝ ∂volume,
      τ ∈ Set.uIoc s t → ‖rate τ‖ ≤ C := by
    filter_upwards [hbound] with τ hτ
    intro _
    simpa only [Real.norm_eq_abs] using hτ
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := s) (b := t) (C := C) hnorm)

/-- A single integrated modal equation yields a time-increment bound,
without requiring a derivative of the modal trajectory. -/
theorem pressure_modal_increment_from_integrated_rate
    (mode rate : ℝ → ℝ) (s t C : ℝ)
    (hinc : mode t - mode s = ∫ τ in s..t, rate τ)
    (hbound : ∀ᵐ τ : ℝ ∂volume, |rate τ| ≤ C) :
    |mode t - mode s| ≤ C * |t - s| := by
  rw [hinc]
  exact pressure_interval_integral_bound_ae rate s t C hbound

/-- The Fourier-coordinate secant of the actual Hilbert-space increment.
When s=t it is defined as zero. -/
noncomputable def pressureModalSecant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (pressure : ℝ → H)
    (s t : ℝ) (k : ℕ) : ℝ :=
  if t = s then 0 else (b.repr (pressure t - pressure s)) k / (t - s)

/-- Definition of the secant gives the exact coordinate identity used
in Stage 20, even when the two times coincide. -/
theorem pressure_modal_secant_coordinates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (pressure : ℝ → H)
    (s t : ℝ) (k : ℕ) :
    (b.repr (pressure t - pressure s)) k =
      (t - s) * pressureModalSecant b pressure s t k := by
  by_cases hts : t = s
  · subst t
    simp [pressureModalSecant]
  · have hdiff : t - s ≠ (0 : ℝ) := sub_ne_zero.mpr hts
    simp only [pressureModalSecant, if_neg hts]
    field_simp [hdiff]

/-- Integrated modal identity and a.e. rate bound give the secant bound.
No differentiability of the pressure curve is assumed. -/
theorem pressure_modal_secant_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (pressure : ℝ → H)
    (rate : ℝ → ℝ) (s t C : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hinc : (b.repr (pressure t - pressure s)) k =
      ∫ τ in s..t, rate τ)
    (hbound : ∀ᵐ τ : ℝ ∂volume, |rate τ| ≤ C) :
    |pressureModalSecant b pressure s t k| ≤ C := by
  by_cases hts : t = s
  · simp [pressureModalSecant, hts, hC]
  · have hdiff : t - s ≠ (0 : ℝ) := sub_ne_zero.mpr hts
    have habs : 0 < |t - s| := abs_pos.mpr hdiff
    have hincrement :
        |(b.repr (pressure t - pressure s)) k| ≤ C * |t - s| := by
      rw [hinc]
      exact pressure_interval_integral_bound_ae rate s t C hbound
    have hquot :
        |(b.repr (pressure t - pressure s)) k / (t - s)| ≤ C := by
      rw [abs_div]
      exact (div_le_iff₀ habs).2 hincrement
    simpa [pressureModalSecant, hts] using hquot

/-- The Stage 20 Hilbert-space Lipschitz estimate, now with hypotheses
formulated as integrated modal equations and a.e. modal-rate bounds.
The abstract modal secant estimate is *derived*, not hypothesized.
The PDE still needs to supply the integrated modal equations. -/
theorem pressure_multiwell_increment_from_integrated_modes
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) {m : ℕ}
    (pressure : ℝ → H)
    (modalRate : ℝ → ℕ → ℝ)
    (init : ℕ → ℝ) (source : Fin m → ℕ → ℝ)
    (M : Fin m → ℝ)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hmodal : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
        (b.repr (pressure t - pressure s)) k =
          ∫ τ in s..t, modalRate τ k)
    (hrate : ∀ k : ℕ, ∀ᵐ τ : ℝ ∂volume,
      |modalRate τ k| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k|) :
    ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ‖pressure t - pressure s‖ ^ 2 ≤
        (t - s) ^ 2 *
          (2 * (∑' k : ℕ, (init k) ^ 2) +
            (8 * ∑ j : Fin m, (M j) ^ 2) *
              (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2)) := by
  classical
  let secant : ℝ → ℝ → ℕ → ℝ :=
    fun s t k => pressureModalSecant b pressure s t k
  have hcoords : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
      (b.repr (pressure t - pressure s)) k = (t - s) * secant s t k := by
    intro s hs t ht k
    exact pressure_modal_secant_coordinates b pressure s t k
  have hmode : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
      |secant s t k| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k| := by
    intro s hs t ht k
    have hterm : 0 ≤ ∑ j : Fin m, M j * |source j k| := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (hM j) (abs_nonneg _)
    have hC : 0 ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k| := by
      exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hterm)
    exact pressure_modal_secant_bound b pressure (fun τ => modalRate τ k)
      s t _ k hC (hmodal s hs t ht k) (hrate k)
  exact pressure_multiwell_increment_energy_bound b pressure secant
    init source M hM hinit hsource hcoords hmode

end ReservoirSeismicityControl
