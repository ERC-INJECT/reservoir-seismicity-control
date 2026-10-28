import ReservoirSeismicityControl.PressureIntegratedModes
import ReservoirSeismicityControl.PressureSpectralMultiwell

/-!
# Appendix A.1: from a scalar mild formula to almost-everywhere modal bounds

The pressure mode has an exponentially decaying homogeneous term and a
positive-kernel convolution with each well rate.  For a given time and mode,
write the convolution contributions as `qAverage`.  The actual spectral
pressure and rate satisfy two separate relations:

  lam * mode = -hom + ∑ j, source j * qAverage j,
  rate = -(lam * mode) + ∑ j, source j * qNow j.

Subtracting them yields exactly the modal formula treated in Stage 17.
Consequently a.e. bounds on the current rates and convolution averages imply
the rate bound required by Stage 21, without any derivative of Q.

The mild representation, its positivity/mass estimate, and the a.e. modal
equation are still hypotheses, not yet consequences of the Neumann PDE.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Subtracting the scalar mild pressure identity from its modal evolution
law produces the convolution form of the pressure rate. -/
theorem pressure_mode_mild_ode_identity
    {m : ℕ} (source qNow qAverage : Fin m → ℝ)
    (lam mode hom rate : ℝ)
    (hmild : lam * mode = -hom +
      ∑ j : Fin m, source j * qAverage j)
    (hode : rate = -(lam * mode) +
      ∑ j : Fin m, source j * qNow j) :
    rate = hom +
      ∑ j : Fin m, source j * (qNow j - qAverage j) := by
  classical
  have hsum :
      (∑ j : Fin m, source j * (qNow j - qAverage j)) =
        (∑ j : Fin m, source j * qNow j) -
          (∑ j : Fin m, source j * qAverage j) := by
    calc
      (∑ j : Fin m, source j * (qNow j - qAverage j)) =
          ∑ j : Fin m,
            (source j * qNow j - source j * qAverage j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j : Fin m, source j * qNow j) -
            (∑ j : Fin m, source j * qAverage j) := by
        rw [Finset.sum_sub_distrib]
  calc
    rate = -(lam * mode) + ∑ j : Fin m, source j * qNow j := hode
    _ = hom - (∑ j : Fin m, source j * qAverage j) +
          (∑ j : Fin m, source j * qNow j) := by
      rw [hmild]
      ring
    _ = hom + ∑ j : Fin m, source j * (qNow j - qAverage j) := by
      rw [hsum]
      ring

/-- A single mode's a.e. rate bound, now deduced from separate mild and
modal evolution identities rather than assumed in convolution form. -/
theorem pressure_mode_bound_from_mild_and_ode
    {m : ℕ} (source qNow qAverage M : Fin m → ℝ)
    (lam mode hom init rate : ℝ)
    (hNow : ∀ j : Fin m, |qNow j| ≤ M j)
    (hAverage : ∀ j : Fin m, |qAverage j| ≤ M j)
    (hdecay : |hom| ≤ |init|)
    (hmild : lam * mode = -hom +
      ∑ j : Fin m, source j * qAverage j)
    (hode : rate = -(lam * mode) +
      ∑ j : Fin m, source j * qNow j) :
    |rate| ≤ |init| +
      2 * ∑ j : Fin m, M j * |source j| := by
  exact pressure_spectral_multiwell_mode_from_input_bounds
    source qNow qAverage M hom init rate hNow hAverage hdecay
    (pressure_mode_mild_ode_identity source qNow qAverage lam mode hom rate
      hmild hode)

/-- The convolution and scalar modal identities imply the a.e. rate
estimate needed by the previously verified integrated-mode theorem.
`qAverage` is a positive-kernel average, but its bound must still be shown
from the concrete exponential kernel for the Neumann operator. -/
theorem pressure_multiwell_ae_rate_from_mild_and_ode
    {m : ℕ}
    (mode hom rate : ℕ → ℝ → ℝ)
    (lam init : ℕ → ℝ)
    (source : Fin m → ℕ → ℝ)
    (Q : Fin m → ℝ → ℝ)
    (qAverage : ℕ → Fin m → ℝ → ℝ)
    (M : Fin m → ℝ)
    (hNow : ∀ᵐ t : ℝ ∂volume,
      ∀ j : Fin m, |Q j t| ≤ M j)
    (hAverage : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      ∀ j : Fin m, |qAverage k j t| ≤ M j)
    (hdecay : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      |hom k t| ≤ |init k|)
    (hmild : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      lam k * mode k t = -hom k t +
        ∑ j : Fin m, source j k * qAverage k j t)
    (hode : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      rate k t = -(lam k * mode k t) +
        ∑ j : Fin m, source j k * Q j t) :
    ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      |rate k t| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k| := by
  intro k
  filter_upwards [hNow, hAverage k, hdecay k, hmild k, hode k]
    with t hqt havt hdt hmt hot
  exact pressure_mode_bound_from_mild_and_ode
    (fun j => source j k) (fun j => Q j t)
    (fun j => qAverage k j t) M
    (lam k) (mode k t) (hom k t) (init k) (rate k t)
    hqt havt hdt hmt hot

/-- Combine the a.e. modal bound just derived with Stage 21's integrated
modal identity to obtain the Hilbert-space pressure increment estimate.
This theorem does not assume a bound on Q-dot or a derivative of pressure.
The integrated modal identity, mild formula and modal ODE still have to be
obtained from the actual Neumann diffusion equation. -/
theorem pressure_multiwell_increment_from_mild_and_ode
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) {m : ℕ}
    (pressure : ℝ → H)
    (mode hom rate : ℕ → ℝ → ℝ)
    (lam init : ℕ → ℝ)
    (source : Fin m → ℕ → ℝ)
    (Q : Fin m → ℝ → ℝ)
    (qAverage : ℕ → Fin m → ℝ → ℝ)
    (M : Fin m → ℝ)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hmodal : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
        (b.repr (pressure t - pressure s)) k =
          ∫ τ in s..t, rate k τ)
    (hNow : ∀ᵐ t : ℝ ∂volume,
      ∀ j : Fin m, |Q j t| ≤ M j)
    (hAverage : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      ∀ j : Fin m, |qAverage k j t| ≤ M j)
    (hdecay : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      |hom k t| ≤ |init k|)
    (hmild : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      lam k * mode k t = -hom k t +
        ∑ j : Fin m, source j k * qAverage k j t)
    (hode : ∀ k : ℕ, ∀ᵐ t : ℝ ∂volume,
      rate k t = -(lam k * mode k t) +
        ∑ j : Fin m, source j k * Q j t) :
    ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ‖pressure t - pressure s‖ ^ 2 ≤
        (t - s) ^ 2 *
          (2 * (∑' k : ℕ, (init k) ^ 2) +
            (8 * ∑ j : Fin m, (M j) ^ 2) *
              (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2)) := by
  exact pressure_multiwell_increment_from_integrated_modes
    b pressure (fun τ k => rate k τ) init source M hM hinit hsource
    hmodal (pressure_multiwell_ae_rate_from_mild_and_ode
      mode hom rate lam init source Q qAverage M
      hNow hAverage hdecay hmild hode)

end ReservoirSeismicityControl
