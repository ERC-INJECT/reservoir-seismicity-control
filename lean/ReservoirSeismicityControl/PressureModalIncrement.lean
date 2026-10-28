import ReservoirSeismicityControl.PressureDerivativeBridge

/-!
# Appendix A.1 — Hilbert-space increments from modal secant estimates

This module avoids assuming that the pressure trajectory has a strong time
 derivative at every instant. A Hilbert basis identifies a pressure increment
from its modal coefficients. If the *secant* coefficients obey the same
uniform multiwell estimate as the modal-rate coefficients in Stage 17, the
pressure trajectory satisfies a uniform quadratic Lipschitz estimate.

The modal SECANT estimate and its derivation from the Neumann diffusion PDE
with bounded measurable Q are NOT proved here. In the PDE, obtaining this
estimate requires proving absolute continuity of the scalar modal
trajectories and integrating their a.e. derivatives. An abstract Hilbert
basis is assumed, not constructed from the Neumann operator.
-/

namespace ReservoirSeismicityControl

/-- A pressure increment is the time increment times the Hilbert vector
reconstructed from its secant Fourier coefficients. In particular, this
identification does not assume that the pressure derivative exists. -/
theorem pressure_modal_increment_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (pressure : ℝ → H) (s t : ℝ)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2))
    (hcoords : ∀ k : ℕ,
      (b.repr (pressure t - pressure s)) k = (t - s) * rate k) :
    pressure t - pressure s =
      (t - s) • pressureRateInHilbert b rate hrate := by
  apply b.repr.injective
  ext k
  calc
    (b.repr (pressure t - pressure s)) k = (t - s) * rate k := hcoords k
    _ = (b.repr ((t - s) • pressureRateInHilbert b rate hrate)) k := by
      simp [pressureRateInHilbert_coordinates]

/-- Parseval for the increment, conditional only on its modal secant
coefficient identity (not on differentiability of the trajectory). -/
theorem pressure_modal_increment_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (pressure : ℝ → H) (s t : ℝ)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2))
    (hcoords : ∀ k : ℕ,
      (b.repr (pressure t - pressure s)) k = (t - s) * rate k) :
    ‖pressure t - pressure s‖ ^ 2 =
      (t - s) ^ 2 * (∑' k : ℕ, (rate k) ^ 2) := by
  calc
    ‖pressure t - pressure s‖ ^ 2 =
        ‖(t - s) • pressureRateInHilbert b rate hrate‖ ^ 2 := by
      rw [pressure_modal_increment_eq b pressure s t rate hrate hcoords]
    _ = (t - s) ^ 2 * ‖pressureRateInHilbert b rate hrate‖ ^ 2 := by
      rw [norm_smul, mul_pow]
      simp only [Real.norm_eq_abs, sq_abs]
    _ = (t - s) ^ 2 * (∑' k : ℕ, (rate k) ^ 2) := by
      rw [pressureRateInHilbert_energy]

/-- A uniform bound on all modal secant coefficients gives a uniform
Hilbert-space quadratic Lipschitz bound for the actual pressure trajectory.
No `HasDerivAt` assumption appears here. The hypotheses `hcoords` and
`hmode` must still be justified for the Neumann PDE, using the scalar modal
mild solutions and bounded (not differentiable) well rates. -/
theorem pressure_multiwell_increment_energy_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    {m : ℕ}
    (pressure : ℝ → H)
    (rate : ℝ → ℝ → ℕ → ℝ)
    (init : ℕ → ℝ)
    (source : Fin m → ℕ → ℝ)
    (M : Fin m → ℝ)
    (hM : ∀ j : Fin m, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hcoords : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
        (b.repr (pressure t - pressure s)) k =
          (t - s) * rate s t k)
    (hmode : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ∀ k : ℕ,
        |rate s t k| ≤ |init k| +
          2 * ∑ j : Fin m, M j * |source j k|) :
    ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
      ‖pressure t - pressure s‖ ^ 2 ≤
        (t - s) ^ 2 *
          (2 * (∑' k : ℕ, (init k) ^ 2) +
            (8 * ∑ j : Fin m, (M j) ^ 2) *
              (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2)) := by
  intro s hs t ht
  obtain ⟨hrate, hbound⟩ :=
    pressure_spectral_multiwell_infinite_energy_bound
      (rate s t) init source M hM hinit hsource (hmode s hs t ht)
  calc
    ‖pressure t - pressure s‖ ^ 2 =
        (t - s) ^ 2 * (∑' k : ℕ, (rate s t k) ^ 2) :=
      pressure_modal_increment_energy b pressure s t (rate s t) hrate
        (hcoords s hs t ht)
    _ ≤ (t - s) ^ 2 *
          (2 * (∑' k : ℕ, (init k) ^ 2) +
            (8 * ∑ j : Fin m, (M j) ^ 2) *
              (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg (t - s))

end ReservoirSeismicityControl
