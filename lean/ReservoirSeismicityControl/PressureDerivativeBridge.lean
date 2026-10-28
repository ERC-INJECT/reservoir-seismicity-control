import ReservoirSeismicityControl.PressureHilbertReconstruction

/-!
# Appendix A.1 — identify the reconstructed spectral vector with a pressure derivative

Stages 15–18 construct, from bounded well rates and a modewise estimate,
a Hilbert-space vector with a uniform energy bound. This module proves the
identification with the strong derivative of a pressure trajectory, PROVIDED
that the trajectory has that derivative and its Fourier coefficients equal
the prescribed modal-rate coefficients.

In particular, it does NOT deduce time differentiability or the Fourier
coefficient equations from the Neumann diffusion PDE. Those are explicit
remaining analytic obligations. A set `Good` allows the derivative condition
to hold only at appropriate times (for example almost everywhere).
-/

namespace ReservoirSeismicityControl

/-- The Fourier coefficients determine a Hilbert-space pressure-rate vector
uniquely. This is an equality in the Hilbert space, not merely a norm bound. -/
theorem pressure_rate_hilbert_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2))
    (v : H)
    (hcoords : ∀ k : ℕ, (b.repr v) k = rate k) :
    v = pressureRateInHilbert b rate hrate := by
  apply b.repr.injective
  ext k
  rw [pressureRateInHilbert_coordinates]
  exact hcoords k

/-- At a time when the pressure has a strong derivative, identifying all
Fourier coefficients of that derivative suffices to identify the derivative
with the vector reconstructed in Stage 18. -/
theorem pressure_rate_hilbert_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (pressure : ℝ → H) (t : ℝ) (v : H)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2))
    (hderiv : HasDerivAt pressure v t)
    (hcoords : ∀ k : ℕ, (b.repr v) k = rate k) :
    HasDerivAt pressure (pressureRateInHilbert b rate hrate) t := by
  have hv : v = pressureRateInHilbert b rate hrate :=
    pressure_rate_hilbert_unique b rate hrate v hcoords
  rw [hv] at hderiv
  exact hderiv

/-- A uniform energy bound for the *actual strong derivative* on an
explicit set of regular times. No bound on derivatives of well rates is
assumed. The `hgood` hypothesis is the outstanding PDE-to-modal bridge.

For inputs that are merely bounded/measurable, `Good` should eventually
be proved to have full measure on the nonnegative half-line; that property
is NOT proved in this module. -/
theorem pressure_rate_hilbert_derivative_uniform
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    {m : ℕ}
    (pressure : ℝ → H)
    (Good : Set ℝ)
    (rate : ℝ → ℕ → ℝ) (init : ℕ → ℝ)
    (source : Fin m → ℕ → ℝ) (M : Fin m → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hmode : ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ,
      |rate t k| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k|)
    (hGood_nonneg : ∀ t : ℝ, t ∈ Good → 0 ≤ t)
    (hgood : ∀ t : ℝ, t ∈ Good →
      ∃ v : H, HasDerivAt pressure v t ∧
        (∀ k : ℕ, (b.repr v) k = rate t k)) :
    ∀ t : ℝ, t ∈ Good →
      ∃ v : H, HasDerivAt pressure v t ∧
        ‖v‖ ^ 2 ≤
          2 * (∑' k : ℕ, (init k) ^ 2) +
          (8 * ∑ j : Fin m, (M j) ^ 2) *
            (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2) := by
  intro t ht
  obtain ⟨v, hv, hcoords⟩ := hgood t ht
  obtain ⟨hsum, hbound⟩ :=
    pressure_spectral_multiwell_uniform_energy_bound
      rate init source M hM hinit hsource hmode t (hGood_nonneg t ht)
  have heq : v = pressureRateInHilbert b (rate t) hsum :=
    pressure_rate_hilbert_unique b (rate t) hsum v hcoords
  refine ⟨v, hv, ?_⟩
  rw [heq, pressureRateInHilbert_energy]
  exact hbound

end ReservoirSeismicityControl
