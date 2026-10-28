import ReservoirSeismicityControl.PressureSpectralMultiwell
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Appendix A.1 — reconstruct square-summable pressure-rate coefficients

Stage 17 proves a uniform `tsum` estimate for the modal pressure-rate
coefficients of finitely many bounded wells. This module places those
coefficients in the genuine Hilbert space `ℓ²(ℕ, ℝ)` and transports them
to an abstract real Hilbert space equipped with a `HilbertBasis`.

The Hilbert basis is an explicit hypothesis. We do not yet prove that it is
the Neumann diffusion eigenbasis. Nor do we identify this reconstructed
Hilbert-space vector with the strong or almost-everywhere time derivative
of the actual PDE mild solution.
-/

open scoped lp

namespace ReservoirSeismicityControl

/-- A square-summable real sequence defines an element of the Hilbert
space of square-summable real sequences. -/
noncomputable def pressureRateAsL2
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2)) : ℓ²(ℕ, ℝ) :=
  ⟨rate, by
    apply memℓp_gen
    simpa [Real.norm_eq_abs, sq_abs] using hrate⟩

/-- Parseval identity for the coefficient sequence embedded in ℓ². -/
theorem pressureRateAsL2_energy
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2)) :
    ‖pressureRateAsL2 rate hrate‖ ^ 2 =
      ∑' k : ℕ, (rate k) ^ 2 := by
  have h :
      ‖pressureRateAsL2 rate hrate‖ ^ 2 =
        ∑' k : ℕ, ‖(pressureRateAsL2 rate hrate) k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (p := 2)
        (by norm_num : 0 < (2 : ENNReal).toReal)
        (pressureRateAsL2 rate hrate))
  simpa [pressureRateAsL2, Real.norm_eq_abs, sq_abs] using h

/-- A Hilbert basis reconstructs a Hilbert-space vector from an ℓ²
coefficient sequence. This definition makes no PDE regularity claim. -/
noncomputable def pressureRateInHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2)) : H :=
  b.repr.symm (pressureRateAsL2 rate hrate)

/-- Reconstruction preserves every modal coordinate of the sequence. -/
theorem pressureRateInHilbert_coordinates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2))
    (k : ℕ) :
    (b.repr (pressureRateInHilbert b rate hrate)) k = rate k := by
  simp [pressureRateInHilbert, pressureRateAsL2]

/-- The reconstructed Hilbert-space vector has exactly the same energy
as its square-summable coefficients. -/
theorem pressureRateInHilbert_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (rate : ℕ → ℝ)
    (hrate : Summable (fun k : ℕ => (rate k) ^ 2)) :
    ‖pressureRateInHilbert b rate hrate‖ ^ 2 =
      ∑' k : ℕ, (rate k) ^ 2 := by
  calc
    ‖pressureRateInHilbert b rate hrate‖ ^ 2 =
        ‖pressureRateAsL2 rate hrate‖ ^ 2 := by
          simp [pressureRateInHilbert]
    _ = ∑' k : ℕ, (rate k) ^ 2 :=
      pressureRateAsL2_energy rate hrate

/-- Stage 17's bound reconstructs a uniformly bounded Hilbert vector at
all nonnegative times, assuming a Hilbert basis of the ambient space.

The existential vector is determined by modal coefficients; identifying
it with the physical pressure derivative is still a separate theorem. -/
theorem pressure_spectral_multiwell_hilbert_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    {m : ℕ}
    (rate : ℝ → ℕ → ℝ) (init : ℕ → ℝ)
    (source : Fin m → ℕ → ℝ) (M : Fin m → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hmode : ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ,
      |rate t k| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k|) :
    ∀ t : ℝ, 0 ≤ t →
      ∃ pressureRate : H,
        ‖pressureRate‖ ^ 2 ≤
          2 * (∑' k : ℕ, (init k) ^ 2) +
          (8 * ∑ j : Fin m, (M j) ^ 2) *
            (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2) := by
  intro t ht
  obtain ⟨hsum, hbound⟩ :=
    pressure_spectral_multiwell_uniform_energy_bound
      rate init source M hM hinit hsource hmode t ht
  refine ⟨pressureRateInHilbert b (rate t) hsum, ?_⟩
  rw [pressureRateInHilbert_energy]
  exact hbound

end ReservoirSeismicityControl
