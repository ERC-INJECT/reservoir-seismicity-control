import ReservoirSeismicityControl.PressureSpectralL2

/-!
# Appendix A.1 — Countably many pressure eigenmodes

Extend the finite-mode pressure-rate bound to a countably infinite spectral
family. The summability of the rate is a *conclusion*, not a hypothesis.

The hypotheses represent one fixed spatial forcing profile. To apply the
result to the Neumann diffusion equation, one still has to prove the modal
mild-solution formula and identify the coefficients as the actual spectral
coordinates of `A p(0)` and the well forcing profile.

No bound on the derivative of the well rate is used.
-/

namespace ReservoirSeismicityControl

/-- The scalar modal estimate implies the squared coefficient bound used for
summation over an infinite family of Neumann eigenmodes. -/
theorem pressure_spectral_mode_square_bound
    (rate init source : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmode : |rate| ≤ |init| + 2 * M * |source|) :
    rate ^ 2 ≤ 2 * init ^ 2 + 8 * M ^ 2 * source ^ 2 := by
  have hterm : 0 ≤ 2 * M * |source| := by positivity
  have hsum : 0 ≤ |init| + 2 * M * |source| :=
    add_nonneg (abs_nonneg _) hterm
  have hsquare : |rate| ^ 2 ≤ (|init| + 2 * M * |source|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hsum).2 hmode
  have hdouble : 0 ≤ (|init| - 2 * M * |source|) ^ 2 :=
    sq_nonneg _
  nlinarith [sq_abs rate, sq_abs init, sq_abs source]

/-- Assuming square-summable initial graph-norm coefficients and a fixed
square-summable well forcing profile, the modal pressure-rate coefficients
are themselves square-summable and satisfy a uniform energy estimate.

This proves the *series bound*, but does not by itself identify `rate` with
the time derivative of a mild PDE solution. -/
theorem pressure_spectral_infinite_energy_bound
    (rate init source : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : Summable (fun k : ℕ => (source k) ^ 2))
    (hmode : ∀ k : ℕ,
      |rate k| ≤ |init k| + 2 * M * |source k|) :
    Summable (fun k : ℕ => (rate k) ^ 2) ∧
    (∑' k : ℕ, (rate k) ^ 2) ≤
       2 * (∑' k : ℕ, (init k) ^ 2) +
       8 * M ^ 2 * (∑' k : ℕ, (source k) ^ 2) := by
  have hsq : ∀ k : ℕ,
      (rate k) ^ 2 ≤
        2 * (init k) ^ 2 + (8 * M ^ 2) * (source k) ^ 2 := by
    intro k
    exact pressure_spectral_mode_square_bound (rate k) (init k) (source k)
      M hM (hmode k)
  have hmajor : Summable (fun k : ℕ =>
      2 * (init k) ^ 2 + (8 * M ^ 2) * (source k) ^ 2) :=
    (hinit.mul_left 2).add (hsource.mul_left (8 * M ^ 2))
  have hrate : Summable (fun k : ℕ => (rate k) ^ 2) :=
    hmajor.of_nonneg_of_le (fun k => sq_nonneg (rate k)) hsq
  refine ⟨hrate, ?_⟩
  calc
    (∑' k : ℕ, (rate k) ^ 2) ≤
        ∑' k : ℕ,
          (2 * (init k) ^ 2 + (8 * M ^ 2) * (source k) ^ 2) :=
      Summable.tsum_le_tsum hsq hrate hmajor
    _ = (∑' k : ℕ, 2 * (init k) ^ 2) +
        (∑' k : ℕ, (8 * M ^ 2) * (source k) ^ 2) :=
      (hinit.mul_left 2).tsum_add (hsource.mul_left (8 * M ^ 2))
    _ = 2 * (∑' k : ℕ, (init k) ^ 2) +
        8 * M ^ 2 * (∑' k : ℕ, (source k) ^ 2) := by
      rw [tsum_mul_left, tsum_mul_left]

/-- A single bound holds for every time in the interval, with no time
regularity imposed on the input: the required modal inequalities are assumed
pointwise in time. In applications they must be derived from the mild solution
and interpreted at times where its strong time derivative exists. -/
theorem pressure_spectral_uniform_infinite_energy_bound
    (rate : ℝ → ℕ → ℝ) (init source : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : Summable (fun k : ℕ => (source k) ^ 2))
    (hmode : ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ,
      |rate t k| ≤ |init k| + 2 * M * |source k|) :
    ∀ t : ℝ, 0 ≤ t →
      Summable (fun k : ℕ => (rate t k) ^ 2) ∧
      (∑' k : ℕ, (rate t k) ^ 2) ≤
        2 * (∑' k : ℕ, (init k) ^ 2) +
        8 * M ^ 2 * (∑' k : ℕ, (source k) ^ 2) := by
  intro t ht
  exact pressure_spectral_infinite_energy_bound
    (rate t) init source M hM hinit hsource (hmode t ht)

end ReservoirSeismicityControl
