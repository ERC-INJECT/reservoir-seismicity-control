import ReservoirSeismicityControl.PressureSpectralInfinite

/-!
# Appendix A.1 — finitely many well profiles, countably many diffusion modes

This module derives the infinite-mode squared-summability estimate for a
finite family of well profiles. The bound on the derivative of each well rate
is not needed. The explicit spectral formula is *assumed*, not deduced from
the reservoir PDE in this module.

If there are m wells, `source j k` is the k-th eigenfunction coefficient of
well profile j, and `M j` is an absolute bound for its scalar rate Q_j.
The bound is independent of the number of diffusion modes.
-/

namespace ReservoirSeismicityControl

/-- The finite-well pressure-rate modal identity, together with bounds on
both the current well rates and their modal convolution averages, gives a
rate estimate without any Q-dot terms. The convolution bounds are obtained
for actual positive stable kernels by Stage 15. -/
theorem pressure_spectral_multiwell_mode_from_input_bounds
    {m : ℕ}
    (source qNow qAverage M : Fin m → ℝ)
    (hom init rate : ℝ)
    (hNow : ∀ j, |qNow j| ≤ M j)
    (hAverage : ∀ j, |qAverage j| ≤ M j)
    (hdecay : |hom| ≤ |init|)
    (hformula : rate = hom +
      ∑ j : Fin m, source j * (qNow j - qAverage j)) :
    |rate| ≤ |init| + 2 * ∑ j : Fin m, M j * |source j| := by
  classical
  have hterm : ∀ j : Fin m,
      |source j * (qNow j - qAverage j)| ≤
        2 * M j * |source j| := by
    intro j
    have hdiff : |qNow j - qAverage j| ≤ 2 * M j := by
      calc
        |qNow j - qAverage j| ≤ |qNow j| + |qAverage j| := abs_sub _ _
        _ ≤ M j + M j := add_le_add (hNow j) (hAverage j)
        _ = 2 * M j := by ring
    calc
      |source j * (qNow j - qAverage j)| =
          |source j| * |qNow j - qAverage j| := abs_mul _ _
      _ ≤ |source j| * (2 * M j) :=
          mul_le_mul_of_nonneg_left hdiff (abs_nonneg (source j))
      _ = 2 * M j * |source j| := by ring
  have hsum :
      |∑ j : Fin m, source j * (qNow j - qAverage j)| ≤
        ∑ j : Fin m, 2 * M j * |source j| := by
    calc
      |∑ j : Fin m, source j * (qNow j - qAverage j)| ≤
          ∑ j : Fin m, |source j * (qNow j - qAverage j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin m, 2 * M j * |source j| := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j
  calc
    |rate| = |hom + ∑ j : Fin m, source j * (qNow j - qAverage j)| := by
      rw [hformula]
    _ ≤ |hom| + |∑ j : Fin m, source j * (qNow j - qAverage j)| :=
      abs_add_le _ _
    _ ≤ |init| + ∑ j : Fin m, 2 * M j * |source j| :=
      add_le_add hdecay hsum
    _ = |init| + 2 * ∑ j : Fin m, M j * |source j| := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A finite number of square-summable well profiles suffices to establish
square summability of the pressure-rate coefficients. The constant uses the
sum of the squared well-rate bounds and no time derivatives of those rates. -/
theorem pressure_spectral_multiwell_infinite_energy_bound
    {m : ℕ}
    (rate init : ℕ → ℝ) (source : Fin m → ℕ → ℝ)
    (M : Fin m → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hinit : Summable (fun k : ℕ => (init k) ^ 2))
    (hsource : ∀ j : Fin m,
      Summable (fun k : ℕ => (source j k) ^ 2))
    (hmode : ∀ k : ℕ,
      |rate k| ≤ |init k| +
        2 * ∑ j : Fin m, M j * |source j k|) :
    Summable (fun k : ℕ => (rate k) ^ 2) ∧
    (∑' k : ℕ, (rate k) ^ 2) ≤
      2 * (∑' k : ℕ, (init k) ^ 2) +
      (8 * ∑ j : Fin m, (M j) ^ 2) *
        (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2) := by
  classical
  have hsrc : Summable (fun k : ℕ =>
      ∑ j : Fin m, (source j k) ^ 2) := by
    exact summable_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun j k => (source j k) ^ 2)
      (by intro j hj; exact hsource j)
  have hsq : ∀ k : ℕ,
      (rate k) ^ 2 ≤
        2 * (init k) ^ 2 +
          (8 * ∑ j : Fin m, (M j) ^ 2) *
            (∑ j : Fin m, (source j k) ^ 2) := by
    intro k
    have hnonneg : 0 ≤ ∑ j : Fin m, M j * |source j k| := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (hM j) (abs_nonneg _)
    have hmode' :
        |rate k| ≤ |init k| + 2 * (1 : ℝ) *
          abs (∑ j : Fin m, M j * |source j k|) := by
      simpa [abs_of_nonneg hnonneg] using hmode k
    have hfirst := pressure_spectral_mode_square_bound
      (rate k) (init k) (∑ j : Fin m, M j * |source j k|)
      1 (by norm_num) hmode'
    have hcs :
        (∑ j : Fin m, M j * |source j k|) ^ 2 ≤
          (∑ j : Fin m, (M j) ^ 2) *
            (∑ j : Fin m, (source j k) ^ 2) := by
      simpa only [sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq
          (Finset.univ : Finset (Fin m))
          M (fun j => |source j k|))
    nlinarith [hfirst, hcs]
  have hmajor : Summable (fun k : ℕ =>
      2 * (init k) ^ 2 +
        (8 * ∑ j : Fin m, (M j) ^ 2) *
          (∑ j : Fin m, (source j k) ^ 2)) :=
    (hinit.mul_left 2).add
      (hsrc.mul_left (8 * ∑ j : Fin m, (M j) ^ 2))
  have hrate : Summable (fun k : ℕ => (rate k) ^ 2) :=
    hmajor.of_nonneg_of_le (fun k => sq_nonneg (rate k)) hsq
  refine ⟨hrate, ?_⟩
  calc
    (∑' k : ℕ, (rate k) ^ 2) ≤
        ∑' k : ℕ, (2 * (init k) ^ 2 +
          (8 * ∑ j : Fin m, (M j) ^ 2) *
            (∑ j : Fin m, (source j k) ^ 2)) :=
      Summable.tsum_le_tsum hsq hrate hmajor
    _ = 2 * (∑' k : ℕ, (init k) ^ 2) +
          (8 * ∑ j : Fin m, (M j) ^ 2) *
            (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2) := by
      rw [(hinit.mul_left 2).tsum_add
        (hsrc.mul_left (8 * ∑ j : Fin m, (M j) ^ 2))]
      rw [tsum_mul_left, tsum_mul_left]

/-- The same finite-well, infinite-mode estimate holds uniformly in time
when the modal bound holds for all nonnegative times. -/
theorem pressure_spectral_multiwell_uniform_energy_bound
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
      Summable (fun k : ℕ => (rate t k) ^ 2) ∧
      (∑' k : ℕ, (rate t k) ^ 2) ≤
        2 * (∑' k : ℕ, (init k) ^ 2) +
        (8 * ∑ j : Fin m, (M j) ^ 2) *
          (∑' k : ℕ, ∑ j : Fin m, (source j k) ^ 2) := by
  intro t ht
  exact pressure_spectral_multiwell_infinite_energy_bound
    (rate t) init source M hM hinit hsource (hmode t ht)

end ReservoirSeismicityControl
