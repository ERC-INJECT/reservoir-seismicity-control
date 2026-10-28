import Mathlib

/-!
# Appendix A.1: the pressure time derivative, spectral route

The Neumann diffusion equation has a fixed, finite collection of spatial well
forcing profiles. For a positive eigenvalue λ, the contribution to λ p_k(t)
from a bounded well rate is the integral of that rate against the nonnegative
kernel λ exp (-λ (t-s)) on [0,t]. This kernel has mass 1-exp(-λt) ≤ 1.

Here we prove the measure-theoretic subprobability estimate, the resulting
single-mode estimate, and an L² energy bound for finitely many modes. No
assumption on the derivative of the input signal is made.

Unproved PDE links: the spectral representation of the actual Neumann operator,
the kernel-mass identity for its eigenvalues, summation over all (infinitely
many) eigenmodes, and compatibility with the model's well profiles. In
particular, this module is NOT a theorem about the full PDE yet.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Integrating a bounded scalar signal against a finite positive measure of
mass at most one cannot increase its absolute bound. The measure models the
stable modal convolution kernel, including the λ=0 case (zero mass). -/
theorem pressure_subprobability_integral_bound
    {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsFiniteMeasure ν]
    (Q : T → ℝ) (M : ℝ)
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M)
    (hM : 0 ≤ M)
    (hmass : ν.real Set.univ ≤ 1) :
    |∫ s, Q s ∂ν| ≤ M := by
  have hQnorm : ∀ᵐ s ∂ν, ‖Q s‖ ≤ M := by
    filter_upwards [hQ] with s hs
    simpa only [Real.norm_eq_abs] using hs
  have hbound : ‖∫ s, Q s ∂ν‖ ≤ M * ν.real Set.univ :=
    norm_integral_le_of_norm_le_const (μ := ν) hQnorm
  have hmassbound : M * ν.real Set.univ ≤ M := by
    have h := mul_nonneg hM (sub_nonneg.mpr hmass)
    nlinarith
  rw [Real.norm_eq_abs] at hbound
  exact hbound.trans hmassbound

/-- Modewise pressure-rate estimate. `hom` is the decaying homogeneous
contribution, `init` is the corresponding initial graph-norm coefficient, and
`ν` is the positive convolution measure for this mode at the selected time.
The precise mild-solution representation is explicitly assumed in `hformula`.
No bound on the time derivative of Q is required. -/
theorem pressure_spectral_mode_rate_bound
    {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsFiniteMeasure ν]
    (Q : T → ℝ) (qNow hom init source rate M : ℝ)
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M)
    (hM : 0 ≤ M)
    (hmass : ν.real Set.univ ≤ 1)
    (hqNow : |qNow| ≤ M)
    (hdecay : |hom| ≤ |init|)
    (hformula : rate = hom + source * (qNow - ∫ s, Q s ∂ν)) :
    |rate| ≤ |init| + 2 * M * |source| := by
  have hfilter : |∫ s, Q s ∂ν| ≤ M :=
    pressure_subprobability_integral_bound ν Q M hQ hM hmass
  have hdiff : |qNow - ∫ s, Q s ∂ν| ≤ 2 * M := by
    calc
      |qNow - ∫ s, Q s ∂ν| ≤ |qNow| + |∫ s, Q s ∂ν| :=
        abs_sub _ _
      _ ≤ M + M := add_le_add hqNow hfilter
      _ = 2 * M := by ring
  have hsource : |source * (qNow - ∫ s, Q s ∂ν)| ≤
      2 * M * |source| := by
    calc
      |source * (qNow - ∫ s, Q s ∂ν)| =
          |source| * |qNow - ∫ s, Q s ∂ν| := abs_mul _ _
      _ ≤ |source| * (2 * M) :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg source)
      _ = 2 * M * |source| := by ring
  calc
    |rate| = |hom + source * (qNow - ∫ s, Q s ∂ν)| := by rw [hformula]
    _ ≤ |hom| + |source * (qNow - ∫ s, Q s ∂ν)| := abs_add_le _ _
    _ ≤ |init| + 2 * M * |source| := add_le_add hdecay hsource

/-- A uniform modewise estimate implies a finite-dimensional L² energy bound.
For a spectral Galerkin truncation, `init` stands for A p(0), `source` for a
fixed well profile, and `rate` for p_t. The constant is intentionally
nonoptimal, avoiding any use of a time derivative of the input. -/
theorem pressure_spectral_finite_energy_bound
    {n : ℕ} (rate init source : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hmode : ∀ k : Fin n,
      |rate k| ≤ |init k| + 2 * M * |source k|) :
    (∑ k : Fin n, (rate k) ^ 2) ≤
      2 * (∑ k : Fin n, (init k) ^ 2) +
      8 * M ^ 2 * (∑ k : Fin n, (source k) ^ 2) := by
  classical
  calc
    (∑ k : Fin n, (rate k) ^ 2) ≤
        ∑ k : Fin n,
          (2 * (init k) ^ 2 + 8 * M ^ 2 * (source k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hterm : 0 ≤ 2 * M * |source k| := by positivity
      have hsum : 0 ≤ |init k| + 2 * M * |source k| :=
        add_nonneg (abs_nonneg _) hterm
      have hsquare : |rate k| ^ 2 ≤
          (|init k| + 2 * M * |source k|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hsum).2 (hmode k)
      have hdouble : 0 ≤ (|init k| - 2 * M * |source k|) ^ 2 :=
        sq_nonneg _
      nlinarith [sq_abs (rate k), sq_abs (init k), sq_abs (source k)]
    _ = 2 * (∑ k : Fin n, (init k) ^ 2) +
        8 * M ^ 2 * (∑ k : Fin n, (source k) ^ 2) := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]

end ReservoirSeismicityControl
