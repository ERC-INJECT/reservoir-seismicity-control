import ReservoirSeismicityControl.PaperRegionalPerturbationComponents
import ReservoirSeismicityControl.PressureSpectralL2

/-!
# Stage 61: far-field kernel convolution bound, without a derivative of Q

Appendix A.3, equation (A11), has three contributions: an initial term,
a boundary term `-K_j(t) Q_j(0)`, and the convolution of `K'_j`
with bounded well rates. After absorbing the sign of `K'_j` into the
integrand, the last integral is an integral against a *positive* measure
whose density is `|K'_j(t-s)|`. Its total mass is controlled by
`∫ |K'_j|`.

This module proves the quantitative bound on that expression for finitely
many wells, including an almost-everywhere derivative certificate.
It never assumes a bound on Q' or Q''.

What is NOT proved here: the Davies--Gaffney off-diagonal estimate for the
physical Neumann operator, the identification of the positive kernel
measures with its `K'_j`, or the fact that the physical far observation
has derivative (A11). Those PDE-to-kernel hypotheses remain explicit.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- At one time and for one well, a bounded weighted well rate integrated
against a positive kernel measure is controlled by the kernel's L1 mass.
The `Q` argument may incorporate the sign of the original kernel derivative. -/
theorem paper_far_kernel_integral_bound
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (Q : ℝ → ℝ) (M K₁ : ℝ)
    (hM : 0 ≤ M)
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M)
    (hmass : ν.real Set.univ ≤ K₁) :
    |∫ s, Q s ∂ν| ≤ M * K₁ := by
  have hQnorm : ∀ᵐ s ∂ν, ‖Q s‖ ≤ M := by
    filter_upwards [hQ] with s hs
    simpa only [Real.norm_eq_abs] using hs
  have hbound : ‖∫ s, Q s ∂ν‖ ≤ M * ν.real Set.univ :=
    norm_integral_le_of_norm_le_const (μ := ν) hQnorm
  rw [Real.norm_eq_abs] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hmass hM)

/-- The three parts of (A11), for one well. No well-rate derivative is
needed to bound this expression once the kernel representation holds. -/
theorem paper_far_kernel_one_well_bound
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (Q : ℝ → ℝ) (initial KNow q0 M K₀ K₁ : ℝ)
    (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀)
    (hq0 : |q0| ≤ M)
    (hKNow : |KNow| ≤ K₀)
    (hQ : ∀ᵐ s ∂ν, |Q s| ≤ M)
    (hmass : ν.real Set.univ ≤ K₁) :
    |initial - KNow * q0 + ∫ s, Q s ∂ν| ≤
      |initial| + M * (K₀ + K₁) := by
  have hkernel : |KNow * q0| ≤ K₀ * M := by
    calc
      |KNow * q0| = |KNow| * |q0| := abs_mul _ _
      _ ≤ K₀ * |q0| :=
        mul_le_mul_of_nonneg_right hKNow (abs_nonneg _)
      _ ≤ K₀ * M := mul_le_mul_of_nonneg_left hq0 hK₀
  have hint : |∫ s, Q s ∂ν| ≤ M * K₁ :=
    paper_far_kernel_integral_bound ν Q M K₁ hM hQ hmass
  calc
    |initial - KNow * q0 + ∫ s, Q s ∂ν| ≤
        |initial - KNow * q0| + |∫ s, Q s ∂ν| := abs_add_le _ _
    _ ≤ (|initial| + |KNow * q0|) + |∫ s, Q s ∂ν| :=
      add_le_add_left (abs_sub _ _) _
    _ ≤ |initial| + M * (K₀ + K₁) := by
      nlinarith [hkernel, hint]

/-- The far-field derivative expression (A11), represented using one
positive weighted kernel measure per well. -/
noncomputable def paperFarKernelRate
    {n : ℕ} (initial : ℝ) (KNow q0 : Fin n → ℝ)
    (ν : Fin n → Measure ℝ) (Q : Fin n → ℝ → ℝ) : ℝ :=
  initial + ∑ j : Fin n,
    (-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j))

/-- Quantitative bound for the actual finite-well expression in (A11).
`ν j` represents the positive measure with density `|K'_j|` at the
selected observation time. `Q j` represents its sign-weighted well rate.
The measure construction and its mass bound are separate PDE obligations. -/
theorem paper_far_kernel_rate_bound
    {n : ℕ} (initial : ℝ) (KNow q0 : Fin n → ℝ)
    (ν : Fin n → Measure ℝ) (Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ)
    (hνfinite : ∀ j : Fin n, IsFiniteMeasure (ν j))
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hq0 : ∀ j : Fin n, |q0 j| ≤ M j)
    (hKNow : ∀ j : Fin n, |KNow j| ≤ K₀ j)
    (hQ : ∀ j : Fin n, ∀ᵐ s ∂(ν j), |Q j s| ≤ M j)
    (hmass : ∀ j : Fin n, (ν j).real Set.univ ≤ K₁ j) :
    |paperFarKernelRate initial KNow q0 ν Q| ≤
      |initial| + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  classical
  have hterm (j : Fin n) :
      |-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j)| ≤
        M j * (K₀ j + K₁ j) := by
    letI : IsFiniteMeasure (ν j) := hνfinite j
    have hj := paper_far_kernel_one_well_bound
      (ν j) (Q j) 0 (KNow j) (q0 j) (M j) (K₀ j) (K₁ j)
      (hM j) (hK₀ j) (hq0 j) (hKNow j) (hQ j) (hmass j)
    simpa only [zero_sub, zero_add, abs_zero] using hj
  have hsum :
      |∑ j : Fin n, (-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j))| ≤
        ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
    calc
      _ ≤ ∑ j : Fin n,
          |-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j
  calc
    |paperFarKernelRate initial KNow q0 ν Q| =
        |initial + ∑ j : Fin n,
          (-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j))| := rfl
    _ ≤ |initial| +
        |∑ j : Fin n, (-(KNow j * q0 j) + ∫ s, Q j s ∂(ν j))| :=
          abs_add_le _ _
    _ ≤ |initial| + ∑ j : Fin n, M j * (K₀ j + K₁ j) :=
      add_le_add_right hsum _

/-- Uniform a.e. bound for the *classical derivative* of a scalar far-well
observation, when the PDE has supplied the exact (A11) derivative formula.
Unlike the earlier abstract Stage 60 bound, its numerical constant is
derived directly from bounded Q, pointwise kernel values, and L1 kernel
masses. The PDE-to-kernel derivative formula remains a stated premise. -/
theorem paper_far_actual_derivative_bound_from_kernel_formula_ae
    {n : ℕ} (far initial : ℝ → ℝ)
    (KNow : ℝ → Fin n → ℝ) (q0 : Fin n → ℝ)
    (ν : ℝ → Fin n → Measure ℝ)
    (Q : ℝ → Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ) (Linit : ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hq0 : ∀ j : Fin n, |q0 j| ≤ M j)
    (hinit : ∀ᵐ t ∂paperPositiveTime, |initial t| ≤ Linit)
    (hνfinite : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, IsFiniteMeasure (ν t j))
    (hKNow : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, |KNow t j| ≤ K₀ j)
    (hQ : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, ∀ᵐ s ∂(ν t j), |Q t j s| ≤ M j)
    (hmass : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, (ν t j).real Set.univ ≤ K₁ j)
    (hfarDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt far
        (paperFarKernelRate (initial t) (KNow t) q0 (ν t) (Q t)) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤
        Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  filter_upwards [hinit, hνfinite, hKNow, hQ, hmass, hfarDeriv]
    with t hi hfin hk hq hm hd
  have hb := paper_far_kernel_rate_bound
    (initial t) (KNow t) q0 (ν t) (Q t) M K₀ K₁
    hfin hM hK₀ hq0 hk hq hm
  rw [hd.deriv, Real.norm_eq_abs]
  exact hb.trans (add_le_add_left hi _)

end ReservoirSeismicityControl
