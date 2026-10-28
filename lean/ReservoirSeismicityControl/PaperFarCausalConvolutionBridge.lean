import ReservoirSeismicityControl.PaperFarSignedConvolutionBridge

/-!
# Stage 64: the causal, frozen-observation-time form of the far-field kernel

Appendix A.3, equation (A11), integrates the *signed* kernel derivative
`K'_{j,t}(t-s)` against the applied well flux `Q_j(s)` over `0 < s ≤ t`.
The extra subscript `t` matters: the SR observation weight `w(t)` changes
with the observation time and is held fixed when the lag is differentiated.

This module specializes the abstract signed-measure bound of Stage 63 to
that exact causal convolution and derives its quantitative a.e. bound.
It does **not** claim the physical Neumann semigroup kernel has the
necessary L¹ bound, nor that differentiation of the physical far
observation yields (A11). Those remain explicit PDE obligations.

No derivative of the applied flux Q occurs in the definitions or hypotheses.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The causal far-field derivative expression (A11) at a fixed observation
    time `t`. In `K` and `KRate`, the observation weight `w(t)` is already
    frozen. `KRate j` denotes differentiation in the *lag*, not in `t`.
    The first argument `initial` also includes any weight-derivative term
    when this expression is used for the derivative of an actual observation. -/
noncomputable def paperFarCausalKernelRate
    {n : ℕ} (t initial : ℝ)
    (K KRate Q : Fin n → ℝ → ℝ) : ℝ :=
  initial + ∑ j : Fin n,
    (-(K j t * Q j 0) +
      ∫ s in Set.Ioc (0 : ℝ) t, KRate j (t - s) * Q j s)

/-- The causal time convolution is exactly Stage 63's signed convolution
    using Lebesgue measure restricted to the past interval. -/
theorem paper_far_causal_rate_eq_signed
    {n : ℕ} (t initial : ℝ)
    (K KRate Q : Fin n → ℝ → ℝ) :
    paperFarCausalKernelRate t initial K KRate Q =
      paperFarSignedKernelRate initial
        (fun j => K j t) (fun j => Q j 0)
        (fun _ => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t))
        (fun j s => KRate j (t - s)) Q := by
  rfl

/-- A causal convolution bound in physical time coordinates. The pointwise
    kernel-value and L¹-lag-derivative bounds are still analytic premises,
    but the measure, integration interval, time reversal, and initial well
    rates are now the concrete quantities of (A11). -/
theorem paper_far_causal_kernel_rate_bound
    {n : ℕ} (t initial : ℝ)
    (K KRate Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hKNow : ∀ j : Fin n, |K j t| ≤ K₀ j)
    (hk : ∀ j : Fin n,
      Integrable (fun s => KRate j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hkMass : ∀ j : Fin n,
      (∫ s in Set.Ioc (0 : ℝ) t, |KRate j (t - s)|) ≤ K₁ j) :
    |paperFarCausalKernelRate t initial K KRate Q| ≤
      |initial| + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  rw [paper_far_causal_rate_eq_signed]
  exact paper_far_signed_kernel_rate_bound
    initial (fun j => K j t) (fun j => Q j 0)
    (fun _ => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t))
    (fun j s => KRate j (t - s)) Q M K₀ K₁
    hM hK₀ (fun j => hQ j 0) hKNow hk hkMass hQ

/-- Almost-everywhere bound when the physical far-field derivative is
    identified with its (A11) causal representation. `K t` and `KRate t`
    are frozen-time kernels; the argument `t-s` is the convolution lag.
    The PDE-to-derivative identification remains a named premise.
    No boundedness assumption on Q' or Q'' is needed. -/
theorem paper_far_actual_derivative_bound_from_causal_kernel_ae
    {n : ℕ} (far initial : ℝ → ℝ)
    (K KRate : ℝ → Fin n → ℝ → ℝ)
    (Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ) (Linit : ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hinit : ∀ᵐ t ∂paperPositiveTime, |initial t| ≤ Linit)
    (hKNow : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, |K t j t| ≤ K₀ j)
    (hk : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n,
        Integrable (fun s => KRate t j (t - s))
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hkMass : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n,
        (∫ s in Set.Ioc (0 : ℝ) t, |KRate t j (t - s)|) ≤ K₁ j)
    (hfarDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt far
        (paperFarCausalKernelRate t (initial t) (K t) (KRate t) Q) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤
        Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  filter_upwards [hinit, hKNow, hk, hkMass, hfarDeriv]
    with t hi hkn hki hmass hderiv
  have hrate := paper_far_causal_kernel_rate_bound
    t (initial t) (K t) (KRate t) Q M K₀ K₁
    hM hK₀ hQ hkn hki hmass
  rw [hderiv.deriv, Real.norm_eq_abs]
  exact hrate.trans (add_le_add_left hi _)

end ReservoirSeismicityControl
