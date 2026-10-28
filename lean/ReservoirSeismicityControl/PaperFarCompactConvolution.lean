import ReservoirSeismicityControl.PaperFarSignedConvolutionBridge
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Block 70 — Differentiating a smooth truncated far-field convolution

This is a genuine convolution differentiation result, rather than a theorem
assuming the physical observation derivative formula.

Mathlib's convolution differentiation theorem gives, for a locally integrable
input Q and a C¹ compactly supported kernel K,

    d/dt ∫ Q(s) K(t-s) ds = ∫ Q(s) K'(t-s) ds.

No derivative of Q appears. This is the smooth compact-truncation step in a
proof of the causal convolution derivative needed for Appendix A.3.

IMPORTANT: The actual Neumann kernel need not have compact support. Passing
from truncated kernels to the physical kernel requires uniform L¹ bounds,
a limit theorem, and a proof that the physical PDE observation is represented
by that convolution. This file does not claim those steps are complete.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Differentiation falls on the smooth compact kernel, not on the well
input. The input can be discontinuous, provided it is locally integrable.
The formula holds at every observation time. -/
theorem paper_far_compact_convolution_hasDerivAt
    (Q K : ℝ → ℝ)
    (hQ : LocallyIntegrable Q volume)
    (hKcompact : HasCompactSupport K)
    (hKsmooth : ContDiff ℝ 1 K)
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s))
      (∫ s : ℝ, Q s * deriv K (t - s)) t := by
  have h := HasCompactSupport.hasDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hQ hKcompact hKsmooth t
  have hEq :
      (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s)) =
        MeasureTheory.convolution Q K
          (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext τ
    simp only [MeasureTheory.convolution_mul]
  rw [hEq]
  exact h

/-- The genuine derivative, rather than an abstract HasDerivAt premise.
In particular, no time derivative of the applied input Q is required. -/
theorem paper_far_compact_convolution_deriv
    (Q K : ℝ → ℝ)
    (hQ : LocallyIntegrable Q volume)
    (hKcompact : HasCompactSupport K)
    (hKsmooth : ContDiff ℝ 1 K)
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s)) t =
      ∫ s : ℝ, Q s * deriv K (t - s) := by
  exact (paper_far_compact_convolution_hasDerivAt
    Q K hQ hKcompact hKsmooth t).deriv

/-- Combine actual convolution differentiation with the signed-kernel
integral bound from Stage 63. Only an integrable derivative of K and
bounded Q are needed for the quantitative estimate. -/
theorem paper_far_compact_convolution_deriv_bound
    (Q K : ℝ → ℝ)
    (hQloc : LocallyIntegrable Q volume)
    (hKcompact : HasCompactSupport K)
    (hKsmooth : ContDiff ℝ 1 K)
    (M L : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ s : ℝ, |Q s| ≤ M)
    (t : ℝ)
    (hKint : Integrable (fun s : ℝ => deriv K (t - s)) volume)
    (hKmass : (∫ s : ℝ, |deriv K (t - s)|) ≤ L) :
    ‖deriv (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s)) t‖ ≤ M * L := by
  rw [paper_far_compact_convolution_deriv Q K hQloc hKcompact hKsmooth t,
    Real.norm_eq_abs]
  have hbound := paper_far_signed_kernel_rate_bound
    (n := 1) (0 : ℝ)
    (fun _ => 0) (fun _ => 0)
    (fun _ => (volume : Measure ℝ))
    (fun _ s => deriv K (t - s)) (fun _ s => Q s)
    (fun _ => M) (fun _ => 0) (fun _ => L)
    (fun _ => hM) (fun _ => le_refl (0 : ℝ))
    (fun _ => by simpa only [abs_zero] using hM) (fun _ => by simp)
    (fun _ => hKint) (fun _ => hKmass)
    (fun _ s => hQ s)
  have hflip :
      (∫ s : ℝ, Q s * deriv K (t - s)) =
        ∫ s : ℝ, deriv K (t - s) * Q s := by
    apply integral_congr_ae
    filter_upwards [] with s
    exact mul_comm _ _
  rw [hflip]
  simpa [paperFarSignedKernelRate, Fin.sum_univ_one] using hbound

/-- The physical reservoir has finitely many wells. For smooth compact
truncations of their kernels, differentiation commutes with the finite sum.
Again, none of the individual well fluxes needs to be differentiable. -/
theorem paper_far_compact_multiwell_hasDerivAt
    {n : ℕ} (Q K : Fin n → ℝ → ℝ)
    (hQ : ∀ j : Fin n, LocallyIntegrable (Q j) volume)
    (hKcompact : ∀ j : Fin n, HasCompactSupport (K j))
    (hKsmooth : ∀ j : Fin n, ContDiff ℝ 1 (K j))
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∑ j : Fin n,
        ∫ s : ℝ, Q j s * K j (τ - s))
      (∑ j : Fin n,
        ∫ s : ℝ, Q j s * deriv (K j) (t - s)) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact paper_far_compact_convolution_hasDerivAt
    (Q j) (K j) (hQ j) (hKcompact j) (hKsmooth j) t

/-- An additional time-dependent scalar observation weight contributes a
product-rule term. The convolution is differentiated through its KERNEL.
This is a scalar prototype of the time-dependent SR observation weight. -/
theorem paper_far_compact_weighted_multiwell_hasDerivAt
    {n : ℕ} (Q K : Fin n → ℝ → ℝ)
    (hQ : ∀ j : Fin n, LocallyIntegrable (Q j) volume)
    (hKcompact : ∀ j : Fin n, HasCompactSupport (K j))
    (hKsmooth : ∀ j : Fin n, ContDiff ℝ 1 (K j))
    (w : ℝ → ℝ) (t wRate : ℝ)
    (hw : HasDerivAt w wRate t) :
    HasDerivAt
      (fun τ : ℝ => w τ *
        (∑ j : Fin n, ∫ s : ℝ, Q j s * K j (τ - s)))
      (wRate * (∑ j : Fin n,
          ∫ s : ℝ, Q j s * K j (t - s)) +
        w t * (∑ j : Fin n,
          ∫ s : ℝ, Q j s * deriv (K j) (t - s))) t := by
  exact hw.mul (paper_far_compact_multiwell_hasDerivAt
    Q K hQ hKcompact hKsmooth t)

end ReservoirSeismicityControl
