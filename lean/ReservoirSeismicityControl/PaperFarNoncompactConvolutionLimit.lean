import ReservoirSeismicityControl.PaperFarCompactConvolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Block 70 — From compact approximations to a noncompact far-field kernel

This module removes compact support from the *conclusion* of the convolution
integration theorem by applying Mathlib's uniform-limit derivative theorem.

It assumes two approximation properties, rather than differentiability of the
well flux Q:

1. Compactly supported C¹ kernels Kₙ converge in convolution against Q at
   each observation time.
2. Their convolved derivatives converge uniformly in observation time.

For the actual Neumann heat kernel these two convergence properties must be
proved from the off-diagonal short-time and large-time bounds. No conclusion
about the physical Neumann semigroup is claimed here.

The compact approximants are a proof device. The resulting derivative formula
is about the actual, possibly noncompact, kernel K.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter

/-- Differentiation of a convolution with a potentially noncompact kernel.
No derivative of the input Q is assumed. The two convergence hypotheses
identify exactly what still needs to be justified for Neumann kernels. -/
theorem paper_far_noncompact_convolution_limit_hasDerivAt
    (Q K : ℝ → ℝ) (Kn : ℕ → ℝ → ℝ)
    (hQ : LocallyIntegrable Q volume)
    (hcompact : ∀ n : ℕ, HasCompactSupport (Kn n))
    (hsmooth : ∀ n : ℕ, ContDiff ℝ 1 (Kn n))
    (hderivUniform : TendstoUniformly
      (fun n t => ∫ s : ℝ, Q s * deriv (Kn n) (t - s))
      (fun t => ∫ s : ℝ, Q s * deriv K (t - s)) atTop)
    (hvalue : ∀ t : ℝ,
      Tendsto (fun n => ∫ s : ℝ, Q s * Kn n (t - s))
        atTop (nhds (∫ s : ℝ, Q s * K (t - s))))
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s))
      (∫ s : ℝ, Q s * deriv K (t - s)) t := by
  apply hasDerivAt_of_tendstoUniformly hderivUniform
    (Filter.Eventually.of_forall (fun n τ =>
      paper_far_compact_convolution_hasDerivAt
        Q (Kn n) hQ (hcompact n) (hsmooth n) τ)) hvalue t

/-- Express the uniform-limit result using the ordinary derivative. -/
theorem paper_far_noncompact_convolution_limit_deriv
    (Q K : ℝ → ℝ) (Kn : ℕ → ℝ → ℝ)
    (hQ : LocallyIntegrable Q volume)
    (hcompact : ∀ n : ℕ, HasCompactSupport (Kn n))
    (hsmooth : ∀ n : ℕ, ContDiff ℝ 1 (Kn n))
    (hderivUniform : TendstoUniformly
      (fun n t => ∫ s : ℝ, Q s * deriv (Kn n) (t - s))
      (fun t => ∫ s : ℝ, Q s * deriv K (t - s)) atTop)
    (hvalue : ∀ t : ℝ,
      Tendsto (fun n => ∫ s : ℝ, Q s * Kn n (t - s))
        atTop (nhds (∫ s : ℝ, Q s * K (t - s))))
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ s : ℝ, Q s * K (τ - s)) t =
      ∫ s : ℝ, Q s * deriv K (t - s) := by
  exact (paper_far_noncompact_convolution_limit_hasDerivAt
    Q K Kn hQ hcompact hsmooth hderivUniform hvalue t).deriv

/-- The physical reservoir has finitely many wells. Convolution
 differentiation and finite summation commute without differentiating Q_j. -/
theorem paper_far_noncompact_multiwell_limit_hasDerivAt
    {m : ℕ} (Q K : Fin m → ℝ → ℝ)
    (Kn : ℕ → Fin m → ℝ → ℝ)
    (hQ : ∀ j : Fin m, LocallyIntegrable (Q j) volume)
    (hcompact : ∀ n : ℕ, ∀ j : Fin m, HasCompactSupport (Kn n j))
    (hsmooth : ∀ n : ℕ, ∀ j : Fin m, ContDiff ℝ 1 (Kn n j))
    (hderivUniform : ∀ j : Fin m, TendstoUniformly
      (fun n t => ∫ s : ℝ, Q j s * deriv (Kn n j) (t - s))
      (fun t => ∫ s : ℝ, Q j s * deriv (K j) (t - s)) atTop)
    (hvalue : ∀ j : Fin m, ∀ t : ℝ,
      Tendsto (fun n => ∫ s : ℝ, Q j s * Kn n j (t - s))
        atTop (nhds (∫ s : ℝ, Q j s * K j (t - s))))
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∑ j : Fin m,
        ∫ s : ℝ, Q j s * K j (τ - s))
      (∑ j : Fin m,
        ∫ s : ℝ, Q j s * deriv (K j) (t - s)) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact paper_far_noncompact_convolution_limit_hasDerivAt
    (Q j) (K j) (fun n => Kn n j) (hQ j)
    (fun n => hcompact n j) (fun n => hsmooth n j)
    (hderivUniform j) (hvalue j) t

/-- The time-dependent scalar observation weight contributes the usual
product-rule term, while the well fluxes remain undifferentiated. -/
theorem paper_far_noncompact_weighted_multiwell_limit_hasDerivAt
    {m : ℕ} (Q K : Fin m → ℝ → ℝ)
    (Kn : ℕ → Fin m → ℝ → ℝ)
    (hQ : ∀ j : Fin m, LocallyIntegrable (Q j) volume)
    (hcompact : ∀ n : ℕ, ∀ j : Fin m, HasCompactSupport (Kn n j))
    (hsmooth : ∀ n : ℕ, ∀ j : Fin m, ContDiff ℝ 1 (Kn n j))
    (hderivUniform : ∀ j : Fin m, TendstoUniformly
      (fun n t => ∫ s : ℝ, Q j s * deriv (Kn n j) (t - s))
      (fun t => ∫ s : ℝ, Q j s * deriv (K j) (t - s)) atTop)
    (hvalue : ∀ j : Fin m, ∀ t : ℝ,
      Tendsto (fun n => ∫ s : ℝ, Q j s * Kn n j (t - s))
        atTop (nhds (∫ s : ℝ, Q j s * K j (t - s))))
    (w : ℝ → ℝ) (t wrate : ℝ)
    (hw : HasDerivAt w wrate t) :
    HasDerivAt
      (fun τ : ℝ => w τ * ∑ j : Fin m,
        ∫ s : ℝ, Q j s * K j (τ - s))
      (wrate * (∑ j : Fin m,
        ∫ s : ℝ, Q j s * K j (t - s)) +
        w t * (∑ j : Fin m,
        ∫ s : ℝ, Q j s * deriv (K j) (t - s))) t := by
  exact hw.mul (paper_far_noncompact_multiwell_limit_hasDerivAt
    Q K Kn hQ hcompact hsmooth hderivUniform hvalue t)

end ReservoirSeismicityControl
