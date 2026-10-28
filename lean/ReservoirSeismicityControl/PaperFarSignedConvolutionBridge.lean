import ReservoirSeismicityControl.PaperFarSignedKernelMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Stage 63: identify the signed convolution with its positive-measure form

Stage 62 constructs the positive finite measure `|k| μ` and the flux
whose sign absorbs the sign of `k`. Stage 63 proves the corresponding
*integral identity*, using Mathlib's Bochner change-of-density theorem.

The final estimates can therefore be stated directly in terms of
`∫ k(s) * Q(s) ∂μ` rather than an abstract positive measure. `k` only
needs to be integrable with respect to the base measure. No derivative
of `Q` appears in any theorem.

What remains: identifying the physical Neumann off-diagonal semigroup
kernel and proving that the far-observation derivative has the signed
kernel expression from Appendix A.3, equation (A11).
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Change of measure from the signed kernel `k` to its absolute-density
measure. Integrability of `k` supplies the required a.e. measurability.
The identity holds for arbitrary `Q`, independently of the derivative
of `Q`. -/
theorem paper_far_signed_kernel_integral
    (μ : Measure ℝ) (k Q : ℝ → ℝ)
    (hk : Integrable k μ) :
    (∫ s, paperFarSignAdjustedFlux k Q s ∂
      paperFarAbsoluteKernelMeasure μ k) =
      ∫ s, k s * Q s ∂μ := by
  have hdensity :
      AEMeasurable (fun s => ENNReal.ofReal (|k s|)) μ :=
    hk.aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal
  have hfinite :
      ∀ᵐ s ∂μ, ENNReal.ofReal (|k s|) < ⊤ :=
    Filter.Eventually.of_forall (fun s => ENNReal.ofReal_lt_top)
  calc
    (∫ s, paperFarSignAdjustedFlux k Q s ∂
      paperFarAbsoluteKernelMeasure μ k) =
        ∫ s, (ENNReal.ofReal (|k s|)).toReal •
          paperFarSignAdjustedFlux k Q s ∂μ := by
            simpa only [paperFarAbsoluteKernelMeasure] using
              (integral_withDensity_eq_integral_toReal_smul₀
                hdensity hfinite (paperFarSignAdjustedFlux k Q))
    _ = ∫ s, k s * Q s ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        -- Expose the beta-reduced integrands before rewriting the density.
        change (ENNReal.ofReal (|k s|)).toReal •
          paperFarSignAdjustedFlux k Q s = k s * Q s
        simpa only [ENNReal.toReal_ofReal (abs_nonneg (k s)),
          smul_eq_mul, paperFarSignAdjustedFlux] using
            (paper_far_signed_kernel_pointwise (k s) (Q s)))

/-- The original signed version of the finite-well far-field expression
in Appendix A.3, equation (A11), with an arbitrary base measure.
When specialized to the physical time variable, `k` represents the
translated derivative of the off-diagonal kernel. -/
noncomputable def paperFarSignedKernelRate
    {n : ℕ} (initial : ℝ) (KNow q0 : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (k Q : Fin n → ℝ → ℝ) : ℝ :=
  initial + ∑ j : Fin n,
    (-(KNow j * q0 j) + ∫ s, k j s * Q j s ∂(μ j))

/-- The rate from the original signed convolution equals the rate
constructed using the positive measures in Stage 62. -/
theorem paper_far_signed_kernel_rate_eq
    {n : ℕ} (initial : ℝ) (KNow q0 : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (k Q : Fin n → ℝ → ℝ)
    (hk : ∀ j : Fin n, Integrable (k j) (μ j)) :
    paperFarSignedKernelRate initial KNow q0 μ k Q =
      paperFarKernelRate initial KNow q0
        (fun j => paperFarAbsoluteKernelMeasure (μ j) (k j))
        (fun j s => paperFarSignAdjustedFlux (k j) (Q j) s) := by
  unfold paperFarSignedKernelRate paperFarKernelRate
  refine congrArg (fun z : ℝ => initial + z) ?_
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ => -(KNow j * q0 j) + z)
    (paper_far_signed_kernel_integral (μ j) (k j) (Q j) (hk j)).symm

/-- Finite-well kernel bound expressed directly with a signed integrand,
no longer requiring the artificial measure or sign-adjusted flux in
the theorem statement. -/
theorem paper_far_signed_kernel_rate_bound
    {n : ℕ} (initial : ℝ) (KNow q0 : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) (k Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hq0 : ∀ j : Fin n, |q0 j| ≤ M j)
    (hKNow : ∀ j : Fin n, |KNow j| ≤ K₀ j)
    (hk : ∀ j : Fin n, Integrable (k j) (μ j))
    (hkMass : ∀ j : Fin n, (∫ s, |k j s| ∂μ j) ≤ K₁ j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j) :
    |paperFarSignedKernelRate initial KNow q0 μ k Q| ≤
      |initial| + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  rw [paper_far_signed_kernel_rate_eq initial KNow q0 μ k Q hk]
  exact paper_far_rate_bound_from_signed_kernel
    initial KNow q0 μ k Q M K₀ K₁
    hM hK₀ hq0 hKNow hk hkMass hQ

/-- A.e. derivative bound expressed in terms of the actual signed
convolution. Only the *PDE-to-kernel derivative identity* is assumed.
Neither bounded `Q'` nor bounded `Q''` is assumed. -/
theorem paper_far_actual_derivative_bound_from_signed_convolution_ae
    {n : ℕ} (far initial : ℝ → ℝ)
    (KNow : ℝ → Fin n → ℝ) (q0 : Fin n → ℝ)
    (μ : ℝ → Fin n → Measure ℝ)
    (k Q : ℝ → Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ) (Linit : ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hq0 : ∀ j : Fin n, |q0 j| ≤ M j)
    (hinit : ∀ᵐ t ∂paperPositiveTime, |initial t| ≤ Linit)
    (hKNow : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, |KNow t j| ≤ K₀ j)
    (hk : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, Integrable (k t j) (μ t j))
    (hkMass : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, (∫ s, |k t j s| ∂μ t j) ≤ K₁ j)
    (hQ : ∀ᵐ t ∂paperPositiveTime,
      ∀ j : Fin n, ∀ s : ℝ, |Q t j s| ≤ M j)
    (hfarDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt far
        (paperFarSignedKernelRate (initial t) (KNow t) q0
          (μ t) (k t) (Q t)) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤
        Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  filter_upwards [hinit, hKNow, hk, hkMass, hQ, hfarDeriv]
    with t hi hkn hki hmass hflux hderiv
  have hrate := paper_far_signed_kernel_rate_bound
    (initial t) (KNow t) q0 (μ t) (k t) (Q t) M K₀ K₁
    hM hK₀ hq0 hkn hki hmass hflux
  rw [hderiv.deriv, Real.norm_eq_abs]
  exact hrate.trans (add_le_add_left hi _)

end ReservoirSeismicityControl
