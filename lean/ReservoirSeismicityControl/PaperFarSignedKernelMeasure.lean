import ReservoirSeismicityControl.PaperFarKernelConvolutionBounds
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Stage 62: construct the positive measure from a signed far-field kernel

Stage 61 bounds an integral against a finite positive kernel measure. Here
we construct that measure from an integrable real-valued kernel derivative
`k(s)` using the density `|k(s)|`. We prove its finiteness and its exact
mass, and bound its sign-adjusted well-flux integrand using only `|Q| ≤ M`.
This discharges the *measure finiteness, measure mass, and flux-bound*
premises in Stage 61 when a signed kernel derivative is given.

The pointwise identity `|k| (sgn k) Q = k Q` is also proved. The Bochner
change-of-measure formula for identifying the resulting integral with the
original signed convolution, and the PDE-to-kernel derivative identity,
remain separate obligations. Neither a bound on Q' nor on Q'' is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A positive measure with density equal to the absolute value of a
signed kernel derivative, relative to an arbitrary base measure. For
Appendix A.3 the base measure is Lebesgue measure restricted to `(0,t]`. -/
noncomputable def paperFarAbsoluteKernelMeasure
    (μ : Measure ℝ) (k : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun s => ENNReal.ofReal (|k s|))

/-- Exact total mass of the positive kernel measure. -/
private theorem paper_far_absolute_kernel_mass_ennreal
    (μ : Measure ℝ) (k : ℝ → ℝ)
    (hk : Integrable k μ) :
    paperFarAbsoluteKernelMeasure μ k Set.univ =
      ENNReal.ofReal (∫ s, |k s| ∂μ) := by
  have hnorm : Integrable (fun s => |k s|) μ := by
    simpa only [Real.norm_eq_abs] using hk.norm
  have hnonneg : ∀ᵐ s ∂μ, 0 ≤ |k s| :=
    Filter.Eventually.of_forall (fun s => abs_nonneg (k s))
  calc
    paperFarAbsoluteKernelMeasure μ k Set.univ =
        ∫⁻ s, ENNReal.ofReal (|k s|) ∂μ := by
          simp only [paperFarAbsoluteKernelMeasure,
            withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ENNReal.ofReal (∫ s, |k s| ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hnorm hnonneg).symm

/-- Integrability of the signed kernel derivative automatically makes the
absolute-density measure finite. -/
theorem paper_far_absolute_kernel_finite
    (μ : Measure ℝ) (k : ℝ → ℝ)
    (hk : Integrable k μ) :
    IsFiniteMeasure (paperFarAbsoluteKernelMeasure μ k) := by
  refine ⟨?_⟩
  rw [paper_far_absolute_kernel_mass_ennreal μ k hk]
  exact ENNReal.ofReal_lt_top

/-- Exact real-valued mass of the absolute-density measure. -/
theorem paper_far_absolute_kernel_mass
    (μ : Measure ℝ) (k : ℝ → ℝ)
    (hk : Integrable k μ) :
    (paperFarAbsoluteKernelMeasure μ k).real Set.univ =
      ∫ s, |k s| ∂μ := by
  rw [measureReal_def, paper_far_absolute_kernel_mass_ennreal μ k hk]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun s => abs_nonneg (k s)))

/-- Sign-adjusted well rate. Its absolute value is exactly the absolute
value of the original well rate. -/
noncomputable def paperFarSignAdjustedFlux (k Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  if 0 ≤ k s then Q s else -Q s

theorem paper_far_sign_adjusted_flux_abs
    (k Q : ℝ → ℝ) (s : ℝ) :
    |paperFarSignAdjustedFlux k Q s| = |Q s| := by
  by_cases h : 0 ≤ k s
  · simp [paperFarSignAdjustedFlux, h]
  · simp [paperFarSignAdjustedFlux, h]

/-- The algebra behind the signed-to-positive-kernel representation.
The corresponding integral identity requires a change-of-measure theorem. -/
theorem paper_far_signed_kernel_pointwise
    (k q : ℝ) :
    |k| * (if 0 ≤ k then q else -q) = k * q := by
  by_cases h : 0 ≤ k
  · simp [h, abs_of_nonneg h]
  · have hneg : k < 0 := lt_of_not_ge h
    simp [h, abs_of_neg hneg]

/-- The Stage 61 flux hypothesis follows from the bounded *applied*
well flux. No derivative of that flux occurs. -/
theorem paper_far_sign_adjusted_flux_bound
    (μ : Measure ℝ) (k Q : ℝ → ℝ) (M : ℝ)
    (hQ : ∀ s, |Q s| ≤ M) :
    ∀ᵐ s ∂paperFarAbsoluteKernelMeasure μ k,
      |paperFarSignAdjustedFlux k Q s| ≤ M := by
  exact Filter.Eventually.of_forall (fun s => by
    calc
      |paperFarSignAdjustedFlux k Q s| = |Q s| :=
        paper_far_sign_adjusted_flux_abs k Q s
      _ ≤ M := hQ s)

/-- The Stage 61 finite-well estimate with the positive kernel measures
and the sign-adjusted fluxes now defined from actual signed kernel rates.
Only integrability and an L1 bound on those kernel rates are needed here. -/
theorem paper_far_rate_bound_from_signed_kernel
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
    |paperFarKernelRate initial KNow q0
      (fun j => paperFarAbsoluteKernelMeasure (μ j) (k j))
      (fun j s => paperFarSignAdjustedFlux (k j) (Q j) s)| ≤
      |initial| + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  have hfinite (j : Fin n) :
      IsFiniteMeasure (paperFarAbsoluteKernelMeasure (μ j) (k j)) :=
    paper_far_absolute_kernel_finite (μ j) (k j) (hk j)
  have hmass (j : Fin n) :
      (paperFarAbsoluteKernelMeasure (μ j) (k j)).real Set.univ ≤ K₁ j := by
    rw [paper_far_absolute_kernel_mass (μ j) (k j) (hk j)]
    exact hkMass j
  have hflux (j : Fin n) :
      ∀ᵐ s ∂paperFarAbsoluteKernelMeasure (μ j) (k j),
        |paperFarSignAdjustedFlux (k j) (Q j) s| ≤ M j :=
    paper_far_sign_adjusted_flux_bound (μ j) (k j) (Q j) (M j) (hQ j)
  exact paper_far_kernel_rate_bound initial KNow q0
    (fun j => paperFarAbsoluteKernelMeasure (μ j) (k j))
    (fun j s => paperFarSignAdjustedFlux (k j) (Q j) s)
    M K₀ K₁ hfinite hM hK₀ hq0 hKNow hflux hmass

/-- Almost-everywhere derivative certificate with a signed kernel derivative.
The *physical* far-field derivative formula is still explicitly required.
The measure-theoretic hypotheses of Stage 61 are no longer independent. -/
theorem paper_far_actual_derivative_bound_from_signed_kernel_ae
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
        (paperFarKernelRate (initial t) (KNow t) q0
          (fun j => paperFarAbsoluteKernelMeasure (μ t j) (k t j))
          (fun j s => paperFarSignAdjustedFlux (k t j) (Q t j) s)) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤
        Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  filter_upwards [hinit, hKNow, hk, hkMass, hQ, hfarDeriv]
    with t hi hkn hki hmass hflux hderiv
  have hrate := paper_far_rate_bound_from_signed_kernel
    (initial t) (KNow t) q0 (μ t) (k t) (Q t) M K₀ K₁
    hM hK₀ hq0 hkn hki hmass hflux
  rw [hderiv.deriv, Real.norm_eq_abs]
  exact hrate.trans (add_le_add_left hi _)

end ReservoirSeismicityControl
