import ReservoirSeismicityControl.PressurePositiveSemigroupA5StepLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A5: quantitative L1 stability for the genuine Bochner Duhamel integral

A contraction semigroup defines a time-dependent operator kernel of norm at
most one. Consequently, the associated Bochner forcing integral is Lipschitz
in the scalar input in L1, with constant ‖f‖.

This module proves the actual Bochner-integral estimate and its strong-limit
consequence. It works with any measure space and any time map, including the
backward-time kernel needed for the mild solution.

Explicit integrability hypotheses for the vector-valued integrands remain.
The *separate* outstanding tasks are:
* producing uniformly bounded interval-step approximations to every bounded
  measurable scalar rate, in L1 on a finite interval;
* verifying Bochner integrability and equality of each stepwise sum with its
  Bochner integral;
* identifying the canonical and physical three-dimensional semigroups.

No bounded derivative of a rate, eigenbasis, or compactness assumption appears.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology

section BochnerL1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
variable {α : Type*} [MeasurableSpace α]

/-- A semigroup convolution integral against a scalar rate, written in an
arbitrary time parametrization. For the physical mild formula use the measure
`volume.restrict (Set.Ioc 0 t)` and `τ s = Real.toNNReal (t - s)`.
The scalar rate is **not** assumed differentiable. -/
noncomputable def pressureBochnerForcing
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure α) (τ : α → NNReal) (f : H) (q : α → ℝ) : H :=
  ∫ s, q s • S (τ s) f ∂μ

/-- The Bochner forcing operator is Lipschitz in L1 with the sharp kernel
constant ‖f‖. This result applies to measurable time-varying rates without
assuming any time derivative of q or r. -/
theorem pressure_bochner_forcing_l1_stability
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure α) (τ : α → NNReal) (f : H) (q r : α → ℝ)
    (hq : Integrable q μ) (hr : Integrable r μ)
    (hqv : Integrable (fun s => q s • S (τ s) f) μ)
    (hrv : Integrable (fun s => r s • S (τ s) f) μ) :
    ‖pressureBochnerForcing S μ τ f q - pressureBochnerForcing S μ τ f r‖ ≤
      ∫ s, ‖f‖ * |q s - r s| ∂μ := by
  have hInt : Integrable (fun s => ‖f‖ * |q s - r s|) μ := by
    exact (hq.sub hr).abs.const_mul ‖f‖
  have hMajor : ∀ᵐ s ∂μ,
      ‖(q s - r s) • S (τ s) f‖ ≤ ‖f‖ * |q s - r s| := by
    apply Filter.Eventually.of_forall
    intro s
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |q s - r s| * ‖S (τ s) f‖ ≤ |q s - r s| * ‖f‖ :=
        mul_le_mul_of_nonneg_left (S.norm_apply_le (τ s) f) (abs_nonneg _)
      _ = ‖f‖ * |q s - r s| := mul_comm _ _
  have hSub :
      pressureBochnerForcing S μ τ f q - pressureBochnerForcing S μ τ f r =
        ∫ s, (q s - r s) • S (τ s) f ∂μ := by
    unfold pressureBochnerForcing
    calc
      (∫ s, q s • S (τ s) f ∂μ) - (∫ s, r s • S (τ s) f ∂μ) =
          ∫ s, (q s • S (τ s) f - r s • S (τ s) f) ∂μ :=
        (integral_sub hqv hrv).symm
      _ = ∫ s, (q s - r s) • S (τ s) f ∂μ := by
        congr 1
        funext s
        exact (sub_smul (q s) (r s) (S (τ s) f)).symm
  rw [hSub]
  exact norm_integral_le_of_norm_le hInt hMajor

/-- Convergence of scalar rates in L1 implies *strong* convergence of their
Bochner semigroup forcing terms. This is the convergence needed by the already
verified A5 step-limit theorem. -/
theorem pressure_bochner_forcing_tendsto_of_l1
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure α) (τ : α → NNReal) (f : H)
    (q : ℕ → α → ℝ) (r : α → ℝ)
    (hq : ∀ k, Integrable (q k) μ) (hr : Integrable r μ)
    (hqv : ∀ k, Integrable (fun s => q k s • S (τ s) f) μ)
    (hrv : Integrable (fun s => r s • S (τ s) f) μ)
    (hL1 : Tendsto (fun k => ∫ s, |q k s - r s| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => pressureBochnerForcing S μ τ f (q k)) atTop
      (𝓝 (pressureBochnerForcing S μ τ f r)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hBound (k : ℕ) :
      ‖pressureBochnerForcing S μ τ f (q k) - pressureBochnerForcing S μ τ f r‖ ≤
        ‖f‖ * ∫ s, |q k s - r s| ∂μ := by
    simpa only [integral_const_mul] using
      (pressure_bochner_forcing_l1_stability S μ τ f (q k) r
        (hq k) hr (hqv k) hrv)
  have hMajor :
      Tendsto (fun k => ‖f‖ * ∫ s, |q k s - r s| ∂μ) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hL1) using 1 <;> simp
  exact squeeze_zero
    (fun k => norm_nonneg _)
    hBound hMajor

end BochnerL1

end ReservoirSeismicityControl
