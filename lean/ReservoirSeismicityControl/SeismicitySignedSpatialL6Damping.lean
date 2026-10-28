import ReservoirSeismicityControl.SeismicitySignedSpatialFirstQuotientBarrier
import ReservoirSeismicityControl.SeismicitySignedSpatialH2Bootstrap
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# M1 — Spatially varying positive damping is a contraction on L⁶(U_j)

This module removes the *pointwise-in-space forcing bound* previously used
by the first-quotient comparison theorem.  The coefficient a(x,t)=γ₂R* satisfies a≥aMin>0. Factoring the deterministic kernel
exp(-aMin*(t-v)) from the actual propagator leaves a residual spatial
factor bounded pointwise by one. Multiplication by this (spatially varying) factor is therefore a
contraction on the genuine spatial L⁶ quotient space, not just on scalar
trajectories.

Combining this contraction with the previously VERIFIED exponentially
weighted Bochner convolution yields a uniform-in-time L⁶ estimate under
L∞_t L⁶_x forcing bounds. There is NO requirement for L∞_x derivatives
of a or b and no control-input derivative.

The final theorem assumes the exact L⁶-valued Duhamel representation of
the physical first difference quotient and spatial measurability of the
integrating factor. Establishing that identification from the pointwise
Caratheodory formula (and local H² coefficient bounds) remains an open M1
bridge; it is NOT silently treated as proved here.

The sign s=±1 is absorbed in b=γ₂ exp(s γ₁u); neither the contraction
nor the time kernel depends on the sign.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The Banach-space structure of `Lp ℝ 6 μ` requires `1 ≤ 6`.
    Keep this numeric instance local to the signed spatial L⁶ module. -/
private instance : Fact ((1 : ENNReal) ≤ (6 : ENNReal)) := ⟨by norm_num⟩

/-- The exact spatially dependent damping factor for the linear reciprocal
ODE, extended symmetrically outside the physical time triangle to keep it
between zero and one for all pairs of times. In the physical case 0≤v≤t,
its exponent is precisely -∫_v^t (a(x,τ)-aMin)dτ, the
residual damping after factoring out exp(-aMin*(t-v)). -/
noncomputable def srSignedSpatialDamping
    {Ω : Type*} (a : Ω → ℝ → ℝ) (aMin t v : ℝ) (x : Ω) : ℝ :=
  Real.exp (-(∫ τ in (min v t)..(max v t), a x τ - aMin))

/-- The lower coefficient bound a≥aMin implies the *actual spatially varying*
propagator has absolute value ≤1. No pointwise bounds on spatial
derivatives of a are needed. -/
theorem sr_signed_spatial_damping_abs_le_one
    {Ω : Type*} (a : Ω → ℝ → ℝ)
    (aMin : ℝ)
    (ha : ∀ x : Ω, ∀ τ : ℝ, aMin ≤ a x τ)
    (t v : ℝ) (x : Ω) :
    |srSignedSpatialDamping a aMin t v x| ≤ 1 := by
  have hminmax : min v t ≤ max v t :=
    (min_le_left v t).trans (le_max_left v t)
  have hIntegral :
      0 ≤ ∫ τ in (min v t)..(max v t), a x τ - aMin := by
    apply intervalIntegral.integral_nonneg hminmax
    intro τ _
    exact sub_nonneg.mpr (ha x τ)
  unfold srSignedSpatialDamping
  rw [abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(∫ τ in (min v t)..(max v t), a x τ - aMin)) ≤
        Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hIntegral)
    _ = 1 := Real.exp_zero

/-- A bounded measurable spatial multiplier preserves the genuine L⁶
space. This constructs the result as an Lp equivalence class. -/
private theorem sr_signed_spatial_L6_damping_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (hpMeas : AEStronglyMeasurable p μ)
    (hpBound : ∀ᵐ x ∂μ, |p x| ≤ 1)
    (f : Lp ℝ (6 : ENNReal) μ) :
    MemLp (fun x : Ω => p x * (f x : ℝ)) (6 : ENNReal) μ := by
  have hMeas : AEStronglyMeasurable
      (fun x : Ω => p x * (f x : ℝ)) μ :=
    hpMeas.mul (Lp.aestronglyMeasurable f)
  apply (Lp.memLp f).of_le_mul hMeas
  filter_upwards [hpBound] with x hx
  calc
    ‖p x * (f x : ℝ)‖ = |p x| * ‖(f x : ℝ)‖ := by
      rw [norm_mul, Real.norm_eq_abs]
    _ ≤ 1 * ‖(f x : ℝ)‖ :=
      mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- The concrete spatial damping multiplier acting on L⁶ classes. -/
noncomputable def srSignedSpatialL6Multiplier
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (hpMeas : AEStronglyMeasurable p μ)
    (hpBound : ∀ᵐ x ∂μ, |p x| ≤ 1)
    (f : Lp ℝ (6 : ENNReal) μ) : Lp ℝ (6 : ENNReal) μ :=
  MemLp.toLp (fun x : Ω => p x * (f x : ℝ))
    (sr_signed_spatial_L6_damping_memLp μ p hpMeas hpBound f)

/-- The concrete multiplier is a contraction in *spatial L⁶ norm*;
this is stronger than a pointwise scalar comparison and does not assume
that forcing has any pointwise spatial uniform bound. -/
theorem sr_signed_spatial_L6_multiplier_norm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (hpMeas : AEStronglyMeasurable p μ)
    (hpBound : ∀ᵐ x ∂μ, |p x| ≤ 1)
    (f : Lp ℝ (6 : ENNReal) μ) :
    ‖srSignedSpatialL6Multiplier μ p hpMeas hpBound f‖ ≤ ‖f‖ := by
  have hRep :
      (srSignedSpatialL6Multiplier μ p hpMeas hpBound f : Ω → ℝ)
        =ᵐ[μ] (fun x : Ω => p x * (f x : ℝ)) :=
    MemLp.coeFn_toLp
      (sr_signed_spatial_L6_damping_memLp μ p hpMeas hpBound f)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hRep, hpBound] with x hx hp
  rw [hx]
  calc
    ‖p x * (f x : ℝ)‖ = |p x| * ‖(f x : ℝ)‖ := by
      rw [norm_mul, Real.norm_eq_abs]
    _ ≤ 1 * ‖(f x : ℝ)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ‖(f x : ℝ)‖ := one_mul _

/-- Actual spatially varying propagator, with its bound *derived* from
a≥aMin. The only measurability input is spatial measurability of the
integrating factor; its pointwise contraction is not a separate premise. -/
theorem sr_signed_spatial_L6_physical_damping_contraction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : Ω → ℝ → ℝ)
    (aMin : ℝ)
    (ha : ∀ x : Ω, ∀ τ : ℝ, aMin ≤ a x τ)
    (t v : ℝ)
    (hpMeas : AEStronglyMeasurable (srSignedSpatialDamping a aMin t v) μ)
    (f : Lp ℝ (6 : ENNReal) μ) :
    ‖srSignedSpatialL6Multiplier μ
      (srSignedSpatialDamping a aMin t v) hpMeas
      (Filter.Eventually.of_forall
        (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) f‖ ≤ ‖f‖ := by
  exact sr_signed_spatial_L6_multiplier_norm_le μ
    (srSignedSpatialDamping a aMin t v) hpMeas
    (Filter.Eventually.of_forall
      (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) f

set_option maxHeartbeats 1000000

/-- This is the exact missing *spatial L⁶* variant of the first-quotient
barrier: a nonconstant-in-space residual propagator with positive damping,
uniform L⁶ forcing, and an exponentially weighted time integral.

The physical Duhamel equality is stated explicitly: its construction
from the verified pointwise Carathéodory quotient is still outstanding.
In particular, the theorem does NOT require |D_h a|≤A₁ pointwise in x. -/
theorem sr_signed_spatial_first_quotient_uniform_L6_of_Duhamel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : Ω → ℝ → ℝ) (aMin : ℝ)
    (ha : ∀ x : Ω, ∀ τ : ℝ, aMin ≤ a x τ)
    (hpMeas : ∀ t v : ℝ,
      AEStronglyMeasurable (srSignedSpatialDamping a aMin t v) μ)
    (G0 Fmax : ℝ)
    (haMin : 0 < aMin) (hFmax : 0 ≤ Fmax)
    (z zHom F : ℝ → Lp ℝ (6 : ENNReal) μ)
    (hHom : ∀ t : ℝ, 0 ≤ t → ‖zHom t‖ ≤ G0)
    (hF : ∀ v : ℝ, 0 ≤ v → ‖F v‖ ≤ Fmax)
    (hSupport : ∀ t : ℝ, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t, 0 ≤ v)
    (hDuhamel : ∀ t : ℝ, 0 ≤ t →
      z t = zHom t + aMin⁻¹ •
        (∫ v, srSignedSpatialL6Multiplier μ
          (srSignedSpatialDamping a aMin t v) (hpMeas t v)
          (Filter.Eventually.of_forall
            (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) (F v)
          ∂pressureExponentialKernelMeasure aMin t)) :
    ∀ t : ℝ, 0 ≤ t → ‖z t‖ ≤ G0 + Fmax / aMin := by
  intro t ht
  have hIntegratorBound :
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        ‖srSignedSpatialL6Multiplier μ
          (srSignedSpatialDamping a aMin t v) (hpMeas t v)
          (Filter.Eventually.of_forall
            (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) (F v)‖ ≤ Fmax := by
    filter_upwards [hSupport t ht] with v hv
    exact (sr_signed_spatial_L6_physical_damping_contraction
      μ a aMin ha t v (hpMeas t v) (F v)).trans (hF v hv)
  have hConvolution := sr_damped_bochner_convolution_norm_le
    aMin t Fmax haMin ht hFmax
    (fun v => srSignedSpatialL6Multiplier μ
      (srSignedSpatialDamping a aMin t v) (hpMeas t v)
      (Filter.Eventually.of_forall
        (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) (F v))
    hIntegratorBound
  calc
    ‖z t‖ = ‖zHom t + aMin⁻¹ •
      (∫ v, srSignedSpatialL6Multiplier μ
        (srSignedSpatialDamping a aMin t v) (hpMeas t v)
        (Filter.Eventually.of_forall
          (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) (F v)
        ∂pressureExponentialKernelMeasure aMin t)‖ := by
          rw [hDuhamel t ht]
    _ ≤ ‖zHom t‖ + ‖aMin⁻¹ •
      (∫ v, srSignedSpatialL6Multiplier μ
        (srSignedSpatialDamping a aMin t v) (hpMeas t v)
        (Filter.Eventually.of_forall
          (sr_signed_spatial_damping_abs_le_one a aMin ha t v)) (F v)
        ∂pressureExponentialKernelMeasure aMin t)‖ := norm_add_le _ _
    _ ≤ G0 + Fmax / aMin :=
      add_le_add (hHom t ht) hConvolution

#print axioms ReservoirSeismicityControl.sr_signed_spatial_damping_abs_le_one
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_multiplier_norm_le
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_physical_damping_contraction
#print axioms ReservoirSeismicityControl.sr_signed_spatial_first_quotient_uniform_L6_of_Duhamel

end ReservoirSeismicityControl
