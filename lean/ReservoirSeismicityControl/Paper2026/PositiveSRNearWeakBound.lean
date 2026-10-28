import ReservoirSeismicityControl.Paper2026.PositiveSRNearFarSplit
import ReservoirSeismicityControl.PressureSymmetricDomain
import Mathlib.Tactic

/-!
# P3, Appendix A.3 — physical near-field transposition and rate estimate

The locally regular near weight is exactly the previously verified
`paperSRNearDiffusionWeight`, i.e. the paper's `ζ χ_VR γ₁ R / (γ₁₀ R₀* |VR|)`.

Published local H² / elliptic regularity is *not* reproved here. Its
applicability is stated explicitly as membership of this particular weight
in the Neumann generator domain and a uniform bound on its generator image.
The diffusion operator remains an unbounded map on its declared submodule.

This module proves the symmetric-domain transposition and bounds the
**right-hand side** of the weak near-field derivative formula in A.3,
using only the already checked L² rate bound of the actual moving weight,
A.1 pressure estimates, and the cited elliptic generator estimate.
The identity asserting that this right-hand side is the derivative of
`⟪ζw, Ap⟫` is still an explicit open weak differentiability obligation.
No derivative of the input Q is assumed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Neumann-domain symmetry applied to the *actual normalized near weight*.
The domain premises are to be discharged by the local H² and cutoff facts
in A.2/A.3 via the cited elliptic result, not by inventing bounded A. -/
theorem paper_sr_near_weight_symmetric_pairing
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : Lp ℝ 2 μ)⟫_ℝ = ⟪(u : Lp ℝ 2 μ), A v⟫_ℝ)
    (pressure : ℝ → Lp ℝ 2 μ) (t : ℝ)
    (hwD : paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t ∈ D)
    (hpD : pressure t ∈ D) :
    ⟪paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t,
      A ⟨pressure t, hpD⟩⟫_ℝ =
    ⟪A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t, hwD⟩,
      pressure t⟫_ℝ := by
  exact (hSymm
    ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t, hwD⟩
    ⟨pressure t, hpD⟩).symm

/-- The actual near-field diffusion observation is uniformly bounded,
using A.3's `‖Ap‖₂` estimate and the PASSED normalized near-weight bound. -/
theorem paper_sr_near_observation_value_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (Ap : ℝ → Lp ℝ 2 μ) (CAp : ℝ)
    (hAp : ∀ t, ‖Ap t‖ ≤ CAp) :
    ∀ t,
      |⟪paperSRNearDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff t, Ap t⟫_ℝ| ≤
        (‖cutoff‖ *
          (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))) * CAp := by
  obtain ⟨hNear, _hFar⟩ :=
    paper_sr_diffusion_near_far_norm_bounds μ region hregion Kγ R Rdot
      gamma10 R0star Cγ CR MR cutoff hCγ hK hR hderiv hrate
  intro t
  let v : Lp ℝ 2 μ :=
    paperSRNearDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t
  have hCS : |⟪v, Ap t⟫_ℝ| ≤ ‖v‖ * ‖Ap t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) v (Ap t))
  have hv : ‖v‖ ≤ ‖cutoff‖ *
      (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR)) := hNear t
  change |⟪v, Ap t⟫_ℝ| ≤ _
  calc
    _ ≤ ‖v‖ * ‖Ap t‖ := hCS
    _ ≤ (‖cutoff‖ *
        (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))) *
        ‖Ap t‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hAp t)
      ((norm_nonneg _).trans hv)

/-- Uniform bound on the weak near-field A.3 derivative *expression*.
The L² derivative of `ζw` is supplied by the PASSED P3 near/far theorem.
The only elliptic input is the stated bound for A applied to that same
physical `ζw` (plus membership in D). Thus no Qdot or Apdot is used.
The weak derivative identity itself is not assumed or claimed. -/
theorem paper_sr_near_weak_rate_rhs_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (hwD : ∀ t, paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t ∈ D)
    (CAw CAp CPt : ℝ)
    (hAw : ∀ t, ‖A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t, hwD t⟩‖ ≤ CAw)
    (Ap pressureRate : ℝ → Lp ℝ 2 μ)
    (hAp : ∀ t, ‖Ap t‖ ≤ CAp)
    (hpRate : ∀ t, ‖pressureRate t‖ ≤ CPt) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |⟪cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
              gamma10 R0star t), Ap t⟫_ℝ +
        ⟪A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff t, hwD t⟩,
          pressureRate t⟫_ℝ| ≤
      (‖cutoff‖ *
        (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR))) * CAp +
        CAw * CPt := by
  obtain ⟨hNearRate, _hFarRate⟩ :=
    paper_sr_diffusion_near_far_rate_bounds μ region hregion Kγ R Rdot
      gamma10 R0star Cγ CR MR cutoff hCγ hK hR hderiv hrate
  filter_upwards [hNearRate] with t hwt
  let v : Lp ℝ 2 μ := cutoff (paperSRDiffusionWeightRate μ region hregion
    Kγ Rdot gamma10 R0star t)
  let z : Lp ℝ 2 μ := A ⟨paperSRNearDiffusionWeight μ region hregion Kγ R
    gamma10 R0star cutoff t, hwD t⟩
  have hfirst : |⟪v, Ap t⟫_ℝ| ≤ ‖v‖ * ‖Ap t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) v (Ap t))
  have hsecond : |⟪z, pressureRate t⟫_ℝ| ≤
      ‖z‖ * ‖pressureRate t‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) z (pressureRate t))
  have hwt' : ‖v‖ ≤ ‖cutoff‖ *
      (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR)) := hwt
  have hfst : ‖v‖ * ‖Ap t‖ ≤
      (‖cutoff‖ *
        (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR))) * CAp := by
    calc
      _ ≤ (‖cutoff‖ *
          (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * CR))) *
          ‖Ap t‖ := mul_le_mul_of_nonneg_right hwt' (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hAp t)
        ((norm_nonneg _).trans hwt')
  have hsnd : ‖z‖ * ‖pressureRate t‖ ≤ CAw * CPt := by
    calc
      _ ≤ CAw * ‖pressureRate t‖ :=
        mul_le_mul_of_nonneg_right (hAw t) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpRate t)
        ((norm_nonneg _).trans (hAw t))
  change |⟪v, Ap t⟫_ℝ + ⟪z, pressureRate t⟫_ℝ| ≤ _
  calc
    _ ≤ |⟪v, Ap t⟫_ℝ| + |⟪z, pressureRate t⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖v‖ * ‖Ap t‖ + ‖z‖ * ‖pressureRate t‖ :=
      add_le_add hfirst hsecond
    _ ≤ _ := add_le_add hfst hsnd

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_weight_symmetric_pairing
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_observation_value_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_near_weak_rate_rhs_bound
