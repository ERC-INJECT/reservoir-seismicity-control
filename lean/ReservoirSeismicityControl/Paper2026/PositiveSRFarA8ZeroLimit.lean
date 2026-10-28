import ReservoirSeismicityControl.Paper2026.PositiveSRFarA8L1
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

/-!
# P3 / (A8): zero-lag limit and uniform value bound for the physical smooth kernel

This closes the remaining two SCALAR consequences of the published off-diagonal
semigroup envelopes in (A8): the zero-lag limit and the positive-lag value
bound. The existing L¹ theorem supplies the third scalar consequence.

The conditions `hB₀Zero` and `hB₀Bound` identify the exact short-time and
uniform envelopes supplied by the published Davies--Gaffney/spectral-gap
estimates, whose applicability to the physical Neumann generator remains to
be checked. Crucially, we do not assert that the value of the arbitrary
Neumann-orbit extension AT s=0 is zero: the paper means the limit from s>0.
No Qdot hypothesis.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace Topology

/-- The smooth physical SR far kernel vanishes at zero *from the right*,
with its weight frozen at the observation time t. This is the proper
interpretation of `K_j(0)=0` in (A8), since the semigroup orbit is defined
physically only for positive lag. -/
theorem paper_sr_smooth_far_A8_zero_lag
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1)
    (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j s)‖ ≤ B₁ j s)
    (hB₀Zero : ∀ j : Fin n,
      Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    ∀ (t : ℝ) (j : Fin n),
      Tendsto (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t j)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hAll := paper_sr_smooth_far_A8_from_all_well_cutoff
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  intro t j
  have hScaled : Tendsto (fun s : ℝ => Lw * B₀ j s)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (hB₀Zero j))
  apply squeeze_zero_norm' ?_ hScaled
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hb := (hAll.2 t j s hs).1
  change |paperSRFarSmoothKernel μ region hregion Kγ R
    gamma10 R0star cutoff V E hsep orbit t j s| ≤ Lw * B₀ j s at hb
  simpa only [Real.norm_eq_abs] using hb

/-- A8's UNIFORM positive-lag scalar value bound for the very same
smooth physical kernel. The uniform envelope bound is another consequence
of the cited semigroup short/large-time estimates; no separate kernel
boundedness is postulated. -/
theorem paper_sr_smooth_far_A8_value_uniform
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star t)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star t) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1)
    (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j s)‖ ≤ B₁ j s)
    (C₀ : Fin n → ℝ)
    (hB₀Bound : ∀ j : Fin n, ∀ s : ℝ, 0 < s → B₀ j s ≤ C₀ j) :
    ∀ (t : ℝ) (j : Fin n) (s : ℝ), 0 < s →
      let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
        ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
      |paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
        cutoff V E hsep orbit t j s| ≤ Lw * C₀ j := by
  have hAll := paper_sr_smooth_far_A8_from_all_well_cutoff
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  have hMR : 0 ≤ MR := (norm_nonneg (R 0)).trans (hR 0)
  have hbase : 0 ≤ |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hCγ hMR)
  have hLw : 0 ≤ Lw := add_nonneg hbase
    (mul_nonneg (norm_nonneg cutoff) hbase)
  intro t j s hs
  change |paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
    cutoff V E hsep orbit t j s| ≤ Lw * C₀ j
  exact ((hAll.2 t j s hs).1).trans
    (mul_le_mul_of_nonneg_left (hB₀Bound j s hs) hLw)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_zero_lag
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A8_value_uniform
