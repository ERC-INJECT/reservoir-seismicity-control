import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9PhysicalInitial
import Mathlib.Tactic

/-!
# P3 / A8 -> A9: physical zero-lag endpoint for causal integration by parts

A8 proves the *right-hand limit* of the actual smooth far kernel, not the
value of an arbitrary semigroup-orbit extension at zero. The integration-by-
parts step in A9 needs a kernel with the specified boundary value K(0)=0.
We explicitly extend the actual frozen-time physical kernel by zero for
nonpositive lag. This leaves every strictly positive lag unchanged and proves
the cancellation of the K(0)Q(t) boundary term for every well.

This is a necessary boundary step, **not** the PDE-to-causal derivative
identity. Published Davies--Gaffney applicability and the near SR weak
product rule remain open. No derivative of Q is introduced.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace Topology

/-- The canonical causal extension of a positive-lag scalar kernel. -/
noncomputable def paperA9ZeroLagExtension (K : ℝ → ℝ) (lag : ℝ) : ℝ :=
  if lag ≤ 0 then 0 else K lag

/-- The extension agrees exactly with the semigroup kernel for lag > 0. -/
theorem paper_A9_zero_extension_positive (K : ℝ → ℝ) {lag : ℝ}
    (hlag : 0 < lag) : paperA9ZeroLagExtension K lag = K lag := by
  simp [paperA9ZeroLagExtension, not_le.mpr hlag]

/-- The physical boundary value is zero regardless of the arbitrary orbit
extension at lag 0. -/
theorem paper_A9_zero_extension_at_zero (K : ℝ → ℝ) :
    paperA9ZeroLagExtension K 0 = 0 := by
  simp [paperA9ZeroLagExtension]

/-- The right-sided limit from A8 becomes the right continuity of this
chosen causal extension at the endpoint. -/
theorem paper_A9_zero_extension_tendsto (K : ℝ → ℝ)
    (hK : Tendsto K (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (paperA9ZeroLagExtension K)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have heq : (paperA9ZeroLagExtension K) =ᶠ[𝓝[>] (0 : ℝ)] K := by
    filter_upwards [self_mem_nhdsWithin] with lag hlag
    exact paper_A9_zero_extension_positive K hlag
  exact hK.congr' heq.symm

/-- The K(0) Q(t) endpoint in the finite-well integration-by-parts
formula cancels exactly, without differentiating the flux Q. -/
theorem paper_A9_zero_extension_finite_well_boundary
    {n : ℕ} (K : Fin n → ℝ → ℝ) (Q : Fin n → ℝ → ℝ) (t : ℝ) :
    (∑ j : Fin n, paperA9ZeroLagExtension (K j) 0 * Q j t) = 0 := by
  simp [paper_A9_zero_extension_at_zero]

/-- Strictly causal time-lags preserve the original physical kernel. -/
theorem paper_A9_zero_extension_causal_interior
    (K : ℝ → ℝ) (t s : ℝ) (hs : s < t) :
    paperA9ZeroLagExtension K (t - s) = K (t - s) := by
  exact paper_A9_zero_extension_positive K (sub_pos.mpr hs)

/-- Specialize the endpoint construction to the actual normalized smooth
SR kernel and derive its limit directly from the already verified A8 theorem;
there is no independently postulated K(0)=0 property. -/
theorem paper_sr_smooth_far_A9_zero_boundary
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
    ∀ (observation : ℝ) (j : Fin n),
      paperA9ZeroLagExtension
        (paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
          cutoff V E hsep orbit observation j) 0 = 0 ∧
      Tendsto (paperA9ZeroLagExtension
        (paperSRFarSmoothKernel μ region hregion Kγ R gamma10 R0star
          cutoff V E hsep orbit observation j))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hzero := paper_sr_smooth_far_A8_zero_lag
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond hB₀Zero
  intro observation j
  exact ⟨paper_A9_zero_extension_at_zero _,
    paper_A9_zero_extension_tendsto _ (hzero observation j)⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_positive
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_at_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_tendsto
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_finite_well_boundary
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_zero_extension_causal_interior
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_zero_boundary
