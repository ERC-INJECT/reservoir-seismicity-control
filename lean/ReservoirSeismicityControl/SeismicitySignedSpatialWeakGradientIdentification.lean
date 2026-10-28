import ReservoirSeismicityControl.SeismicitySignedSpatialWeakPairing
import ReservoirSeismicityControl.PressureNeumann3DDistributionalTests
import Mathlib.Tactic

/-!
# M1 — Identification of a spatial weak gradient from approximants

We already have the exact spatial difference-quotient integration by parts
identity for the *constructed signed reciprocal* Y.  The missing Sobolev
step is to identify weak L² limits of regularized/difference-quotient
fields as actual distributional derivatives.

This module proves a useful three-dimensional Hilbert-space closure step:

* strongly converging L² scalar approximants u_n;
* weakly converging L² vector-gradient approximants g_n;
* an exact weak integration-by-parts identity for each approximant;
* a common L² bound for the approximate gradients;

imply that the limiting pair belongs to the **already verified physical
3D distributional weak-gradient graph** and that the gradient obeys the
same bound.  Weak convergence is sufficient; strong convergence of the
gradients is NOT required.

The weak limit of gradient approximants and their IBP properties are
explicit premises.  The module does NOT establish extraction of that weak
subsequence from spatial difference-quotient estimates, nor identify the
physical reciprocal's first/second derivatives automatically.  Those
remain parts of the M1 local H²(U_j) obligation.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- Strong L² convergence on the scalar component, together with weak
convergence on all vector tests, preserves the integration-by-parts
identity.  The lemma works without a strong convergence hypothesis on
the gradient approximants. -/
theorem sr_spatial_weak_IBP_identification
    {H K Φ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [AddCommGroup Φ] [Module ℝ Φ]
    (embed : Φ →ₗ[ℝ] K) (negDiv : Φ →ₗ[ℝ] H)
    (u : ℕ → H) (g : ℕ → K) (uLimit : H) (gLimit : K)
    (hu : Tendsto u atTop (𝓝 uLimit))
    (hgWeak : ∀ v : K,
      Tendsto (fun n : ℕ => ⟪v, g n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ))
    (hIBP : ∀ n : ℕ, ∀ φ : Φ,
      ⟪embed φ, g n⟫_ℝ = ⟪negDiv φ, u n⟫_ℝ) :
    ∀ φ : Φ,
      ⟪embed φ, gLimit⟫_ℝ = ⟪negDiv φ, uLimit⟫_ℝ := by
  intro φ
  have hEq :
      (fun n : ℕ => ⟪embed φ, g n⟫_ℝ) =
        (fun n : ℕ => ⟪negDiv φ, u n⟫_ℝ) := by
    funext n
    exact hIBP n φ
  have hRight :
      Tendsto (fun n : ℕ => ⟪embed φ, g n⟫_ℝ)
        atTop (𝓝 ⟪negDiv φ, uLimit⟫_ℝ) := by
    rw [hEq]
    have hContinuous : Continuous (fun z : H => ⟪negDiv φ, z⟫_ℝ) := by
      fun_prop
    exact (hContinuous.tendsto uLimit).comp hu
  exact tendsto_nhds_unique (hgWeak (embed φ)) hRight

/-- Weak Hilbert-space limits preserve a uniform norm bound, without
requiring norm convergence or a strong gradient subsequence. -/
theorem sr_spatial_weak_gradient_norm_bound
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : ℕ → K) (gLimit : K) (M : ℝ)
    (hgWeak : ∀ v : K,
      Tendsto (fun n : ℕ => ⟪v, g n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ))
    (hBound : ∀ n : ℕ, ‖g n‖ ≤ M) :
    ‖gLimit‖ ≤ M := by
  have hM : 0 ≤ M :=
    (norm_nonneg (g 0)).trans (hBound 0)
  have hPoint (n : ℕ) :
      ⟪gLimit, g n⟫_ℝ ≤ M * ‖gLimit‖ := by
    calc
      ⟪gLimit, g n⟫_ℝ ≤ ‖gLimit‖ * ‖g n‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖gLimit‖ * M :=
        mul_le_mul_of_nonneg_left (hBound n) (norm_nonneg _)
      _ = M * ‖gLimit‖ := mul_comm _ _
  have hLimit : ⟪gLimit, gLimit⟫_ℝ ≤ M * ‖gLimit‖ :=
    le_of_tendsto (hgWeak gLimit) (Filter.Eventually.of_forall hPoint)
  rw [real_inner_self_eq_norm_sq] at hLimit
  by_cases hZero : ‖gLimit‖ = 0
  · simpa only [hZero] using hM
  · have hPos : 0 < ‖gLimit‖ :=
      lt_of_le_of_ne (norm_nonneg gLimit) (Ne.symm hZero)
    by_contra hNot
    have hGt : M < ‖gLimit‖ := lt_of_not_ge hNot
    have hProd : 0 < (‖gLimit‖ - M) * ‖gLimit‖ :=
      mul_pos (sub_pos.mpr hGt) hPos
    nlinarith

/-- **Physical 3D specialization:** approximate reciprocal fields with
an exact weak gradient equation yield a legitimate L² distributional
gradient on the reservoir domain.  The uniform bound passes to the limit.

To apply this to the signed reciprocal Y, the first quotient formulas and
weak pairings must still be used to build the approximants and prove weak
compactness.  No gradient of Y is postulated in this statement. -/
theorem sr_signed_3d_weak_gradient_graph_of_approximants
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
    {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (u : ℕ → pressureNeumann3DScalarL2 Ω μ)
    (g : ℕ → pressureNeumann3DVectorL2 Ω μ)
    (uLimit : pressureNeumann3DScalarL2 Ω μ)
    (gLimit : pressureNeumann3DVectorL2 Ω μ)
    (M : ℝ)
    (hu : Tendsto u atTop (𝓝 uLimit))
    (hgWeak : ∀ v : pressureNeumann3DVectorL2 Ω μ,
      Tendsto (fun n : ℕ => ⟪v, g n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ))
    (hIBP : ∀ n : ℕ, ∀ φ : Φ,
      ⟪embed φ, g n⟫_ℝ = ⟪negDiv φ, u n⟫_ℝ)
    (hBound : ∀ n : ℕ, ‖g n‖ ≤ M) :
    (WithLp.toLp 2 (uLimit, gLimit) :
      WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ)) ∈
        pressureNeumann3DTestGraph μ embed negDiv ∧
      ‖gLimit‖ ≤ M := by
  constructor
  · apply (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv
      (WithLp.toLp 2 (uLimit, gLimit))).2
    intro φ
    change ⟪embed φ, gLimit⟫_ℝ = ⟪negDiv φ, uLimit⟫_ℝ
    exact sr_spatial_weak_IBP_identification
      embed negDiv u g uLimit gLimit hu hgWeak hIBP φ
  · exact sr_spatial_weak_gradient_norm_bound g gLimit M hgWeak hBound

#print axioms ReservoirSeismicityControl.sr_spatial_weak_IBP_identification
#print axioms ReservoirSeismicityControl.sr_spatial_weak_gradient_norm_bound
#print axioms ReservoirSeismicityControl.sr_signed_3d_weak_gradient_graph_of_approximants

end ReservoirSeismicityControl
