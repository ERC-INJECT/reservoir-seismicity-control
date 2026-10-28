import ReservoirSeismicityControl.SeismicitySignedSpatialWeakGradientIdentification
import Mathlib.Tactic

/-!
# M1 — Weak spatial gradient obtained from reciprocal difference quotients

Earlier verified modules prove an exact translation/weak-pairing identity
for the *constructed signed reciprocal* Y(x,t), and the closedness of the
physical three-dimensional weak-gradient test graph. The preceding gradient
identification module required each approximate gradient already to satisfy
an integration-by-parts identity for an approximate scalar solution.

Here we remove that extra approximation requirement. The scalar field Y is
FIXED throughout; the prospective gradient fields are its spatial
**difference quotients**. The test-side differences approach minus divergence.
Thus the graph membership of the limiting pair follows directly from the
discrete quotient identity, without postulating a gradient for Y or for a
smoothed solution.

The proof is an exact Hilbert-space limit argument and preserves the uniform
L² quotient bound. To instantiate this theorem for the physical signed SR,
one must still construct L² representatives of the coordinate quotients,
prove their uniform spatial bounds (using the previously verified quotient
ODE and Hessian-forcing bounds), obtain a weak limit, and prove the test-side
translation quotient converges to the negative divergence. These are *not*
asserted as completed here. The result applies to either sign s = ±1.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- A sequence of (directional) spatial difference quotients of a *fixed*
scalar L² field identifies a distributional derivative as soon as the
quotients converge weakly and the translated-test differences converge
strongly. No spatial derivative or approximation sequence for the scalar
field is assumed. -/
theorem sr_spatial_weak_derivative_from_discrete_pairings
    {H K Φ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [AddCommGroup Φ] [Module ℝ Φ]
    (embed : Φ →ₗ[ℝ] K)
    (negDiv : Φ →ₗ[ℝ] H)
    (discreteNegDiv : ℕ → Φ → H)
    (Y : H) (quotient : ℕ → K) (gLimit : K)
    (hPair : ∀ n : ℕ, ∀ φ : Φ,
      ⟪embed φ, quotient n⟫_ℝ = ⟪discreteNegDiv n φ, Y⟫_ℝ)
    (hTestLimit : ∀ φ : Φ,
      Tendsto (fun n : ℕ => discreteNegDiv n φ) atTop
        (𝓝 (negDiv φ)))
    (hQuotientWeak : ∀ v : K,
      Tendsto (fun n : ℕ => ⟪v, quotient n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ)) :
    ∀ φ : Φ,
      ⟪embed φ, gLimit⟫_ℝ = ⟪negDiv φ, Y⟫_ℝ := by
  intro φ
  have hEqual :
      (fun n : ℕ => ⟪embed φ, quotient n⟫_ℝ) =
      (fun n : ℕ => ⟪discreteNegDiv n φ, Y⟫_ℝ) := by
    funext n
    exact hPair n φ
  have hRight :
      Tendsto (fun n : ℕ => ⟪embed φ, quotient n⟫_ℝ) atTop
        (𝓝 ⟪negDiv φ, Y⟫_ℝ) := by
    rw [hEqual]
    have hContinuous : Continuous (fun z : H => ⟪z, Y⟫_ℝ) := by
      fun_prop
    exact (hContinuous.tendsto (negDiv φ)).comp (hTestLimit φ)
  exact tendsto_nhds_unique (hQuotientWeak (embed φ)) hRight

/-- The quantitative bound on an identified difference-quotient limit
is the *same* as the uniform L² bound of the quotients. -/
theorem sr_spatial_weak_derivative_bound_from_quotients
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (quotient : ℕ → K) (gLimit : K) (M : ℝ)
    (hQuotientWeak : ∀ v : K,
      Tendsto (fun n : ℕ => ⟪v, quotient n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ))
    (hBound : ∀ n : ℕ, ‖quotient n‖ ≤ M) :
    ‖gLimit‖ ≤ M := by
  exact sr_spatial_weak_gradient_norm_bound
    quotient gLimit M hQuotientWeak hBound

/-- Concrete three-dimensional L² version for a fixed reciprocal field
on a well neighborhood U_j. This delivers the physical distributional
gradient-graph membership and the quantitative norm bound, replacing the
prior requirement that all gradient approximants themselves satisfy
continuous IBP.  Its only IBP hypothesis is the **discrete** quotient/test
identity, the type of identity proved by the spatial weak-pairing module. -/
theorem sr_signed_3d_gradient_graph_from_reciprocal_quotients
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
    {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (discreteNegDiv : ℕ → Φ → pressureNeumann3DScalarL2 Ω μ)
    (Y : pressureNeumann3DScalarL2 Ω μ)
    (quotient : ℕ → pressureNeumann3DVectorL2 Ω μ)
    (gLimit : pressureNeumann3DVectorL2 Ω μ)
    (M : ℝ)
    (hPair : ∀ n : ℕ, ∀ φ : Φ,
      ⟪embed φ, quotient n⟫_ℝ = ⟪discreteNegDiv n φ, Y⟫_ℝ)
    (hTestLimit : ∀ φ : Φ,
      Tendsto (fun n : ℕ => discreteNegDiv n φ) atTop
        (𝓝 (negDiv φ)))
    (hQuotientWeak : ∀ v : pressureNeumann3DVectorL2 Ω μ,
      Tendsto (fun n : ℕ => ⟪v, quotient n⟫_ℝ) atTop
        (𝓝 ⟪v, gLimit⟫_ℝ))
    (hBound : ∀ n : ℕ, ‖quotient n‖ ≤ M) :
    (WithLp.toLp 2 (Y, gLimit) :
      WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ)) ∈
          pressureNeumann3DTestGraph μ embed negDiv ∧
        ‖gLimit‖ ≤ M := by
  constructor
  · apply (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv
      (WithLp.toLp 2 (Y, gLimit))).2
    intro φ
    change ⟪embed φ, gLimit⟫_ℝ = ⟪negDiv φ, Y⟫_ℝ
    exact sr_spatial_weak_derivative_from_discrete_pairings
      embed negDiv discreteNegDiv Y quotient gLimit
      hPair hTestLimit hQuotientWeak φ
  · exact sr_spatial_weak_derivative_bound_from_quotients
      quotient gLimit M hQuotientWeak hBound

#print axioms ReservoirSeismicityControl.sr_spatial_weak_derivative_from_discrete_pairings
#print axioms ReservoirSeismicityControl.sr_spatial_weak_derivative_bound_from_quotients
#print axioms ReservoirSeismicityControl.sr_signed_3d_gradient_graph_from_reciprocal_quotients

end ReservoirSeismicityControl
