import ReservoirSeismicityControl.PressureNeumann3DWeakH1Candidate
import ReservoirSeismicityControl.PressureNeumannGraphHilbertDomain

/-!
# Three-dimensional weak H¹: identification with its completed gradient graph

This module establishes a substantial step without asserting an unproved
Sobolev extension or compact-support density theorem. The maximal L²
distributional-gradient graph associated with abstract test maps `embed`
and `negDiv` is closed. When vector tests are dense, its pressure projection
is injective, and the graph is exactly the completed graph of its own
single-valued weak-gradient operator.

In particular, no separate *scalar graph-core density* assumption is needed.
This is the Neumann-appropriate maximal realization, not H₀¹.

The identification with standard H¹(Ω) is still conditional on constructing
real C_c^∞ vector test fields and their divergence on the Lipschitz domain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The completed graph built from the maximal weak-gradient domain is
exactly the original closed distributional-test graph. -/
theorem pressure_neumann_3d_weak_graph_eq_test_graph
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ)) :
    pressureNeumannGraphHilbertDomain
      (pressureNeumann3DWeakH1Candidate μ embed negDiv)
      (pressureNeumann3DWeakGradient μ embed negDiv hDense) =
      pressureNeumann3DTestGraph μ embed negDiv := by
  let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
  let G := pressureNeumann3DWeakGradient μ embed negDiv hDense
  let M := pressureNeumann3DTestGraph μ embed negDiv
  apply le_antisymm
  · intro z hz
    have hClosed : IsClosed (M : Set (WithLp 2
        (pressureNeumann3DScalarL2 Ω μ × pressureNeumann3DVectorL2 Ω μ))) :=
      pressure_neumann_3d_test_graph_closed μ embed negDiv
    have hIncluded : Set.range (pressureNeumannTestGraphMap D G) ⊆ (M : Set _) := by
      rintro x ⟨u, rfl⟩
      apply (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv _).2
      intro phi
      change ⟪embed phi, G u⟫_ℝ = ⟪negDiv phi, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ
      exact pressure_neumann_3d_weak_gradient_ibp μ embed negDiv hDense phi u
    have hzClosure : (z : WithLp 2
        (pressureNeumann3DScalarL2 Ω μ × pressureNeumann3DVectorL2 Ω μ)) ∈
        closure (Set.range (pressureNeumannTestGraphMap D G)) := by
      change z ∈ closure ((LinearMap.range (pressureNeumannTestGraphMap D G)) : Set _)
      rw [← Submodule.topologicalClosure_coe]
      exact hz
    exact (closure_minimal hIncluded hClosed) hzClosure
  · intro z hz
    let x : M := ⟨z, hz⟩
    let u : D :=
      ⟨pressureNeumann3DWeakPressureProjection μ embed negDiv x,
       LinearMap.mem_range_self
         (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap x⟩
    have hPair : pressureNeumannTestGraphMap D G u = z := by
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
      apply Prod.ext
      · change (u : pressureNeumann3DScalarL2 Ω μ) =
          (WithLp.fstL 2 ℝ _ _) z
        rfl
      · change G u = (WithLp.sndL 2 ℝ _ _) z
        exact pressure_neumann_3d_weak_gradient_on_graph μ embed negDiv hDense x
    apply (Submodule.le_topologicalClosure _)
    exact ⟨u, hPair⟩

/-- The Hilbert graph embedding is injective because the distributional
gradient is unique; in particular, the graph represents pressures faithfully. -/
theorem pressure_neumann_3d_weak_graph_embedding_injective
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ)) :
    Function.Injective (pressureNeumannGraphHilbertEmbedding
      (pressureNeumann3DWeakH1Candidate μ embed negDiv)
      (pressureNeumann3DWeakGradient μ embed negDiv hDense)) := by
  let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
  let G := pressureNeumann3DWeakGradient μ embed negDiv hDense
  apply pressure_neumann_graph_embedding_injective_of_closable D G
  intro z hz
  have hEq := pressure_neumann_3d_weak_graph_eq_test_graph μ embed negDiv hDense
  have hzM : (z : WithLp 2
      (pressureNeumann3DScalarL2 Ω μ × pressureNeumann3DVectorL2 Ω μ)) ∈
      pressureNeumann3DTestGraph μ embed negDiv := by
    rw [← hEq]
    exact z.property
  have hSecond := pressure_neumann_3d_test_gradient_unique μ embed negDiv hDense
    (z : WithLp 2 (pressureNeumann3DScalarL2 Ω μ × pressureNeumann3DVectorL2 Ω μ))
    0 hzM (Submodule.zero_mem _) (by
      simpa [pressureNeumannGraphHilbertEmbedding] using hz)
  simpa [pressureNeumannGraphHilbertGradient] using hSecond

/-- Dense scalar members of the weak domain imply dense embedding of its
canonical completed Hilbert graph in pressure L². -/
theorem pressure_neumann_3d_weak_graph_embedding_dense
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (hScalarDense : DenseRange ((pressureNeumann3DWeakH1Candidate μ embed negDiv).subtype :
      pressureNeumann3DWeakH1Candidate μ embed negDiv →
        pressureNeumann3DScalarL2 Ω μ)) :
    DenseRange (pressureNeumannGraphHilbertEmbedding
      (pressureNeumann3DWeakH1Candidate μ embed negDiv)
      (pressureNeumann3DWeakGradient μ embed negDiv hDense)) :=
  pressure_neumann_graph_embedding_dense _ _ hScalarDense

end ReservoirSeismicityControl
