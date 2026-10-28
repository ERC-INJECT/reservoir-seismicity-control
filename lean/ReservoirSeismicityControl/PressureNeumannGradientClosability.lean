import ReservoirSeismicityControl.PressureNeumannGraphHilbertDomain
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Block 70: closability of the weak gradient from integration by parts

The completed graph in `PressureNeumannGraphHilbertDomain` is known to be a
complete Hilbert space. Its projection to the pressure component is injective
provided that the test-space gradient is closable. This module PROVES this
closability criterion using a weak integration-by-parts identity.

Let `D` be the linear domain of scalar test functions in the pressure Hilbert
space `H`, and `G : D →ₗ[ℝ] K` the candidate gradient in the Hilbert space `K`
of vector fields. Let `T ⊆ K` be a dense linear domain of vector-field test
functions, with formal negative divergence `delta : T →ₗ[ℝ] H`.

The sole analytical condition in this module is the test-level identity

  ⟪phi, G u⟫_K = ⟪delta phi, u⟫_H   (u ∈ D, phi ∈ T).

We extend the identity by graph closure, prove closability, and conclude
injectivity of the graph-closure embedding. No boundedness of the divergence
operator is assumed, and no derivatives of reservoir well fluxes are used.

For the eventual physical instance H=L²(Ω), K=L²(Ω;ℝ³), the remaining
obligations are: the concrete weak-gradient and divergence definitions,
integration by parts for smooth compactly supported tests on Ω, and density of
those test spaces. This module does not assert those obligations without proof.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Integration by parts on a dense class of vector-field tests extends to
all elements of the completed gradient graph, without assuming the
unbounded gradient or formal divergence is norm-continuous on their raw
test domains. -/
theorem pressure_neumann_graph_integration_by_parts
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (u : pressureNeumannGraphHilbertDomain D G) (phi : T) :
    ⟪(phi : K), pressureNeumannGraphHilbertGradient D G u⟫_ℝ =
      ⟪delta phi, pressureNeumannGraphHilbertEmbedding D G u⟫_ℝ := by
  let S : Set (WithLp 2 (H × K)) :=
    {z | ⟪(phi : K), (WithLp.sndL 2 ℝ H K) z⟫_ℝ =
      ⟪delta phi, (WithLp.fstL 2 ℝ H K) z⟫_ℝ}
  have hClosed : IsClosed S := by
    dsimp [S]
    apply isClosed_eq
    · exact (continuous_const.inner (WithLp.sndL 2 ℝ H K).continuous)
    · exact (continuous_const.inner (WithLp.fstL 2 ℝ H K).continuous)
  have hSubset : Set.range (pressureNeumannTestGraphMap D G) ⊆ S := by
    rintro z ⟨v, rfl⟩
    simpa [S, pressureNeumannTestGraphMap] using hIBP phi v
  have hClosure : (u : WithLp 2 (H × K)) ∈
      closure (Set.range (pressureNeumannTestGraphMap D G)) := by
    change (u : WithLp 2 (H × K)) ∈
      closure ((LinearMap.range (pressureNeumannTestGraphMap D G)) : Set _)
    rw [← Submodule.topologicalClosure_coe]
    exact u.property
  have hMem : (u : WithLp 2 (H × K)) ∈ S :=
    (closure_minimal hSubset hClosed) hClosure
  change ⟪(phi : K), (WithLp.sndL 2 ℝ H K) (u : WithLp 2 (H × K))⟫_ℝ =
    ⟪delta phi, (WithLp.fstL 2 ℝ H K) (u : WithLp 2 (H × K))⟫_ℝ
  exact hMem

/-- Dense integration-by-parts tests rule out vertical graph-closure
limits `(0,g)` with `g ≠ 0`. This proves closability of the gradient. -/
theorem pressure_neumann_graph_closable_of_integration_by_parts
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K)) :
    ∀ u : pressureNeumannGraphHilbertDomain D G,
      pressureNeumannGraphHilbertEmbedding D G u = 0 →
      pressureNeumannGraphHilbertGradient D G u = 0 := by
  intro u hzero
  apply hTDense.eq_zero_of_inner_left ℝ
  intro phi
  have h := pressure_neumann_graph_integration_by_parts D G T delta hIBP u phi
  rw [real_inner_comm]
  simpa [hzero] using h

/-- Hence the canonical Hilbert graph completion embeds injectively in the
pressure Hilbert space. -/
theorem pressure_neumann_graph_embedding_injective_of_integration_by_parts
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K)) :
    Function.Injective (pressureNeumannGraphHilbertEmbedding D G) := by
  exact pressure_neumann_graph_embedding_injective_of_closable D G
    (pressure_neumann_graph_closable_of_integration_by_parts
      D G T delta hIBP hTDense)

/-- A pair of dense scalar/vector test domains and the weak integration-by-parts
identity supply both embedding properties required by the abstract Neumann
semigroup-construction theorem. -/
theorem pressure_neumann_graph_embedding_injective_and_dense
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K))
    (hDDense : DenseRange (D.subtype : D → H)) :
    Function.Injective (pressureNeumannGraphHilbertEmbedding D G) ∧
      DenseRange (pressureNeumannGraphHilbertEmbedding D G) := by
  exact ⟨pressure_neumann_graph_embedding_injective_of_integration_by_parts
      D G T delta hIBP hTDense,
    pressure_neumann_graph_embedding_dense D G hDDense⟩

end ReservoirSeismicityControl
