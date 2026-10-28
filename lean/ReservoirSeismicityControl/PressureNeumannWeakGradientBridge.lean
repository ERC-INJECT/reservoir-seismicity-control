import ReservoirSeismicityControl.PressureNeumannPhysicalA3ClosedGradientSemigroup
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Block 70: the maximal weak-gradient graph and the completed Neumann gradient

Given test vector fields `T` and a formal negative divergence `delta`,
we define the maximal distributional-gradient graph as the collection of
pairs `(u,g)` satisfying

  ⟪phi, g⟫ = ⟪delta phi, u⟫       for every phi in T.

The graph is closed in the Hilbert product H ⊕₂ K, since each test
identity is the kernel of a continuous linear functional. The gradient
closure previously constructed from the scalar core `D` lies in this
maximal graph, by the established integration-by-parts argument.

Density of vector tests gives uniqueness of the weak gradient. To prove
that the completed-gradient domain is exactly the maximal Sobolev H¹
space, one must STILL prove density of the chosen scalar Neumann core
in this maximal graph norm. This file does not assume or claim that
identification. The scalar core is not required to have compact support.

No assumption concerning time derivatives of the well rates is used.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Continuous functional encoding the weak integration-by-parts equation
for a single test vector field. -/
noncomputable def pressureNeumannWeakIBPFunctional
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) (phi : T) :
    WithLp 2 (H × K) →L[ℝ] ℝ :=
  (innerSL ℝ (phi : K)).comp (WithLp.sndL 2 ℝ H K) -
    (innerSL ℝ (delta phi)).comp (WithLp.fstL 2 ℝ H K)

/-- Maximal distributional graph relative to the test divergence.
This is an intersection of closed kernels, not an assumed Sobolev space. -/
noncomputable def pressureNeumannWeakIBPGraph
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) :
    Submodule ℝ (WithLp 2 (H × K)) :=
  ⨅ phi : T, (pressureNeumannWeakIBPFunctional T delta phi).ker

/-- Membership is precisely the distributional integration-by-parts
identity tested against every field in `T`. -/
theorem pressure_neumann_weak_ibp_graph_mem_iff
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (z : WithLp 2 (H × K)) :
    z ∈ pressureNeumannWeakIBPGraph T delta ↔
      ∀ phi : T,
        ⟪(phi : K), (WithLp.sndL 2 ℝ H K) z⟫_ℝ =
          ⟪delta phi, (WithLp.fstL 2 ℝ H K) z⟫_ℝ := by
  simp only [pressureNeumannWeakIBPGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hz phi
    have h := hz phi
    change ⟪(phi : K), (WithLp.sndL 2 ℝ H K) z⟫_ℝ -
      ⟪delta phi, (WithLp.fstL 2 ℝ H K) z⟫_ℝ = 0 at h
    exact sub_eq_zero.mp h
  · intro hz phi
    change ⟪(phi : K), (WithLp.sndL 2 ℝ H K) z⟫_ℝ -
      ⟪delta phi, (WithLp.fstL 2 ℝ H K) z⟫_ℝ = 0
    exact sub_eq_zero.mpr (hz phi)

/-- The maximal distributional weak-gradient graph is closed in H ⊕₂ K. -/
theorem pressure_neumann_weak_ibp_graph_closed
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) :
    IsClosed ((pressureNeumannWeakIBPGraph T delta :
      Submodule ℝ (WithLp 2 (H × K))) : Set (WithLp 2 (H × K))) := by
  change IsClosed ((⨅ phi : T,
    (pressureNeumannWeakIBPFunctional T delta phi).ker :
      Submodule ℝ (WithLp 2 (H × K))) : Set (WithLp 2 (H × K)))
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun phi => (pressureNeumannWeakIBPFunctional T delta phi).isClosed_ker

/-- Integration by parts on the scalar core implies that the *whole*
completed graph lies in the maximal distributional graph. -/
theorem pressure_neumann_graph_le_weak_ibp_graph
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ) :
    pressureNeumannGraphHilbertDomain D G ≤ pressureNeumannWeakIBPGraph T delta := by
  intro z hz
  apply (pressure_neumann_weak_ibp_graph_mem_iff T delta z).2
  intro phi
  exact pressure_neumann_graph_integration_by_parts D G T delta hIBP ⟨z, hz⟩ phi

/-- Density of vector-field tests makes the distributional gradient unique
when two admissible graph pairs have the same pressure component. -/
theorem pressure_neumann_weak_ibp_gradient_unique
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K))
    (z w : WithLp 2 (H × K))
    (hz : z ∈ pressureNeumannWeakIBPGraph T delta)
    (hw : w ∈ pressureNeumannWeakIBPGraph T delta)
    (hp : (WithLp.fstL 2 ℝ H K) z = (WithLp.fstL 2 ℝ H K) w) :
    (WithLp.sndL 2 ℝ H K) z = (WithLp.sndL 2 ℝ H K) w := by
  have hzero : (WithLp.sndL 2 ℝ H K) z - (WithLp.sndL 2 ℝ H K) w = 0 := by
    apply hTDense.eq_zero_of_inner_left ℝ
    intro phi
    have hzphi := (pressure_neumann_weak_ibp_graph_mem_iff T delta z).1 hz phi
    have hwphi := (pressure_neumann_weak_ibp_graph_mem_iff T delta w).1 hw phi
    have heq : ⟪(phi : K), (WithLp.sndL 2 ℝ H K) z⟫_ℝ =
        ⟪(phi : K), (WithLp.sndL 2 ℝ H K) w⟫_ℝ := by
      calc
        _ = ⟪delta phi, (WithLp.fstL 2 ℝ H K) z⟫_ℝ := hzphi
        _ = ⟪delta phi, (WithLp.fstL 2 ℝ H K) w⟫_ℝ := by rw [hp]
        _ = _ := hwphi.symm
    rw [real_inner_comm, inner_sub_right]
    exact sub_eq_zero.mpr heq
  exact sub_eq_zero.mp hzero

/-- The completed closed gradient satisfies the defining distributional
identity for every vector-field test. -/
theorem pressure_neumann_closed_gradient_weak_ibp
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G))
    (u : pressureNeumannClosedGradientDomain D G) (phi : T) :
    ⟪(phi : K), pressureNeumannClosedGradient D G hInj u⟫_ℝ =
      ⟪delta phi, (u : H)⟫_ℝ := by
  obtain ⟨x, hx, hGx⟩ :=
    (pressure_neumann_closed_gradient_graph_iff D G hInj
      (u : H) (pressureNeumannClosedGradient D G hInj u)).2 ⟨u.property, rfl⟩
  calc
    _ = ⟪(phi : K), pressureNeumannGraphHilbertGradient D G x⟫_ℝ := by rw [hGx]
    _ = ⟪delta phi, pressureNeumannGraphHilbertEmbedding D G x⟫_ℝ :=
      pressure_neumann_graph_integration_by_parts D G T delta hIBP x phi
    _ = ⟪delta phi, (u : H)⟫_ℝ := by rw [hx]

/-- Any vector field satisfying the weak gradient identity for a pressure
from the closed-gradient domain must equal its completed gradient. -/
theorem pressure_neumann_closed_gradient_unique_weak
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K))
    (u : pressureNeumannClosedGradientDomain D G) (g : K)
    (hWeak : ∀ phi : T, ⟪(phi : K), g⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ) :
    g = pressureNeumannClosedGradient D G
      (pressure_neumann_graph_embedding_injective_of_integration_by_parts
        D G T delta hIBP hTDense) u := by
  let hInj := pressure_neumann_graph_embedding_injective_of_integration_by_parts
    D G T delta hIBP hTDense
  have hzero : g - pressureNeumannClosedGradient D G hInj u = 0 := by
    apply hTDense.eq_zero_of_inner_left ℝ
    intro phi
    rw [real_inner_comm, inner_sub_right]
    exact sub_eq_zero.mpr ((hWeak phi).trans
      (pressure_neumann_closed_gradient_weak_ibp D G T delta hIBP hInj u phi).symm)
  exact sub_eq_zero.mp hzero

end ReservoirSeismicityControl
