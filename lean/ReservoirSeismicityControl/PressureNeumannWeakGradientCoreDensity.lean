import ReservoirSeismicityControl.PressureNeumannWeakGradientBridge

/-!
# Block 71: the remaining Neumann weak-gradient core-density obligation

The preceding bridge proves that the graph closure of the scalar gradient
is contained in the maximal distributional-gradient graph. This file
separates two facts that must not be conflated.

* The maximal weak-gradient graph is single-valued when the vector test
  space is dense. This follows from integration by parts and does not
  require a graph approximation theorem.
* Equality of the completed graph and the maximal weak-gradient graph
  follows if every weak pair `(u,g)` can be approximated in the product
  L² graph norm by scalar-core pairs `(v,G v)`. The second condition is
  precisely the remaining Sobolev/core-density obligation. It is NOT
  derived here from the abstract assumptions.

For the physical Neumann realization the scalar core should be H¹-dense,
not merely C_c^infty(Ω), since the latter generally gives H₀¹(Ω).
None of these statements assumes derivatives of the well fluxes.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The maximal distributional weak gradient is single-valued: pressure
projection is injective on its weak integration-by-parts graph. -/
theorem pressure_neumann_weak_ibp_pressure_projection_injective
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K)) :
    Function.Injective
      ((WithLp.fstL 2 ℝ H K).comp
        (pressureNeumannWeakIBPGraph T delta).subtypeL) := by
  intro z w hp
  have hfirst :
      (WithLp.fstL 2 ℝ H K) (z : WithLp 2 (H × K)) =
        (WithLp.fstL 2 ℝ H K) (w : WithLp 2 (H × K)) := by
    simpa using hp
  have hsecond :=
    pressure_neumann_weak_ibp_gradient_unique T delta hTDense
      (z : WithLp 2 (H × K)) (w : WithLp 2 (H × K))
      z.property w.property hfirst
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ H K).injective
  apply Prod.ext
  · simpa using hfirst
  · simpa using hsecond

/-- If the scalar test graph is dense in the maximal weak graph in the
ambient product Hilbert topology, the completed graph equals that maximal
weak graph. The approximation is an explicit proof obligation. -/
theorem pressure_neumann_graph_eq_weak_of_core_closure
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hApprox : ∀ z : WithLp 2 (H × K),
      z ∈ pressureNeumannWeakIBPGraph T delta →
        z ∈ closure (Set.range (pressureNeumannTestGraphMap D G))) :
    pressureNeumannGraphHilbertDomain D G = pressureNeumannWeakIBPGraph T delta := by
  apply le_antisymm
  · exact pressure_neumann_graph_le_weak_ibp_graph D G T delta hIBP
  · intro z hz
    have hcl := hApprox z hz
    change z ∈ (LinearMap.range (pressureNeumannTestGraphMap D G)).topologicalClosure
    change z ∈ closure ((LinearMap.range (pressureNeumannTestGraphMap D G)) : Set _) at hcl
    rw [← Submodule.topologicalClosure_coe] at hcl
    exact hcl

/-- A sequential graph-norm approximation suffices to discharge the
closure condition. This is the convenient formulation for a future
mollification/extension proof on the physical Lipschitz reservoir domain.
It is a *conditional* reduction, not such an approximation proof. -/
theorem pressure_neumann_graph_eq_weak_of_core_sequence
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hApprox : ∀ z : WithLp 2 (H × K),
      z ∈ pressureNeumannWeakIBPGraph T delta →
        ∃ s : ℕ → D,
          Filter.Tendsto (fun n => pressureNeumannTestGraphMap D G (s n))
            Filter.atTop (nhds z)) :
    pressureNeumannGraphHilbertDomain D G = pressureNeumannWeakIBPGraph T delta := by
  apply pressure_neumann_graph_eq_weak_of_core_closure D G T delta hIBP
  intro z hz
  obtain ⟨s, hs⟩ := hApprox z hz
  apply isClosed_closure.mem_of_tendsto hs
  exact Filter.Eventually.of_forall (fun n =>
    subset_closure (show pressureNeumannTestGraphMap D G (s n) ∈
      Set.range (pressureNeumannTestGraphMap D G) from ⟨s n, rfl⟩))

end ReservoirSeismicityControl
