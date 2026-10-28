import ReservoirSeismicityControl.PressureNeumannGraphPhysicalSemigroup
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Block 70: realize the graph completion as a closed, densely defined gradient operator

The preceding files construct the completed graph in H ⊕₂ K, prove
closability from integration by parts, and establish density of the pressure
projection. Here we give its operator-theoretic interpretation.

Its domain is the range of the pressure projection. Under the proved
injectivity condition, the completed gradient is a well-defined linear map
from that (not necessarily closed) domain to K. This domain is dense when
scalar test functions are dense. The graph is closed in H ⊕₂ K by its
construction as the closure of the original test-graph submodule.

This is not yet an identification with the distributional H¹(Ω) gradient.
The physical L² spaces and integration-by-parts tests still need to be
instantiated. Crucially, for a Neumann (not Dirichlet) realization the scalar
test domain D must be an H¹-dense core; taking only C_c^∞(Ω) gives H₀¹(Ω)
on standard domains and would impose Dirichlet conditions. The compact
support requirement belongs to the vector-field integration-by-parts tests,
not automatically to the scalar graph core. No flux derivatives are assumed.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Domain of the closed gradient, viewed as a linear subspace of pressure L². -/
noncomputable def pressureNeumannClosedGradientDomain
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) : Submodule ℝ H :=
  LinearMap.range (pressureNeumannGraphHilbertEmbedding D G).toLinearMap

/-- The unbounded completed gradient, bundled as a *linear map on its domain*.
Its injectivity argument will be provided by the integration-by-parts lemma.
It is not asserted to be bounded in the ambient pressure norm. -/
noncomputable def pressureNeumannClosedGradient
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G)) :
    pressureNeumannClosedGradientDomain D G →ₗ[ℝ] K :=
  (pressureNeumannGraphHilbertGradient D G).toLinearMap.comp
    ((LinearEquiv.ofInjective
      (pressureNeumannGraphHilbertEmbedding D G).toLinearMap hInj).symm.toLinearMap)

/-- The completed gradient and the original graph coordinates agree on
any vector of the completed graph. -/
theorem pressure_neumann_closed_gradient_on_graph
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G))
    (x : pressureNeumannGraphHilbertDomain D G) :
    pressureNeumannClosedGradient D G hInj
      ⟨pressureNeumannGraphHilbertEmbedding D G x,
        LinearMap.mem_range_self
          (pressureNeumannGraphHilbertEmbedding D G).toLinearMap x⟩ =
      pressureNeumannGraphHilbertGradient D G x := by
  let e := LinearEquiv.ofInjective
    (pressureNeumannGraphHilbertEmbedding D G).toLinearMap hInj
  change (pressureNeumannGraphHilbertGradient D G).toLinearMap
    (e.symm (e x)) = pressureNeumannGraphHilbertGradient D G x
  rw [e.symm_apply_apply]
  rfl

/-- Every point of the graph of the closed gradient comes from exactly
one vector of the Hilbert graph completion, and conversely. -/
theorem pressure_neumann_closed_gradient_graph_iff
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G))
    (u : H) (g : K) :
    (∃ x : pressureNeumannGraphHilbertDomain D G,
      pressureNeumannGraphHilbertEmbedding D G x = u ∧
      pressureNeumannGraphHilbertGradient D G x = g) ↔
    ∃ hu : u ∈ pressureNeumannClosedGradientDomain D G,
      pressureNeumannClosedGradient D G hInj ⟨u, hu⟩ = g := by
  constructor
  · rintro ⟨x, hx, hg⟩
    have hu : u ∈ pressureNeumannClosedGradientDomain D G := by
      change u ∈ LinearMap.range (pressureNeumannGraphHilbertEmbedding D G).toLinearMap
      exact ⟨x, hx⟩
    refine ⟨hu, ?_⟩
    have hval : (⟨u, hu⟩ : pressureNeumannClosedGradientDomain D G) =
        ⟨pressureNeumannGraphHilbertEmbedding D G x,
          LinearMap.mem_range_self
            (pressureNeumannGraphHilbertEmbedding D G).toLinearMap x⟩ := by
      apply Subtype.ext
      exact hx.symm
    rw [hval, pressure_neumann_closed_gradient_on_graph]
    exact hg
  · rintro ⟨hu, hg⟩
    let e := LinearEquiv.ofInjective
      (pressureNeumannGraphHilbertEmbedding D G).toLinearMap hInj
    let x : pressureNeumannGraphHilbertDomain D G := e.symm ⟨u, hu⟩
    have hx : pressureNeumannGraphHilbertEmbedding D G x = u := by
      have he : e x = (⟨u, hu⟩ : pressureNeumannClosedGradientDomain D G) :=
        e.apply_symm_apply _
      exact congrArg Subtype.val he
    refine ⟨x, hx, ?_⟩
    have hv : (⟨u, hu⟩ : pressureNeumannClosedGradientDomain D G) = e x := by
      exact (e.apply_symm_apply _).symm
    change (pressureNeumannGraphHilbertGradient D G).toLinearMap (e.symm ⟨u, hu⟩) = g at hg
    exact hg

/-- The domain of the completed gradient is dense in pressure L²,
provided that the original scalar test functions are dense. -/
theorem pressure_neumann_closed_gradient_domain_dense
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hDDense : DenseRange (D.subtype : D → H)) :
    Dense (pressureNeumannClosedGradientDomain D G : Set H) := by
  exact pressure_neumann_graph_embedding_dense D G hDDense

/-- The underlying completed graph is closed in the Hilbert L² product.
This is the closed-graph property of the unbounded gradient operator. -/
theorem pressure_neumann_closed_gradient_graph_closed
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) :
    IsClosed ((pressureNeumannGraphHilbertDomain D G :
      Submodule ℝ (WithLp 2 (H × K))) : Set (WithLp 2 (H × K))) := by
  unfold pressureNeumannGraphHilbertDomain
  rw [Submodule.topologicalClosure_coe]
  exact isClosed_closure

/-- Integration by parts and density of vector tests supply the injectivity
needed to define the closed gradient on its pressure domain. -/
theorem pressure_neumann_closed_gradient_exists_of_IBP
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K)) :
    ∃ hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G),
      ∀ x : pressureNeumannGraphHilbertDomain D G,
        pressureNeumannClosedGradient D G hInj
          ⟨pressureNeumannGraphHilbertEmbedding D G x,
            LinearMap.mem_range_self
              (pressureNeumannGraphHilbertEmbedding D G).toLinearMap x⟩ =
          pressureNeumannGraphHilbertGradient D G x := by
  let hInj := pressure_neumann_graph_embedding_injective_of_integration_by_parts
    D G T delta hIBP hTDense
  exact ⟨hInj, pressure_neumann_closed_gradient_on_graph D G hInj⟩

end ReservoirSeismicityControl
