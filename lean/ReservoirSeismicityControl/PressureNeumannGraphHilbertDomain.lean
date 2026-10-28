import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Block 70: construct a complete graph-norm form domain

Let H be the pressure L² Hilbert space and K be the Hilbert space of
square-integrable vector fields (three components in the physical model).
Let D ⊆ H be a dense linear test domain and let G : D →ₗ[ℝ] K
be the weak-gradient map on D.

We construct V as the closure of the graph {(u, G u) : u ∈ D}
in the Hilbert product H ⊕₂ K. Completeness of V and its exact
squared graph norm follow by construction; neither is postulated.

To identify V faithfully with a space of pressure functions, the gradient
must be closable: an element (0,g) of the graph closure must have g=0.
This is stated explicitly in the injectivity theorem, not hidden.
The density of V → H follows from density of D → H.

The physical choice H=L²(Ω), K=L²(Ω;ℝ³), D=smooth test functions,
and proof of closability of distributional gradient on Ω remain to be
instantiated. No flux-derivative bounds enter these results.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Graph map u ↦ (u, Gu), using the L² product norm, not the max norm. -/
noncomputable def pressureNeumannTestGraphMap
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) : D →ₗ[ℝ] WithLp 2 (H × K) :=
  (WithLp.linearEquiv 2 ℝ (H × K)).symm.toLinearMap.comp (D.subtype.prod G)

/-- Hilbert graph closure of the test-space gradient. -/
noncomputable def pressureNeumannGraphHilbertDomain
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) :
    Submodule ℝ (WithLp 2 (H × K)) :=
  (LinearMap.range (pressureNeumannTestGraphMap D G)).topologicalClosure

/-- This form space is complete without a `CompleteSpace V` hypothesis. -/
noncomputable instance pressureNeumannGraphHilbertDomain_complete
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) :
    CompleteSpace (pressureNeumannGraphHilbertDomain D G) := by
  unfold pressureNeumannGraphHilbertDomain
  infer_instance

/-- The pressure component of an element of the completed graph. -/
noncomputable def pressureNeumannGraphHilbertEmbedding
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) :
    pressureNeumannGraphHilbertDomain D G →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H K).comp (pressureNeumannGraphHilbertDomain D G).subtypeL

/-- The vector-valued weak-gradient component of a completed graph element. -/
noncomputable def pressureNeumannGraphHilbertGradient
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) :
    pressureNeumannGraphHilbertDomain D G →L[ℝ] K :=
  (WithLp.sndL 2 ℝ H K).comp (pressureNeumannGraphHilbertDomain D G).subtypeL

/-- On the original test domain, the completed embedding preserves the pressure. -/
private noncomputable def pressureNeumannGraphTestLift
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (u : D) :
    pressureNeumannGraphHilbertDomain D G :=
  ⟨pressureNeumannTestGraphMap D G u,
    (Submodule.le_topologicalClosure _)
      (LinearMap.mem_range_self (pressureNeumannTestGraphMap D G) u)⟩

theorem pressure_neumann_graph_embedding_test
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (u : D) :
    pressureNeumannGraphHilbertEmbedding D G (pressureNeumannGraphTestLift D G u) = (u : H) := by
  simp [pressureNeumannGraphHilbertEmbedding, pressureNeumannGraphTestLift,
    pressureNeumannTestGraphMap]

/-- Dense original tests imply a dense completed graph embedding. -/
theorem pressure_neumann_graph_embedding_dense
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hD : DenseRange (D.subtype : D → H)) :
    DenseRange (pressureNeumannGraphHilbertEmbedding D G) := by
  have hEq :
      (pressureNeumannGraphHilbertEmbedding D G ∘ pressureNeumannGraphTestLift D G) =
        (D.subtype : D → H) := by
    funext u
    exact pressure_neumann_graph_embedding_test D G u
  have hcomp : DenseRange
      (pressureNeumannGraphHilbertEmbedding D G ∘ pressureNeumannGraphTestLift D G) := by
    rw [hEq]
    exact hD
  exact DenseRange.of_comp hcomp

/-- The exact L² graph norm on the Hilbert completion. -/
theorem pressure_neumann_graph_norm_sq
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (u : pressureNeumannGraphHilbertDomain D G) :
    ‖u‖ * ‖u‖ =
      ‖pressureNeumannGraphHilbertEmbedding D G u‖ *
        ‖pressureNeumannGraphHilbertEmbedding D G u‖ +
      ‖pressureNeumannGraphHilbertGradient D G u‖ *
        ‖pressureNeumannGraphHilbertGradient D G u‖ := by
  have hp := WithLp.prod_inner_apply (𝕜 := ℝ)
    (x := (u : WithLp 2 (H × K))) (y := (u : WithLp 2 (H × K)))
  calc
    ‖u‖ * ‖u‖ = ⟪(u : WithLp 2 (H × K)), (u : WithLp 2 (H × K))⟫_ℝ := by
      simpa using (real_inner_self_eq_norm_mul_norm (u : WithLp 2 (H × K))).symm
    _ = ⟪pressureNeumannGraphHilbertEmbedding D G u,
            pressureNeumannGraphHilbertEmbedding D G u⟫_ℝ +
          ⟪pressureNeumannGraphHilbertGradient D G u,
            pressureNeumannGraphHilbertGradient D G u⟫_ℝ := by
      simpa [pressureNeumannGraphHilbertEmbedding,
        pressureNeumannGraphHilbertGradient] using hp
    _ = _ := by rw [real_inner_self_eq_norm_mul_norm,
      real_inner_self_eq_norm_mul_norm]

/-- A closable gradient makes the completed graph embedding injective.
The hypothesis is exactly the absence of nonzero vertical graph limits. -/
theorem pressure_neumann_graph_embedding_injective_of_closable
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (hClosable : ∀ u : pressureNeumannGraphHilbertDomain D G,
      pressureNeumannGraphHilbertEmbedding D G u = 0 →
      pressureNeumannGraphHilbertGradient D G u = 0) :
    Function.Injective (pressureNeumannGraphHilbertEmbedding D G) := by
  intro u v huv
  have hzero : pressureNeumannGraphHilbertEmbedding D G (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hgrad := hClosable (u - v) hzero
  have hparent : ((u - v : pressureNeumannGraphHilbertDomain D G) :
      WithLp 2 (H × K)) = 0 := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ H K).injective
    apply Prod.ext
    · simpa [pressureNeumannGraphHilbertEmbedding] using hzero
    · simpa [pressureNeumannGraphHilbertGradient] using hgrad
  have hz : u - v = 0 := Subtype.ext (by simpa using hparent)
  exact sub_eq_zero.mp hz

end ReservoirSeismicityControl
