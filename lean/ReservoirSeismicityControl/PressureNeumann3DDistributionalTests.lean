import ReservoirSeismicityControl.PressureNeumannMaximalWeakRealization

/-!
# Block 73: three-dimensional distributional test-field interface

Let Ω be a subset of Euclidean three-space, equipped with a measure μ.
The scalar and vector Hilbert spaces are now fixed to L²(Ω, μ) and
L²(Ω, μ; ℝ³). Rather than requiring vector tests to be an L² submodule
with a separately well-defined divergence, we allow an independent linear
test-field space Φ, an L² realization `embed`, and its negative divergence
`negDiv`. This permits Φ to be instantiated later by compactly supported
smooth vector fields, once their L² and divergence maps are constructed.

We PROVE that the distributional weak-gradient relation determined by
these test maps is a closed linear graph, and that a dense test-field
realization determines a unique L² weak gradient. We also identify this
graph with the existing maximal graph when tests already form an L²
submodule. Thus, no new abstract gradient or hidden equivalence is needed.

NOT PROVED HERE: the existence and density of actual C_c^∞(Ω; ℝ³)
realizations, the integration-by-parts formula for their divergence,
or equality with H¹(Ω). These are the next concrete analytic obligations.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- The physical scalar L² space for a measurable three-dimensional region. -/
abbrev pressureNeumann3DScalarL2
    (Ω : Set (EuclideanSpace ℝ (Fin 3))) (μ : Measure Ω) := Lp ℝ 2 μ

/-- The physical vector-valued L² space for a three-dimensional region. -/
noncomputable abbrev pressureNeumann3DVectorL2
    (Ω : Set (EuclideanSpace ℝ (Fin 3))) (μ : Measure Ω) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 μ

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The weak integration-by-parts functional for a concrete vector test. -/
noncomputable def pressureNeumann3DTestFunctional
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (φ : Φ) :
    WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
      pressureNeumann3DVectorL2 Ω μ) →L[ℝ] ℝ :=
  (innerSL ℝ (embed φ)).comp
    (WithLp.sndL 2 ℝ (pressureNeumann3DScalarL2 Ω μ)
      (pressureNeumann3DVectorL2 Ω μ)) -
  (innerSL ℝ (negDiv φ)).comp
    (WithLp.fstL 2 ℝ (pressureNeumann3DScalarL2 Ω μ)
      (pressureNeumann3DVectorL2 Ω μ))

/-- Maximal L² weak-gradient graph determined by the distributional tests.
It is an intersection of continuous linear-functional kernels. -/
noncomputable def pressureNeumann3DTestGraph
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    Submodule ℝ (WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
      pressureNeumann3DVectorL2 Ω μ)) :=
  ⨅ φ : Φ, (pressureNeumann3DTestFunctional μ embed negDiv φ).ker

/-- Membership in the graph means that g is the distributional gradient
of u, tested against every test field in Φ. -/
theorem pressure_neumann_3d_test_graph_mem_iff
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (z : WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
      pressureNeumann3DVectorL2 Ω μ)) :
    z ∈ pressureNeumann3DTestGraph μ embed negDiv ↔
      ∀ φ : Φ,
        ⟪embed φ, (WithLp.sndL 2 ℝ _ _) z⟫_ℝ =
          ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) z⟫_ℝ := by
  simp only [pressureNeumann3DTestGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hz φ
    have h := hz φ
    change ⟪embed φ, (WithLp.sndL 2 ℝ _ _) z⟫_ℝ -
      ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) z⟫_ℝ = 0 at h
    exact sub_eq_zero.mp h
  · intro hz φ
    change ⟪embed φ, (WithLp.sndL 2 ℝ _ _) z⟫_ℝ -
      ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) z⟫_ℝ = 0
    exact sub_eq_zero.mpr (hz φ)

/-- The distributional test graph is closed in the L² product topology. -/
theorem pressure_neumann_3d_test_graph_closed
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    IsClosed ((pressureNeumann3DTestGraph μ embed negDiv :
      Submodule ℝ (WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ))) :
      Set (WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ))) := by
  change IsClosed ((⨅ φ : Φ,
    (pressureNeumann3DTestFunctional μ embed negDiv φ).ker :
      Submodule ℝ (WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ))) :
      Set (WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
        pressureNeumann3DVectorL2 Ω μ)))
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ =>
    (pressureNeumann3DTestFunctional μ embed negDiv φ).isClosed_ker

/-- Dense vector tests make the distributional gradient single-valued. -/
theorem pressure_neumann_3d_test_gradient_unique
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (z w : WithLp 2 (pressureNeumann3DScalarL2 Ω μ ×
      pressureNeumann3DVectorL2 Ω μ))
    (hz : z ∈ pressureNeumann3DTestGraph μ embed negDiv)
    (hw : w ∈ pressureNeumann3DTestGraph μ embed negDiv)
    (hp : (WithLp.fstL 2 ℝ _ _) z = (WithLp.fstL 2 ℝ _ _) w) :
    (WithLp.sndL 2 ℝ _ _) z = (WithLp.sndL 2 ℝ _ _) w := by
  have hzero : (WithLp.sndL 2 ℝ _ _) z - (WithLp.sndL 2 ℝ _ _) w = 0 := by
    apply hDense.eq_zero_of_inner_left ℝ
    intro φ
    have hzφ := (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv z).mp hz φ
    have hwφ := (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv w).mp hw φ
    have heq : ⟪embed φ, (WithLp.sndL 2 ℝ _ _) z⟫_ℝ =
        ⟪embed φ, (WithLp.sndL 2 ℝ _ _) w⟫_ℝ := by
      calc
        _ = ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) z⟫_ℝ := hzφ
        _ = ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) w⟫_ℝ := by rw [hp]
        _ = _ := hwφ.symm
    rw [real_inner_comm, inner_sub_right]
    exact sub_eq_zero.mpr heq
  exact sub_eq_zero.mp hzero

/-- The new test-field interface agrees with the earlier submodule-based
maximal graph when Φ is exactly the vector test submodule. -/
theorem pressure_neumann_3d_test_graph_eq_existing
    (T : Submodule ℝ (pressureNeumann3DVectorL2 Ω μ))
    (delta : T →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    pressureNeumann3DTestGraph μ T.subtype delta =
      pressureNeumannWeakIBPGraph T delta := by
  rfl

end ReservoirSeismicityControl
