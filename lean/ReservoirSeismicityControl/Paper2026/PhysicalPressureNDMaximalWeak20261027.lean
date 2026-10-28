import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDSemigroup20261027
import ReservoirSeismicityControl.PressureNeumannGraphHilbertDomain
import ReservoirSeismicityControl.PressureNeumannWeakGradientBridge
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Dimension-parametric maximal weak-H¹ Neumann domain

Generalizes the formerly Fin 3 distributional-test graph, unique
weak gradient, closed graph and injection into pressure L² to Fin n_d.
No assumption of a separate integration-by-parts identity: it is *proved*
for this graph. Only density of vector tests is used for uniqueness.

An actual smooth-test realization and density on the physical domain are
standard geometric applicability obligations, not proven by this module.
All previously passing 3D modules are kept unchanged.
-/

namespace ReservoirSeismicityControl

variable {n_d : ℕ}

section NDDistributional
open MeasureTheory
open scoped InnerProductSpace

/-- The physical scalar L² space for a measurable n_d-dimensional region. -/
abbrev pressureNDScalarL2
    (Ω : Set (Paper2026.PaperSpatial n_d)) (μ : Measure Ω) := Lp ℝ 2 μ

/-- The physical vector-valued L² space for a n_d-dimensional region. -/
noncomputable abbrev pressureNDVectorL2
    (Ω : Set (Paper2026.PaperSpatial n_d)) (μ : Measure Ω) :=
  Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ

variable {Ω : Set (Paper2026.PaperSpatial n_d)} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The weak integration-by-parts functional for a concrete vector test. -/
noncomputable def pressureNDTestFunctional
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (φ : Φ) :
    WithLp 2 (pressureNDScalarL2 Ω μ ×
      pressureNDVectorL2 Ω μ) →L[ℝ] ℝ :=
  (innerSL ℝ (embed φ)).comp
    (WithLp.sndL 2 ℝ (pressureNDScalarL2 Ω μ)
      (pressureNDVectorL2 Ω μ)) -
  (innerSL ℝ (negDiv φ)).comp
    (WithLp.fstL 2 ℝ (pressureNDScalarL2 Ω μ)
      (pressureNDVectorL2 Ω μ))

/-- Maximal L² weak-gradient graph determined by the distributional tests.
It is an intersection of continuous linear-functional kernels. -/
noncomputable def pressureNDTestGraph
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    Submodule ℝ (WithLp 2 (pressureNDScalarL2 Ω μ ×
      pressureNDVectorL2 Ω μ)) :=
  ⨅ φ : Φ, (pressureNDTestFunctional μ embed negDiv φ).ker

/-- Membership in the graph means that g is the distributional gradient
of u, tested against every test field in Φ. -/
theorem pressure_nd_test_graph_mem_iff
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (z : WithLp 2 (pressureNDScalarL2 Ω μ ×
      pressureNDVectorL2 Ω μ)) :
    z ∈ pressureNDTestGraph μ embed negDiv ↔
      ∀ φ : Φ,
        ⟪embed φ, (WithLp.sndL 2 ℝ _ _) z⟫_ℝ =
          ⟪negDiv φ, (WithLp.fstL 2 ℝ _ _) z⟫_ℝ := by
  simp only [pressureNDTestGraph, Submodule.mem_iInf, LinearMap.mem_ker]
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
theorem pressure_nd_test_graph_closed
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    IsClosed ((pressureNDTestGraph μ embed negDiv :
      Submodule ℝ (WithLp 2 (pressureNDScalarL2 Ω μ ×
        pressureNDVectorL2 Ω μ))) :
      Set (WithLp 2 (pressureNDScalarL2 Ω μ ×
        pressureNDVectorL2 Ω μ))) := by
  change IsClosed ((⨅ φ : Φ,
    (pressureNDTestFunctional μ embed negDiv φ).ker :
      Submodule ℝ (WithLp 2 (pressureNDScalarL2 Ω μ ×
        pressureNDVectorL2 Ω μ))) :
      Set (WithLp 2 (pressureNDScalarL2 Ω μ ×
        pressureNDVectorL2 Ω μ)))
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ =>
    (pressureNDTestFunctional μ embed negDiv φ).isClosed_ker

/-- Dense vector tests make the distributional gradient single-valued. -/
theorem pressure_nd_test_gradient_unique
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (z w : WithLp 2 (pressureNDScalarL2 Ω μ ×
      pressureNDVectorL2 Ω μ))
    (hz : z ∈ pressureNDTestGraph μ embed negDiv)
    (hw : w ∈ pressureNDTestGraph μ embed negDiv)
    (hp : (WithLp.fstL 2 ℝ _ _) z = (WithLp.fstL 2 ℝ _ _) w) :
    (WithLp.sndL 2 ℝ _ _) z = (WithLp.sndL 2 ℝ _ _) w := by
  have hzero : (WithLp.sndL 2 ℝ _ _) z - (WithLp.sndL 2 ℝ _ _) w = 0 := by
    apply hDense.eq_zero_of_inner_left ℝ
    intro φ
    have hzφ := (pressure_nd_test_graph_mem_iff μ embed negDiv z).mp hz φ
    have hwφ := (pressure_nd_test_graph_mem_iff μ embed negDiv w).mp hw φ
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
theorem pressure_nd_test_graph_eq_existing
    (T : Submodule ℝ (pressureNDVectorL2 Ω μ))
    (delta : T →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    pressureNDTestGraph μ T.subtype delta =
      pressureNeumannWeakIBPGraph T delta := by
  rfl




end NDDistributional

section NDWeakGradient
open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Set (Paper2026.PaperSpatial n_d)} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- Projection of a distributional graph pair onto scalar L² pressure. -/
noncomputable def pressureNDWeakPressureProjection
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    pressureNDTestGraph μ embed negDiv →L[ℝ]
      pressureNDScalarL2 Ω μ :=
  (WithLp.fstL 2 ℝ _ _).comp
    (pressureNDTestGraph μ embed negDiv).subtypeL

/-- Projection of a distributional graph pair onto its L² weak gradient. -/
noncomputable def pressureNDWeakGradientProjection
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    pressureNDTestGraph μ embed negDiv →L[ℝ]
      pressureNDVectorL2 Ω μ :=
  (WithLp.sndL 2 ℝ _ _).comp
    (pressureNDTestGraph μ embed negDiv).subtypeL

/-- L² pressures with an L² distributional gradient relative to the tests. -/
noncomputable def pressureNDWeakH1Candidate
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ) :
    Submodule ℝ (pressureNDScalarL2 Ω μ) :=
  LinearMap.range
    (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap

/-- Dense L² test fields imply that the pressure projection is injective
on the distributional graph. -/
theorem pressure_nd_weak_pressure_projection_injective
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ)) :
    Function.Injective
      (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap := by
  intro z w hp
  have hfirst :
      (WithLp.fstL 2 ℝ _ _) z.val =
        (WithLp.fstL 2 ℝ _ _) w.val := by
    simpa [pressureNDWeakPressureProjection] using hp
  have hsecond :=
    pressure_nd_test_gradient_unique μ embed negDiv hDense
      z.val w.val z.property w.property hfirst
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · simpa using hfirst
  · simpa using hsecond

/-- The unique L² distributional gradient, defined on the whole candidate
weak-H¹ domain. -/
noncomputable def pressureNDWeakGradient
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ)) :
    pressureNDWeakH1Candidate μ embed negDiv →ₗ[ℝ]
      pressureNDVectorL2 Ω μ :=
  (pressureNDWeakGradientProjection μ embed negDiv).toLinearMap.comp
    ((LinearEquiv.ofInjective
      (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap
      (pressure_nd_weak_pressure_projection_injective
        μ embed negDiv hDense)).symm.toLinearMap)

/-- The candidate weak gradient is the gradient of each admissible graph pair. -/
theorem pressure_nd_weak_gradient_on_graph
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (z : pressureNDTestGraph μ embed negDiv) :
    pressureNDWeakGradient μ embed negDiv hDense
      ⟨pressureNDWeakPressureProjection μ embed negDiv z,
        LinearMap.mem_range_self
          (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap z⟩ =
      pressureNDWeakGradientProjection μ embed negDiv z := by
  let e := LinearEquiv.ofInjective
    (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap
    (pressure_nd_weak_pressure_projection_injective
      μ embed negDiv hDense)
  change pressureNDWeakGradientProjection μ embed negDiv
    (e.symm (e z)) = pressureNDWeakGradientProjection μ embed negDiv z
  rw [e.symm_apply_apply]

/-- On the whole weak-H¹ candidate, the gradient satisfies the
n_d-dimensional distributional integration-by-parts identity for every test field. -/
theorem pressure_nd_weak_gradient_ibp
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (φ : Φ) (u : pressureNDWeakH1Candidate μ embed negDiv) :
    ⟪embed φ, pressureNDWeakGradient μ embed negDiv hDense u⟫_ℝ =
      ⟪negDiv φ, (u : pressureNDScalarL2 Ω μ)⟫_ℝ := by
  let e := LinearEquiv.ofInjective
    (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap
    (pressure_nd_weak_pressure_projection_injective
      μ embed negDiv hDense)
  let z : pressureNDTestGraph μ embed negDiv := e.symm u
  have hp : pressureNDWeakPressureProjection μ embed negDiv z =
      (u : pressureNDScalarL2 Ω μ) := by
    have he : e z = u := e.apply_symm_apply u
    exact congrArg Subtype.val he
  have h := (pressure_nd_test_graph_mem_iff μ embed negDiv
    z.val).mp z.property φ
  change ⟪embed φ, pressureNDWeakGradientProjection μ embed negDiv z⟫_ℝ =
    ⟪negDiv φ, pressureNDWeakPressureProjection μ embed negDiv z⟫_ℝ at h
  change ⟪embed φ, pressureNDWeakGradientProjection μ embed negDiv (e.symm u)⟫_ℝ =
    ⟪negDiv φ, (u : pressureNDScalarL2 Ω μ)⟫_ℝ
  rw [← hp]
  exact h




end NDWeakGradient

section NDGraphClosure
open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Set (Paper2026.PaperSpatial n_d)} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The completed graph built from the maximal weak-gradient domain is
exactly the original closed distributional-test graph. -/
theorem pressure_nd_weak_graph_eq_test_graph
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ)) :
    pressureNeumannGraphHilbertDomain
      (pressureNDWeakH1Candidate μ embed negDiv)
      (pressureNDWeakGradient μ embed negDiv hDense) =
      pressureNDTestGraph μ embed negDiv := by
  let D := pressureNDWeakH1Candidate μ embed negDiv
  let G := pressureNDWeakGradient μ embed negDiv hDense
  let M := pressureNDTestGraph μ embed negDiv
  apply le_antisymm
  · intro z hz
    have hClosed : IsClosed (M : Set (WithLp 2
        (pressureNDScalarL2 Ω μ × pressureNDVectorL2 Ω μ))) :=
      pressure_nd_test_graph_closed μ embed negDiv
    have hIncluded : Set.range (pressureNeumannTestGraphMap D G) ⊆ (M : Set _) := by
      rintro x ⟨u, rfl⟩
      apply (pressure_nd_test_graph_mem_iff μ embed negDiv _).2
      intro phi
      change ⟪embed phi, G u⟫_ℝ = ⟪negDiv phi, (u : pressureNDScalarL2 Ω μ)⟫_ℝ
      exact pressure_nd_weak_gradient_ibp μ embed negDiv hDense phi u
    have hzClosure : (z : WithLp 2
        (pressureNDScalarL2 Ω μ × pressureNDVectorL2 Ω μ)) ∈
        closure (Set.range (pressureNeumannTestGraphMap D G)) := by
      change z ∈ closure ((LinearMap.range (pressureNeumannTestGraphMap D G)) : Set _)
      rw [← Submodule.topologicalClosure_coe]
      exact hz
    exact (closure_minimal hIncluded hClosed) hzClosure
  · intro z hz
    let x : M := ⟨z, hz⟩
    let u : D :=
      ⟨pressureNDWeakPressureProjection μ embed negDiv x,
       LinearMap.mem_range_self
         (pressureNDWeakPressureProjection μ embed negDiv).toLinearMap x⟩
    have hPair : pressureNeumannTestGraphMap D G u = z := by
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
      apply Prod.ext
      · change (u : pressureNDScalarL2 Ω μ) =
          (WithLp.fstL 2 ℝ _ _) z
        rfl
      · change G u = (WithLp.sndL 2 ℝ _ _) z
        exact pressure_nd_weak_gradient_on_graph μ embed negDiv hDense x
    apply (Submodule.le_topologicalClosure _)
    exact ⟨u, hPair⟩

/-- The Hilbert graph embedding is injective because the distributional
gradient is unique; in particular, the graph represents pressures faithfully. -/
theorem pressure_nd_weak_graph_embedding_injective
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ)) :
    Function.Injective (pressureNeumannGraphHilbertEmbedding
      (pressureNDWeakH1Candidate μ embed negDiv)
      (pressureNDWeakGradient μ embed negDiv hDense)) := by
  let D := pressureNDWeakH1Candidate μ embed negDiv
  let G := pressureNDWeakGradient μ embed negDiv hDense
  apply pressure_neumann_graph_embedding_injective_of_closable D G
  intro z hz
  have hEq := pressure_nd_weak_graph_eq_test_graph μ embed negDiv hDense
  have hzM : (z : WithLp 2
      (pressureNDScalarL2 Ω μ × pressureNDVectorL2 Ω μ)) ∈
      pressureNDTestGraph μ embed negDiv := by
    rw [← hEq]
    exact z.property
  have hSecond := pressure_nd_test_gradient_unique μ embed negDiv hDense
    (z : WithLp 2 (pressureNDScalarL2 Ω μ × pressureNDVectorL2 Ω μ))
    0 hzM (Submodule.zero_mem _) (by
      simpa [pressureNeumannGraphHilbertEmbedding] using hz)
  simpa [pressureNeumannGraphHilbertGradient] using hSecond

/-- Dense scalar members of the weak domain imply dense embedding of its
canonical completed Hilbert graph in pressure L². -/
theorem pressure_nd_weak_graph_embedding_dense
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (hScalarDense : DenseRange ((pressureNDWeakH1Candidate μ embed negDiv).subtype :
      pressureNDWeakH1Candidate μ embed negDiv →
        pressureNDScalarL2 Ω μ)) :
    DenseRange (pressureNeumannGraphHilbertEmbedding
      (pressureNDWeakH1Candidate μ embed negDiv)
      (pressureNDWeakGradient μ embed negDiv hDense)) :=
  pressure_neumann_graph_embedding_dense _ _ hScalarDense



/-- Density of actual scalar test representatives follows from scalar L²
    density and the distributional integration-by-parts identity against
    every vector test. It is *not* separately postulated for the maximal
    weak-H¹ domain. This proof is valid for every n_d. -/
theorem pressure_nd_weak_H1_dense_of_scalar_tests
    {Ψ : Type*}
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (scalarEmbed : Ψ → pressureNDScalarL2 Ω μ)
    (hScalarTestsDense : DenseRange scalarEmbed)
    (hSmoothIBP : ∀ ψ : Ψ,
      ∃ g : pressureNDVectorL2 Ω μ,
        ∀ φ : Φ,
          ⟪embed φ, g⟫_ℝ = ⟪negDiv φ, scalarEmbed ψ⟫_ℝ) :
    DenseRange
      ((pressureNDWeakH1Candidate μ embed negDiv).subtype :
        pressureNDWeakH1Candidate μ embed negDiv →
          pressureNDScalarL2 Ω μ) := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  obtain ⟨ψ, hψ⟩ := (Metric.denseRange_iff.mp hScalarTestsDense) u ε hε
  obtain ⟨g, hg⟩ := hSmoothIBP ψ
  let z : WithLp 2 (pressureNDScalarL2 Ω μ × pressureNDVectorL2 Ω μ) :=
    WithLp.toLp 2 (scalarEmbed ψ, g)
  have hz : z ∈ pressureNDTestGraph μ embed negDiv := by
    apply (pressure_nd_test_graph_mem_iff μ embed negDiv z).2
    intro φ
    change ⟪embed φ, g⟫_ℝ = ⟪negDiv φ, scalarEmbed ψ⟫_ℝ
    exact hg φ
  have hmem : scalarEmbed ψ ∈ pressureNDWeakH1Candidate μ embed negDiv := by
    change ∃ a : pressureNDTestGraph μ embed negDiv,
      pressureNDWeakPressureProjection μ embed negDiv a = scalarEmbed ψ
    exact ⟨⟨z, hz⟩, rfl⟩
  exact ⟨⟨scalarEmbed ψ, hmem⟩, hψ⟩

end NDGraphClosure

end ReservoirSeismicityControl
