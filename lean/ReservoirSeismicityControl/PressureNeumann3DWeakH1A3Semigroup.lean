import ReservoirSeismicityControl.PressureNeumann3DMaximalGraphEquivalence
import ReservoirSeismicityControl.PressureNeumannPhysicalA3L2Semigroup

/-!
# 3D maximal weak-gradient Neumann semigroup

This step combines the *maximal weak H¹ candidate* with the existing
Neumann graph-form and Hille–Yosida semigroup constructions.

Unlike the earlier scalar-core construction, we do not assume a separate
integration-by-parts law for an additional scalar test core. Integration
by parts is already built into the maximal distributional gradient.
Vector-test density guarantees a single-valued gradient. Density of the
resulting weak pressure domain in scalar L² is kept explicitly visible.

The second theorem uses the actual three-dimensional permeability tensor
k/(beta eta) and derives uniform ellipticity from the paper's A3 bounds.

This gives a weak-form generator characterization and a C₀ contraction
semigroup, conditional only on the two density hypotheses and the
coefficient hypotheses. It does NOT assert that the test space has
already been instantiated with C_c^∞, that Ω has been given its
Lebesgue measure, or that the domain has been identified with H¹(Ω).
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The maximal weak-gradient graph, when its test fields and scalar domain
are dense, generates a contraction semigroup for every bounded symmetric
uniformly elliptic vector-field coefficient. There is no auxiliary scalar
core nor a separate test-level IBP hypothesis. -/
theorem pressure_neumann_3d_maximal_weak_semigroup_exists
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hTestsDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (hScalarDense : DenseRange
      ((pressureNeumann3DWeakH1Candidate μ embed negDiv).subtype :
        pressureNeumann3DWeakH1Candidate μ embed negDiv →
          pressureNeumann3DScalarL2 Ω μ))
    (C : pressureNeumann3DVectorL2 Ω μ →L[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (c : ℝ) (hc : 0 < c)
    (hEll : ∀ z : pressureNeumann3DVectorL2 Ω μ,
      c * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ)
    (hSym : ∀ z w : pressureNeumann3DVectorL2 Ω μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 Ω μ),
      ∀ u f : pressureNeumann3DScalarL2 Ω μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNeumann3DWeakH1Candidate μ embed negDiv)
            (pressureNeumann3DWeakGradient μ embed negDiv hTestsDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNeumann3DWeakH1Candidate μ embed negDiv)
              (pressureNeumann3DWeakGradient μ embed negDiv hTestsDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
  let G := pressureNeumann3DWeakGradient μ embed negDiv hTestsDense
  let j := pressureNeumannGraphHilbertEmbedding D G
  let g := pressureNeumannGraphHilbertGradient D G
  let E := pressureNeumannGraphCoefficientEnergy D G C
  let B₁ := pressureNeumannGraphCoefficientUnitForm D G C
  have hForm₁ : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B₁ x y = ⟪j x, j y⟫_ℝ + E x y := by
    intro x y
    exact pressure_neumann_graph_coefficient_unit_form_apply D G C x y
  have hE : ∀ x : pressureNeumannGraphHilbertDomain D G, 0 ≤ E x x := by
    intro x
    exact pressure_neumann_bounded_coefficient_form_nonneg g C c hc hEll x
  have hSymE : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric g C hSym
  have hSymB : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B₁ x y = B₁ y x := by
    intro x y
    calc
      B₁ x y = ⟪j x, j y⟫_ℝ + E x y := hForm₁ x y
      _ = ⟪j y, j x⟫_ℝ + E y x := by
        rw [real_inner_comm (j x) (j y), hSymE x y]
      _ = B₁ y x := (hForm₁ y x).symm
  have hB₁ : IsCoercive B₁ :=
    pressure_neumann_graph_coefficient_unit_form_coercive D G C c hc hEll
  have hInjective : Function.Injective j :=
    pressure_neumann_3d_weak_graph_embedding_injective μ embed negDiv hTestsDense
  have hRange : DenseRange j :=
    pressure_neumann_3d_weak_graph_embedding_dense
      μ embed negDiv hTestsDense hScalarDense
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ E hB₁ hForm₁ hE hSymB hInjective hRange
  refine ⟨S, ?_⟩
  intro u f
  change (∃ x : pressureNeumannGraphHilbertDomain D G,
      j x = u ∧ ∀ v : pressureNeumannGraphHilbertDomain D G,
        E x v = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSymB hInjective hRange).generatorDomain,
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSymB hInjective hRange).generator ⟨u, hu⟩ = -f
  exact pressure_neumann_dense_generator_weak_iff
    j B₁ E hB₁ hForm₁ hE hSymB hInjective hRange u f

/-- For the actual three-dimensional permeability/viscosity tensor in A3,
construct the Neumann C₀ contraction semigroup on the maximal L² weak-gradient
domain, without assuming a separate scalar-gradient core or Green identity. -/
theorem pressure_neumann_3d_maximal_weak_A3_semigroup_exists
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hTestsDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (hScalarDense : DenseRange
      ((pressureNeumann3DWeakH1Candidate μ embed negDiv).subtype :
        pressureNeumann3DWeakH1Candidate μ embed negDiv →
          pressureNeumann3DScalarL2 Ω μ))
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin 3 → ℝ),
      km * (∑ i : Fin 3, (z i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin 3 → ℝ),
      (∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j) ≤
        kM * (∑ i : Fin 3, (z i) ^ 2))
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 Ω μ),
      ∀ u f : pressureNeumann3DScalarL2 Ω μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNeumann3DWeakH1Candidate μ embed negDiv)
            (pressureNeumann3DWeakGradient μ embed negDiv hTestsDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNeumann3DWeakH1Candidate μ embed negDiv)
              (pressureNeumann3DWeakGradient μ embed negDiv hTestsDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hA3 := pressure_neumann_physical_A3_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNeumann3DVectorL2 Ω μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hSym : ∀ z w : pressureNeumann3DVectorL2 Ω μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  exact pressure_neumann_3d_maximal_weak_semigroup_exists
    μ embed negDiv hTestsDense hScalarDense C
    (km / (beta * etaM)) hc hEll hSym

end ReservoirSeismicityControl
