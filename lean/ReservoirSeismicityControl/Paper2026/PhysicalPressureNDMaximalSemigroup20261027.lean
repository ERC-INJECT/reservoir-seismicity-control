import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDMaximalWeak20261027
import ReservoirSeismicityControl.PressureNeumannPhysicalA3ClosedGradientSemigroup
import Mathlib.Tactic

/-!
# Physical A3 maximal weak-Neumann semigroup in n_d = 1,2,3

This instantiates the verified dimension-independent Neumann form construction
on the actual n_d-dimensional maximal distributional weak-H¹ domain.
Unlike PhysicalPressureNDSemigroup20261027 it does not assume a separately
specified G, test-level hIBP, or a dense auxiliary D: these are constructed
or deduced from the weak-gradient graph. Vector-test density, scalar-test density, smooth-test IBP and A3 physical
tensor hypotheses are sufficient; scalar weak-pressure density is proved.

The two density facts are geometric smooth-test applicability obligations;
there is no claim here to have constructed C_c^∞(Ω) for each n_d.
-/

namespace ReservoirSeismicityControl

variable {n_d : ℕ}

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

variable {Ω : Set (Paper2026.PaperSpatial n_d)} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- The maximal weak-gradient graph, when its test fields and scalar domain
are dense, generates a contraction semigroup for every bounded symmetric
uniformly elliptic vector-field coefficient. There is no auxiliary scalar
core nor a separate test-level IBP hypothesis. -/
theorem pressure_nd_maximal_weak_semigroup_exists
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hTestsDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (hScalarDense : DenseRange
      ((pressureNDWeakH1Candidate μ embed negDiv).subtype :
        pressureNDWeakH1Candidate μ embed negDiv →
          pressureNDScalarL2 Ω μ))
    (C : pressureNDVectorL2 Ω μ →L[ℝ] pressureNDVectorL2 Ω μ)
    (c : ℝ) (hc : 0 < c)
    (hEll : ∀ z : pressureNDVectorL2 Ω μ,
      c * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ)
    (hSym : ∀ z w : pressureNDVectorL2 Ω μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNDScalarL2 Ω μ),
      ∀ u f : pressureNDScalarL2 Ω μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNDWeakH1Candidate μ embed negDiv)
            (pressureNDWeakGradient μ embed negDiv hTestsDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNDWeakH1Candidate μ embed negDiv)
              (pressureNDWeakGradient μ embed negDiv hTestsDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  let D := pressureNDWeakH1Candidate μ embed negDiv
  let G := pressureNDWeakGradient μ embed negDiv hTestsDense
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
    pressure_nd_weak_graph_embedding_injective μ embed negDiv hTestsDense
  have hRange : DenseRange j :=
    pressure_nd_weak_graph_embedding_dense
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

/-- For the actual n_d-dimensional permeability/viscosity tensor in A3,
construct the Neumann C₀ contraction semigroup on the maximal L² weak-gradient
domain, without assuming a separate scalar-gradient core or Green identity. -/
theorem pressure_nd_maximal_weak_A3_semigroup_exists
    {Ψ : Type*}
    (hd : Paper2026.PaperSpatialDimension n_d)
    (embed : Φ →ₗ[ℝ] pressureNDVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNDScalarL2 Ω μ)
    (hTestsDense : DenseRange (embed : Φ → pressureNDVectorL2 Ω μ))
    (scalarEmbed : Ψ → pressureNDScalarL2 Ω μ)
    (hScalarTestsDense : DenseRange scalarEmbed)
    (hSmoothIBP : ∀ ψ : Ψ,
      ∃ g : pressureNDVectorL2 Ω μ,
        ∀ φ : Φ,
          ⟪embed φ, g⟫_ℝ = ⟪negDiv φ, scalarEmbed ψ⟫_ℝ)
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (z i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j) ≤
        kM * (∑ i : Fin n_d, (z i) ^ 2))
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let C := paperPressureL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNDScalarL2 Ω μ),
      ∀ u f : pressureNDScalarL2 Ω μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNDWeakH1Candidate μ embed negDiv)
            (pressureNDWeakGradient μ embed negDiv hTestsDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNDWeakH1Candidate μ embed negDiv)
              (pressureNDWeakGradient μ embed negDiv hTestsDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  let C := paperPressureL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hA3 := paper_pressure_A3_nd_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNDVectorL2 Ω μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hSym : ∀ z w : pressureNDVectorL2 Ω μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  have hScalarDense : DenseRange
      ((pressureNDWeakH1Candidate μ embed negDiv).subtype :
        pressureNDWeakH1Candidate μ embed negDiv →
          pressureNDScalarL2 Ω μ) :=
    pressure_nd_weak_H1_dense_of_scalar_tests
      μ embed negDiv scalarEmbed hScalarTestsDense hSmoothIBP
  exact pressure_nd_maximal_weak_semigroup_exists
    μ embed negDiv hTestsDense hScalarDense C
    (km / (beta * etaM)) hc hEll hSym


end ReservoirSeismicityControl
