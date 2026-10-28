import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSelfAdjoint

/-!
# Self-adjoint, nonpositive physical Neumann generator

The previous module identifies the generator as a densely defined
self-adjoint linear partial map on physical scalar L². Here the same
physical weak-energy identity shows its quadratic form is nonpositive.

For every u in the generator domain, the generator L=-A satisfies

  ⟪L u,u⟫ ≤ 0.

This follows directly from the positive elliptic energy in the weak
Neumann formulation. There is no compactness assumption, spectral
basis assumption, or hypothesis on derivatives of the well rates.

This establishes the correct spectral *sign*, but does not yet construct
an L² spectral representation or the forced Duhamel formula for (A5).
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractWeakGenerator

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Nonnegative weak diffusion energy makes the associated generator
    nonpositive on its domain. No differentiation of any source is needed. -/
theorem pressure_weak_generator_inner_nonpos
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (j : V →L[ℝ] H)
    (E : V →L[ℝ] V →L[ℝ] ℝ)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hWeak : ∀ u f : H,
      (∃ x : V, j x = u ∧ ∀ v : V, E x v = ⟪f, j v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f)
    (u : H) (hu : u ∈ S.generatorDomain) :
    ⟪S.generator ⟨u, hu⟩, u⟫_ℝ ≤ 0 := by
  let g : H := S.generator ⟨u, hu⟩
  have hGraph : ∃ hv : u ∈ S.generatorDomain,
      S.generator ⟨u, hv⟩ = -(-g) := by
    refine ⟨hu, ?_⟩
    simp [g]
  obtain ⟨x, hx, hEq⟩ := (hWeak u (-g)).mpr hGraph
  have hPos : 0 ≤ ⟪-g, u⟫_ℝ := by
    calc
      0 ≤ E x x := hE x
      _ = ⟪-g, j x⟫_ℝ := hEq x
      _ = ⟪-g, u⟫_ℝ := by rw [hx]
  have hNeg : 0 ≤ -⟪g, u⟫_ℝ := by
    simpa only [inner_neg_left] using hPos
  change ⟪g, u⟫_ℝ ≤ 0
  exact neg_nonneg.mp hNeg

end AbstractWeakGenerator

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- The actual physical Neumann generator is self-adjoint and
nonpositive. The coefficient multiplier is k/(beta*eta), and the energy
inequality follows from the uniform ellipticity of the physical tensor.
No spectral or compactness hypotheses are added. -/
theorem pressure_neumann_3d_physical_generator_selfAdjoint_nonpositive
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (k : ↥(Ω : Set pressureNeumannE3) → Fin 3 → Fin 3 → ℝ)
    (eta : ↥(Ω : Set pressureNeumannE3) → ℝ)
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
    let μ := pressureNeumann3DRestrictedMeasure Ω
      (volume : Measure pressureNeumannE3)
    let embed := pressureNeumann3DRestrictedVectorL2Embed Ω
      (volume : Measure pressureNeumannE3) hΩ
    let negDiv := pressureNeumann3DRestrictedNegDivL2 Ω
      (volume : Measure pressureNeumannE3) hΩ
    let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
    let hTests := pressure_neumann_3d_canonical_vector_tests_dense Ω
      (volume : Measure pressureNeumannE3) hΩ
    let G := pressureNeumann3DWeakGradient μ embed negDiv hTests
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    let j := pressureNeumannGraphHilbertEmbedding D G
    let E := pressureNeumannGraphCoefficientEnergy D G C
    let B := pressureNeumannGraphCoefficientUnitForm D G C
    ∃ (hB : IsCoercive B)
      (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)),
      IsSelfAdjoint (pressureGeneratorPMap S) ∧
      ∀ u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        ∀ hu : u ∈ S.generatorDomain,
          ⟪S.generator ⟨u, hu⟩, u⟫_ℝ ≤ 0 := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, hAdj, _hNonneg, hBridge, hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hSA : IsSelfAdjoint (pressureGeneratorPMap S) :=
    pressure_unit_resolvent_generator_isSelfAdjoint
      (pressureHilbertWeakResolvent j B hB) S hAdj hBridge hUnit
  have hA3 := pressure_neumann_physical_A3_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNeumann3DVectorL2
        (Ω : Set pressureNeumannE3) μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hE : ∀ x : pressureNeumannGraphHilbertDomain D G,
      0 ≤ E x x := by
    intro x
    exact pressure_neumann_bounded_coefficient_form_nonneg
      (pressureNeumannGraphHilbertGradient D G) C
      (km / (beta * etaM))
      (div_pos hkm (mul_pos hbeta hetaM)) hEll x
  have hForm : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B x y = ⟪j x, j y⟫_ℝ + E x y := by
    intro x y
    exact pressure_neumann_graph_coefficient_unit_form_apply D G C x y
  have hWeak : ∀ u f : pressureNeumann3DScalarL2
      (Ω : Set pressureNeumannE3) μ,
      (∃ x : pressureNeumannGraphHilbertDomain D G,
        j x = u ∧ ∀ v : pressureNeumannGraphHilbertDomain D G,
          E x v = ⟪f, j v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f := by
    intro u f
    exact (pressure_neumann_weak_energy_graph_iff
      j B E hB hForm u f).trans (hBridge u f).symm
  refine ⟨hB, S, hSA, ?_⟩
  intro u hu
  exact pressure_weak_generator_inner_nonpos S j E hE hWeak u hu

end PhysicalVolume

end ReservoirSeismicityControl
