import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSymmetric

/-!
# Maximal symmetry of the physical Neumann generator

The generator L of the physical Neumann contraction semigroup has the
self-adjoint graph property: any pair (u,g) satisfying the formal-adjoint
identity against all elements of its generator domain is already a pair
in the graph of L.

The proof uses only the symmetric unit weak resolvent R=(I-L)⁻¹, the
exact graph correspondence, and the existence of R h in D(L) with
L(R h)=R h-h. It does not assume compact resolvent, an eigenbasis,
a spectral measure, or time derivatives of the well inputs.

This is a domain-sensitive self-adjointness statement. Its translation to
Mathlib's `LinearPMap.IsSelfAdjoint` is a separate representation step.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractGenerator

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A symmetric unit resolvent and an exact unit-resolvent graph identity
show that the generator graph equals its formal adjoint graph. The
statement includes the full *domain* characterization, not only
symmetry on pairs of already-admissible states. -/
theorem pressure_unit_resolvent_generator_selfadjoint_graph
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hBridge : ∀ u f : H,
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔ R (u + f) = u)
    (hUnit : ∀ h : H,
      ∃ hh : R h ∈ S.generatorDomain,
        S.generator ⟨R h, hh⟩ = R h - h)
    (u g : H) :
    (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
      ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
    ∃ hu : u ∈ S.generatorDomain,
      S.generator ⟨u, hu⟩ = g := by
  constructor
  · intro hFormal
    have hSymR (x y : H) : ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ := by
      calc
        ⟪R x, y⟫_ℝ =
            ⟪x, (ContinuousLinearMap.adjoint R) y⟫_ℝ :=
              (ContinuousLinearMap.adjoint_inner_right R x y).symm
        _ = ⟪x, R y⟫_ℝ := by rw [hAdj]
    have hRu : R (u - g) = u := by
      apply ext_inner_right ℝ
      intro x
      obtain ⟨hx, hLx⟩ := hUnit x
      have hTest : ⟪u, R x - x⟫_ℝ = ⟪g, R x⟫_ℝ := by
        simpa only [hLx] using hFormal (R x) hx
      calc
        ⟪R (u - g), x⟫_ℝ = ⟪u - g, R x⟫_ℝ := hSymR _ _
        _ = ⟪u, R x⟫_ℝ - ⟪g, R x⟫_ℝ := by rw [inner_sub_left]
        _ = ⟪u, R x⟫_ℝ - ⟪u, R x - x⟫_ℝ := by rw [← hTest]
        _ = ⟪u, x⟫_ℝ := by rw [inner_sub_right]; ring
    have hRu' : R (u + (-g)) = u := by
      simpa only [sub_eq_add_neg] using hRu
    obtain ⟨hu, hLu⟩ := (hBridge u (-g)).mpr hRu'
    exact ⟨hu, by simpa only [neg_neg] using hLu⟩
  · rintro ⟨hu, hLu⟩ v hv
    have hSym := pressure_unit_resolvent_generator_symmetric
      R S hAdj hBridge u v hu hv
    calc
      ⟪u, S.generator ⟨v, hv⟩⟫_ℝ =
          ⟪S.generator ⟨u, hu⟩, v⟫_ℝ := hSym.symm
      _ = ⟪g, v⟫_ℝ := by rw [hLu]

end AbstractGenerator

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- The physical three-dimensional Neumann generator has a self-adjoint
operator graph. This uses the weak resolvent built from k/(beta*eta).
No compact embedding, spectral measure, or new regularity of Q is assumed. -/
theorem pressure_neumann_3d_physical_generator_selfadjoint_graph
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
      ∀ u g : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∀ v : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
          ∀ hv : v ∈ S.generatorDomain,
            ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = g := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, hAdj, _hNonneg, hBridge, hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  exact ⟨hB, S, fun u g =>
    pressure_unit_resolvent_generator_selfadjoint_graph
      (pressureHilbertWeakResolvent j B hB) S
      hAdj hBridge hUnit u g⟩

end PhysicalVolume

end ReservoirSeismicityControl
