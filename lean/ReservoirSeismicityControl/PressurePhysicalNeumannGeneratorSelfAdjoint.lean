import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSelfAdjointGraph
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Physical Neumann generator as a self-adjoint partially defined operator

The previous module proves the full adjoint graph characterization for the
physical semigroup generator. Here we translate that characterization to
Mathlib's native `LinearPMap.IsSelfAdjoint` predicate.

The domain-density argument uses only the self-adjoint unit resolvent and
its exact generator identity. In particular, it does not assume compact
resolvent, a Neumann eigenbasis, Rellich compactness, or bounded Q'.

This theorem does not yet supply a spectral representation or a forced
Duhamel formula for the pressure equation.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractGenerator

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Regard the semigroup generator as Mathlib's partially defined linear map. -/
noncomputable def pressureGeneratorPMap
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H) :
    H →ₗ.[ℝ] H where
  domain := S.generatorDomain
  toFun := S.generator

/-- A self-adjoint unit resolvent whose image lies in the generator
 domain forces that domain to be dense. -/
theorem pressure_unit_resolvent_generator_domain_dense
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hUnit : ∀ h : H,
      ∃ hh : R h ∈ S.generatorDomain,
        S.generator ⟨R h, hh⟩ = R h - h) :
    Dense (S.generatorDomain : Set H) := by
  have hRker : ∀ x : H, R x = 0 → x = 0 := by
    intro x hx
    obtain ⟨hRx, hGen⟩ := hUnit x
    have heq : (⟨R x, hRx⟩ : S.generatorDomain) = 0 :=
      Subtype.ext hx
    have hgen0 : S.generator ⟨R x, hRx⟩ = 0 := by
      rw [heq]
      exact map_zero S.generator
    rw [hgen0, hx, zero_sub] at hGen
    exact (neg_eq_zero.mp hGen.symm)
  have hSep : ∀ z : H, (∀ x : H, ⟪z, R x⟫_ℝ = 0) → z = 0 := by
    intro z hz
    have hRz : R z = 0 := by
      apply ext_inner_right ℝ
      intro x
      calc
        ⟪R z, x⟫_ℝ =
            ⟪z, (ContinuousLinearMap.adjoint R) x⟫_ℝ :=
              (ContinuousLinearMap.adjoint_inner_right R z x).symm
        _ = ⟪z, R x⟫_ℝ := by rw [hAdj]
        _ = 0 := hz x
        _ = ⟪(0 : H), x⟫_ℝ := by simp
    exact hRker z hRz
  have hDenseR : DenseRange R :=
    pressure_neumann_denseRange_of_separating R hSep
  apply Dense.mono (s₁ := Set.range R) (s₂ := (S.generatorDomain : Set H))
    (fun u hu => by
      obtain ⟨x, rfl⟩ := hu
      exact (hUnit x).1)
  exact hDenseR

/-- A densely defined linear operator satisfying the full adjoint graph
 characterization is self-adjoint in Mathlib's native sense. -/
theorem pressure_selfadjoint_pmap_of_graph
    (T : H →ₗ.[ℝ] H)
    (hDense : Dense (T.domain : Set H))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ T.domain,
        ⟪u, T ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ T.domain, T ⟨u, hu⟩ = g) :
    IsSelfAdjoint T := by
  have hDomain : T.adjoint.domain = T.domain := by
    apply Submodule.ext
    intro u
    constructor
    · intro hu
      have hFormal : ∀ v : H, ∀ hv : v ∈ T.domain,
          ⟪u, T ⟨v, hv⟩⟫_ℝ = ⟪T.adjoint ⟨u, hu⟩, v⟫_ℝ := by
        intro v hv
        exact (T.adjoint_isFormalAdjoint hDense ⟨u, hu⟩ ⟨v, hv⟩).symm
      obtain ⟨hu', _⟩ := (hGraph u (T.adjoint ⟨u, hu⟩)).mp hFormal
      exact hu'
    · intro hu
      have hFormal := (hGraph u (T ⟨u, hu⟩)).mpr ⟨hu, rfl⟩
      apply T.mem_adjoint_domain_of_exists u
      refine ⟨T ⟨u, hu⟩, ?_⟩
      intro v
      exact (hFormal v v.property).symm
  apply (LinearPMap.isSelfAdjoint_def).2
  apply LinearPMap.ext hDomain
  intro u hu hu'
  have hFormal : ∀ v : H, ∀ hv : v ∈ T.domain,
      ⟪u, T ⟨v, hv⟩⟫_ℝ = ⟪T.adjoint ⟨u, hu⟩, v⟫_ℝ := by
    intro v hv
    exact (T.adjoint_isFormalAdjoint hDense ⟨u, hu⟩ ⟨v, hv⟩).symm
  obtain ⟨_, hValue⟩ := (hGraph u (T.adjoint ⟨u, hu⟩)).mp hFormal
  exact hValue.symm

/-- The semigroup generator is self-adjoint once its resolvent has the
 established symmetry, unit-domain identity, and adjoint-graph property. -/
theorem pressure_unit_resolvent_generator_isSelfAdjoint
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hBridge : ∀ u f : H,
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔ R (u + f) = u)
    (hUnit : ∀ h : H,
      ∃ hh : R h ∈ S.generatorDomain,
        S.generator ⟨R h, hh⟩ = R h - h) :
    IsSelfAdjoint (pressureGeneratorPMap S) := by
  apply pressure_selfadjoint_pmap_of_graph (pressureGeneratorPMap S)
  · exact pressure_unit_resolvent_generator_domain_dense R S hAdj hUnit
  · intro u g
    exact pressure_unit_resolvent_generator_selfadjoint_graph
      R S hAdj hBridge hUnit u g

end AbstractGenerator

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- Mathlib-native self-adjointness of the generator of the actual
 three-dimensional Neumann diffusion semigroup. The weak physical
 coefficient is k/(beta*eta). No Rellich compactness is assumed. -/
theorem pressure_neumann_3d_physical_generator_isSelfAdjoint
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
      IsSelfAdjoint (pressureGeneratorPMap S) := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, hAdj, _hNonneg, hBridge, hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  exact ⟨hB, S, pressure_unit_resolvent_generator_isSelfAdjoint
    (pressureHilbertWeakResolvent j B hB) S hAdj hBridge hUnit⟩

end PhysicalVolume

end ReservoirSeismicityControl
