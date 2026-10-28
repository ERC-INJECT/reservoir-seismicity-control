import ReservoirSeismicityControl.PressurePhysicalNeumannResolventEigenmode

/-!
# Domain of the physical Neumann generator as the range of its unit resolvent

For the physical diffusion generator `L = -A` and its weak unit resolvent
`R = (I + A)⁻¹`, the resolvent image is EXACTLY the generator domain.
Moreover, `R` is injective and the identity

    R (u - L u) = u    for u in D(L)

holds.  Thus the bounded operator `R` parametrizes the full domain of the
unbounded generator, not merely its eigenvectors.

The result follows from the previously formalized weak resolvent and
generator bridge.  No compactness, eigenbasis, or bounded derivative of the
well fluxes is assumed.  This is not yet a spectral representation or (A5).
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractResolventRange

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The unit resolvent is a one-to-one parametrization of the entire
semigroup generator domain; the resolvent identity holds on that domain. -/
theorem pressure_unit_resolvent_range_eq_generator_domain
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hBridge : ∀ u f : H,
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔ R (u + f) = u)
    (hUnit : ∀ h : H,
      ∃ hh : R h ∈ S.generatorDomain,
        S.generator ⟨R h, hh⟩ = R h - h) :
    Set.range R = (S.generatorDomain : Set H) ∧
    Function.Injective R ∧
    (∀ (u : H) (hu : u ∈ S.generatorDomain),
      R (u - S.generator ⟨u, hu⟩) = u) := by
  have hRecover : ∀ (u : H) (hu : u ∈ S.generatorDomain),
      R (u - S.generator ⟨u, hu⟩) = u := by
    intro u hu
    have h := (hBridge u (-S.generator ⟨u, hu⟩)).mp
      ⟨hu, by simp⟩
    simpa only [sub_eq_add_neg] using h
  have hRange : Set.range R = (S.generatorDomain : Set H) := by
    ext u
    constructor
    · rintro ⟨h, rfl⟩
      exact (hUnit h).1
    · intro hu
      exact ⟨u - S.generator ⟨u, hu⟩, hRecover u hu⟩
  have hKernel : ∀ z : H, R z = 0 → z = 0 := by
    intro z hz
    obtain ⟨hRDomain, hG⟩ := hUnit z
    have heq : (⟨R z, hRDomain⟩ : S.generatorDomain) = 0 :=
      Subtype.ext hz
    have hGzero : S.generator ⟨R z, hRDomain⟩ = 0 := by
      rw [heq]
      exact map_zero S.generator
    rw [hGzero, hz, zero_sub] at hG
    exact (neg_eq_zero.mp hG.symm)
  have hInjective : Function.Injective R := by
    intro x y hxy
    have hzero : R (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hKernel _ hzero)
  exact ⟨hRange, hInjective, hRecover⟩

end AbstractResolventRange

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- Full resolvent-range characterization of the actual physical Neumann
3D pressure generator for coefficient `k/(beta*eta)`. -/
theorem pressure_neumann_3d_physical_unit_resolvent_exact_range
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
      let R := pressureHilbertWeakResolvent j B hB
      Set.range R = (S.generatorDomain : Set _) ∧
      Function.Injective R ∧
      (∀ (u : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
        (hu : u ∈ S.generatorDomain),
          R (u - S.generator ⟨u, hu⟩) = u) := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, _hAdj, _hNonneg, hBridge, hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨hB, S, ?_⟩
  dsimp only
  exact pressure_unit_resolvent_range_eq_generator_domain
    (pressureHilbertWeakResolvent j B hB) S hBridge hUnit

end PhysicalVolume

end ReservoirSeismicityControl
