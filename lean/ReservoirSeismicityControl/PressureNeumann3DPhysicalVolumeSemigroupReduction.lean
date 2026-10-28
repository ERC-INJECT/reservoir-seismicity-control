import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeCoordinateIBP
import ReservoirSeismicityControl.PressureNeumann3DWeakH1A3Semigroup

/-!
# Physical 3D Neumann semigroup: reduction to one explicit smooth IBP identity

Unlike the previous generic semigroup theorem, this statement fixes the
actual three-dimensional Euclidean volume measure and the exact smooth
compactly supported test-field embedding and negative divergence.

It does not ask for either abstract dense-range hypothesis: both are
discharged using the recently completed density results and the supplied
smooth IBP property.

IMPORTANT: `hSmoothIBP` is an outstanding *concrete physical* identity,
not a theorem established by this file. The coordinate-wise physical IBP
lemma in the imported module is the first part of proving `hSmoothIBP`.
This file is an honest proof reduction, NOT an unconditional semigroup theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

variable (Ω : Opens pressureNeumannE3)

/-- Under the *single explicit* physical smooth-gradient IBP identity,
the bounded-elliptic Neumann diffusion operator built from the true 3D
coefficient has a strongly continuous contraction semigroup.

The theorem assumes neither test-field density nor maximal weak-pressure
domain density; both follow from already proved results.
-/
theorem pressure_neumann_3d_physical_volume_A3_semigroup_of_ibp
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (hSmoothIBP : ∀ ψ : pressureNeumann3DSmoothScalarTests Ω,
      ∃ g : pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω
          (volume : Measure pressureNeumannE3)),
        ∀ φ : pressureNeumann3DSmoothVectorTests Ω,
          ⟪pressureNeumann3DRestrictedVectorL2Embed Ω
              (volume : Measure pressureNeumannE3) hΩ φ, g⟫_ℝ =
            ⟪pressureNeumann3DRestrictedNegDivL2 Ω
                (volume : Measure pressureNeumannE3) hΩ φ,
              pressureNeumann3DRestrictedScalarL2Embed Ω
                (volume : Measure pressureNeumannE3) hΩ ψ⟫_ℝ)
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
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ),
      ∀ u f : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          pressureNeumannGraphHilbertEmbedding D G x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding D G v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  letI : IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω
      (volume : Measure pressureNeumannE3)) :=
    pressure_neumann_3d_restricted_measure_finite Ω
      (volume : Measure pressureNeumannE3) hΩ
  have hTests : DenseRange
      (pressureNeumann3DRestrictedVectorL2Embed Ω
        (volume : Measure pressureNeumannE3) hΩ :
        pressureNeumann3DSmoothVectorTests Ω →
          pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3)
            (pressureNeumann3DRestrictedMeasure Ω
              (volume : Measure pressureNeumannE3))) :=
    pressure_neumann_3d_canonical_vector_tests_dense Ω
      (volume : Measure pressureNeumannE3) hΩ
  have hDomain := pressure_neumann_3d_restricted_weak_H1_dense_of_smooth_ibp
    Ω (volume : Measure pressureNeumannE3) hΩ hSmoothIBP
  exact pressure_neumann_3d_maximal_weak_A3_semigroup_exists
    (pressureNeumann3DRestrictedMeasure Ω
      (volume : Measure pressureNeumannE3))
    (pressureNeumann3DRestrictedVectorL2Embed Ω
      (volume : Measure pressureNeumannE3) hΩ)
    (pressureNeumann3DRestrictedNegDivL2 Ω
      (volume : Measure pressureNeumannE3) hΩ)
    hTests hDomain k eta beta km kM etam etaM
    hbeta hkm hkM hetam hetaM hEtaLo hEtaHi
    hKSym hKLo hKHi hTensor

end ReservoirSeismicityControl
