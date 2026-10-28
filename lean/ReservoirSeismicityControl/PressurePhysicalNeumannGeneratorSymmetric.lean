import ReservoirSeismicityControl.PressurePhysicalNeumannUnitResolventGenerator

/-!
# Symmetry of the physical Neumann diffusion generator

The unit weak resolvent has already been identified with the generator
of the physical Neumann contraction semigroup.  We show here that
self-adjointness of the *bounded* unit resolvent and the exact graph
identity imply symmetry of the (generally unbounded) generator.

There is no compact embedding hypothesis, no eigenbasis, and no
assumption on derivatives of the well fluxes.  This is a useful
intermediate certificate, but not yet a proof of the spectral Duhamel
representation required to transfer the general-spectrum A5 theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractGenerator

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The inverse graph of a self-adjoint unit resolvent is symmetric.
If `R (u+f)=u` and `R (v+g)=v`, then `<f,v>=<u,g>`. -/
theorem pressure_unit_resolvent_graph_symmetric
    (R : H →L[ℝ] H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (u f v g : H)
    (hu : R (u + f) = u)
    (hv : R (v + g) = v) :
    ⟪f, v⟫_ℝ = ⟪u, g⟫_ℝ := by
  have hSym : ∀ x y : H, ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ := by
    intro x y
    calc
      ⟪R x, y⟫_ℝ = ⟪x, (ContinuousLinearMap.adjoint R) y⟫_ℝ :=
        (ContinuousLinearMap.adjoint_inner_right R x y).symm
      _ = ⟪x, R y⟫_ℝ := by rw [hAdj]
  have h : ⟪u + f, v⟫_ℝ = ⟪u, v + g⟫_ℝ := by
    calc
      ⟪u + f, v⟫_ℝ = ⟪u + f, R (v + g)⟫_ℝ := by rw [hv]
      _ = ⟪R (u + f), v + g⟫_ℝ := (hSym _ _).symm
      _ = ⟪u, v + g⟫_ℝ := by rw [hu]
  have h' : ⟪u, v⟫_ℝ + ⟪f, v⟫_ℝ =
      ⟪u, v⟫_ℝ + ⟪u, g⟫_ℝ := by
    simpa only [inner_add_left, inner_add_right] using h
  exact add_left_cancel h'

/-- The generator identified with the negative weak Neumann operator is
symmetric on its *actual generator domain*.  This theorem asks only
for the unit-resolvent graph characterization, proved in the earlier
physical bridge; it does not postulate PDE eigenfunctions. -/
theorem pressure_unit_resolvent_generator_symmetric
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hBridge : ∀ u f : H,
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔ R (u + f) = u)
    (u v : H)
    (hu : u ∈ S.generatorDomain)
    (hv : v ∈ S.generatorDomain) :
    ⟪S.generator ⟨u, hu⟩, v⟫_ℝ =
      ⟪u, S.generator ⟨v, hv⟩⟫_ℝ := by
  have huR : R (u + -(S.generator ⟨u, hu⟩)) = u :=
    (hBridge u (-(S.generator ⟨u, hu⟩))).mp ⟨hu, by simp⟩
  have hvR : R (v + -(S.generator ⟨v, hv⟩)) = v :=
    (hBridge v (-(S.generator ⟨v, hv⟩))).mp ⟨hv, by simp⟩
  have h := pressure_unit_resolvent_graph_symmetric R hAdj
    u (-(S.generator ⟨u, hu⟩))
    v (-(S.generator ⟨v, hv⟩)) huR hvR
  simpa only [inner_neg_left, inner_neg_right, neg_inj] using h

end AbstractGenerator

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- The physical 3D Neumann generator is symmetric on its generator
 domain, under the existing ellipticity and measurability assumptions.
 No Rellich compactness or spectral representation is assumed. -/
theorem pressure_neumann_3d_physical_generator_symmetric
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
      ∀ u v : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        ∀ (hu : u ∈ S.generatorDomain) (hv : v ∈ S.generatorDomain),
          ⟪S.generator ⟨u, hu⟩, v⟫_ℝ =
            ⟪u, S.generator ⟨v, hv⟩⟫_ℝ := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, hAdj, _hNonneg, hBridge, _hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨hB, S, ?_⟩
  intro u v hu hv
  exact pressure_unit_resolvent_generator_symmetric
    (pressureHilbertWeakResolvent j B hB) S hAdj hBridge u v hu hv

end PhysicalVolume

end ReservoirSeismicityControl
