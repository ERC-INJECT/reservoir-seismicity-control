import ReservoirSeismicityControl.PressureNeumann3DSmoothL2Bridge

/-!
# 3D Neumann form semigroup for actual smooth vector tests

This is the final downstream realization of the *conditional* Neumann
semigroup theorem with a genuine smooth test-field type and its physical
negative divergence. The realization data must first be constructed for
volume restricted to the actual reservoir Ω.

The result derives scalar-domain density from a scalar core, constructs
and uses the A3 elliptic tensor multiplier and applies the existing graph
semigroup theorem. No scalar core or test density proof is postulated as a
new global axiom: all required analytic facts are fields of an explicit
realization structure, and proving they hold remains an open obligation.

The theorem is NOT yet the physical Lipschitz-domain H¹ or heat-kernel
regularity theorem claimed in Appendix A. It is a precise endpoint to which
those still-missing analytic proofs can be connected.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

variable (Ω : Opens pressureNeumannE3)
variable (μ : Measure (Ω : Set pressureNeumannE3))

/-- Once the smooth tests have their verified L² realization, Assumption 3's
symmetric uniformly elliptic tensor defines a Neumann-form semigroup.
This is a theorem about the weak operator associated with the *actual*
compactly supported smooth tests, not an unidentified abstract Φ. -/
theorem pressure_neumann_3d_smooth_A3_semigroup_exists
    (r : PressureNeumann3DSmoothL2Realization Ω μ)
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
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ),
      ∀ u f : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv)
            (pressureNeumann3DWeakGradient μ r.embed r.negDiv r.testsDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNeumann3DWeakH1Candidate μ r.embed r.negDiv)
              (pressureNeumann3DWeakGradient μ r.embed r.negDiv r.testsDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  exact pressure_neumann_3d_maximal_weak_A3_semigroup_exists
    μ r.embed r.negDiv r.testsDense
    (PressureNeumann3DSmoothL2Realization.weak_H1_dense Ω μ r)
    k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor

end ReservoirSeismicityControl
