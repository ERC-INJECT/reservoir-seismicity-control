import ReservoirSeismicityControl.PaperA5Physical3DCanonicalPath
import ReservoirSeismicityControl.PaperNearWeakNeumannMovingDerivative
import Mathlib.Tactic

/-!
# Stage 79 — physical 3D moving near-field observation

Stage 78 builds the actual three-dimensional Neumann form semigroup and a
canonical physical pressure path in the weak operator domain.  Stage 63
establishes the moving-observation product rule once both ambient paths are
differentiable at the observation time and the pressure operator image is
continuous.

This module combines those verified results without assuming a separate
weak-generator identification, physical path correspondence, operator-image
continuity, or energy-form symmetry.  The energy symmetry follows from the
physical anisotropic tensor.  No derivative of any well rate is needed.

The differentiability of the physical pressure and SR cutoff observation
weight, and the latter's weak Neumann domain membership, are *not* derived
by this theorem.  Those remain the next physical analytic obligations.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix NNReal

set_option maxHeartbeats 4000000

/-- Symmetry of the canonical weak energy is inherited from symmetry of
its physical form before transport to the range of the energy embedding. -/
theorem pressure_A5_canonical_range_energy_symmetric
    {U H : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : U →L[ℝ] H) (Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hjinj : Function.Injective j)
    (hSym : ∀ x y : U, Eform x y = Eform y x) :
    ∀ x y : LinearMap.range j.toLinearMap,
      pressureA5CanonicalRangeEnergy j Eform hjinj x y =
        pressureA5CanonicalRangeEnergy j Eform hjinj y x := by
  intro x y
  let e := pressureA5CanonicalFormRangeEquiv j hjinj
  have hx := pressure_A5_canonical_range_energy_eq j Eform hjinj
    (e.symm x) (e.symm y)
  have hy := pressure_A5_canonical_range_energy_eq j Eform hjinj
    (e.symm y) (e.symm x)
  have hxx : e (e.symm x) = x := e.apply_symm_apply x
  have hyy : e (e.symm y) = y := e.apply_symm_apply y
  rw [hxx, hyy] at hx hy
  exact hx.trans ((hSym _ _).trans hy.symm)

/-- The complete moving near-field derivative assertion for a canonical
weak Neumann pressure path.  This named proposition keeps the very large
3D physical specialization from repeatedly unfolding its dependent types.
Unfolding this definition recovers exactly the Stage 79 conclusion. -/
def pressureA5CanonicalMovingNearPathProperty
    {U H : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : U →L[ℝ] H) (E : U →L[ℝ] U →L[ℝ] ℝ)
    (hInj : Function.Injective j) (hDense : DenseRange j)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H) : Prop :=
  ∀ (T : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
      (hq : ∀ i : Fin m, Integrable (q i)
        (volume.restrict (Set.Ico 0 (T : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
      (hBound : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i),
    ∃ p : ℝ → pressureWeakNeumannDomain
        (LinearMap.range j.toLinearMap)
        (pressureA5CanonicalRangeEnergy j E hInj),
      (∀ τ : ℝ,
        (((p τ : LinearMap.range j.toLinearMap) : H)) =
          S (pressureA5HorizonClip T τ) (p₀ : H) +
            pressureA5ForwardDuhamel S
              (pressureA5HorizonClip T τ) m f q) ∧
      ∀ (w : ℝ → pressureWeakNeumannDomain
           (LinearMap.range j.toLinearMap)
           (pressureA5CanonicalRangeEnergy j E hInj))
        (wdot pdot : H) (τ : ℝ),
        HasDerivAt
          (fun s : ℝ => (((w s : LinearMap.range j.toLinearMap) : H)))
          wdot τ →
        HasDerivAt
          (fun s : ℝ => (((p s : LinearMap.range j.toLinearMap) : H)))
          pdot τ →
        HasDerivAt
          (paperNearWeakNeumannMovingObservation
            (LinearMap.range j.toLinearMap)
            (pressureA5CanonicalRangeEnergy j E hInj)
            (pressure_A5_canonical_range_separates j hInj hDense)
            w p)
          (⟪wdot, pressureWeakNeumannOperator
              (LinearMap.range j.toLinearMap)
              (pressureA5CanonicalRangeEnergy j E hInj)
              (pressure_A5_canonical_range_separates j hInj hDense)
              (p τ)⟫_ℝ +
           ⟪pressureWeakNeumannOperator
              (LinearMap.range j.toLinearMap)
              (pressureA5CanonicalRangeEnergy j E hInj)
              (pressure_A5_canonical_range_separates j hInj hDense)
              (w τ), pdot⟫_ℝ) τ

/-- General step: a continuous canonical weak Neumann image and a
symmetric energy imply the moving near-field product rule.  This avoids
re-elaborating the physical 3D construction within the derivative proof. -/
theorem pressure_A5_canonical_moving_near_of_continuous_path
    {U H : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : U →L[ℝ] H) (E : U →L[ℝ] U →L[ℝ] ℝ)
    (hInj : Function.Injective j) (hDense : DenseRange j)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hESym : ∀ x y : U, E x y = E y x)
    (hPath : ∀ (T : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
      (hq : ∀ i : Fin m, Integrable (q i)
        (volume.restrict (Set.Ico 0 (T : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
      (hBound : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i),
        ∃ p : ℝ → pressureWeakNeumannDomain
            (LinearMap.range j.toLinearMap)
            (pressureA5CanonicalRangeEnergy j E hInj),
          (∀ τ : ℝ,
            (((p τ : LinearMap.range j.toLinearMap) : H)) =
              S (pressureA5HorizonClip T τ) (p₀ : H) +
                pressureA5ForwardDuhamel S
                  (pressureA5HorizonClip T τ) m f q) ∧
          Continuous (fun τ : ℝ =>
            pressureWeakNeumannOperator
              (LinearMap.range j.toLinearMap)
              (pressureA5CanonicalRangeEnergy j E hInj)
              (pressure_A5_canonical_range_separates j hInj hDense)
              (p τ))) :
    pressureA5CanonicalMovingNearPathProperty j E hInj hDense S := by
  have hWeakSym : ∀ x y : LinearMap.range j.toLinearMap,
      pressureA5CanonicalRangeEnergy j E hInj x y =
        pressureA5CanonicalRangeEnergy j E hInj y x :=
    pressure_A5_canonical_range_energy_symmetric j E hInj hESym
  intro T p₀ m f q hq M hM hBound
  obtain ⟨p, hpPhysical, hpGraph⟩ :=
    hPath T p₀ m f q hq M hM hBound
  refine ⟨p, hpPhysical, ?_⟩
  intro w wdot pdot τ hw hp
  exact paper_near_weak_neumann_moving_hasDerivAt
    (LinearMap.range j.toLinearMap)
    (pressureA5CanonicalRangeEnergy j E hInj)
    (pressure_A5_canonical_range_separates j hInj hDense)
    hWeakSym w p wdot pdot τ hw hp hpGraph.continuousAt

/-- The physical 3D Neumann construction satisfies the canonical moving
near-field derivative property.  Its only pointwise derivative premises
are the ambient derivatives of pressure and of the moving SR weight.
No independent semigroup/operator/path identification or Qdot is assumed. -/
theorem pressure_A5_physical_3d_moving_near_derivative
    (Ω : Opens pressureNeumannE3)
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
    let G := pressureNeumann3DWeakGradient μ embed negDiv
      (pressure_neumann_3d_canonical_vector_tests_dense Ω
        (volume : Measure pressureNeumannE3) hΩ)
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    let U := pressureNeumannGraphHilbertDomain D G
    let j := pressureNeumannGraphHilbertEmbedding D G
    let E := pressureNeumannGraphCoefficientEnergy D G C
    ∃ (hInj : Function.Injective j) (hDense : DenseRange j)
      (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)),
      pressureA5CanonicalMovingNearPathProperty j E hInj hDense S := by
  classical
  let μ := pressureNeumann3DRestrictedMeasure Ω
    (volume : Measure pressureNeumannE3)
  let embed := pressureNeumann3DRestrictedVectorL2Embed Ω
    (volume : Measure pressureNeumannE3) hΩ
  let negDiv := pressureNeumann3DRestrictedNegDivL2 Ω
    (volume : Measure pressureNeumannE3) hΩ
  let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
  letI : IsFiniteMeasure μ :=
    pressure_neumann_3d_restricted_measure_finite Ω
      (volume : Measure pressureNeumannE3) hΩ
  have hTests : DenseRange (embed : pressureNeumann3DSmoothVectorTests Ω →
      pressureNeumann3DVectorL2 (Ω : Set pressureNeumannE3) μ) :=
    pressure_neumann_3d_canonical_vector_tests_dense Ω
      (volume : Measure pressureNeumannE3) hΩ
  let G := pressureNeumann3DWeakGradient μ embed negDiv hTests
  let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  let U := pressureNeumannGraphHilbertDomain D G
  let j := pressureNeumannGraphHilbertEmbedding D G
  let E := pressureNeumannGraphCoefficientEnergy D G C
  obtain ⟨hInj, hDense, S, _hGraph, hPath⟩ :=
    pressure_A5_physical_3d_canonical_weak_path
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM
      hetam hetaM hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨hInj, hDense, S, ?_⟩
  have hCoeffSym : ∀ z w : pressureNeumann3DVectorL2
      (Ω : Set pressureNeumannE3) μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ :=
    (pressure_neumann_physical_A3_l2_coefficient_properties
      μ k eta beta km kM etam etaM hbeta hkm hkM
      hetam hetaM hEtaLo hEtaHi hKSym hKLo hKHi hTensor).1
  have hESym : ∀ x y : U, E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric
      (pressureNeumannGraphHilbertGradient D G) C hCoeffSym
  exact pressure_A5_canonical_moving_near_of_continuous_path
    j E hInj hDense S hESym hPath

end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_canonical_range_energy_symmetric
#print axioms ReservoirSeismicityControl.pressure_A5_canonical_moving_near_of_continuous_path
#print axioms ReservoirSeismicityControl.pressure_A5_physical_3d_moving_near_derivative
