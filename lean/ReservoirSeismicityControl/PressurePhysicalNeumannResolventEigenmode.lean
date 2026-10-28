import ReservoirSeismicityControl.PressurePhysicalNeumannResolventOrder

/-!
# Eigenmode correspondence for the physical unit Neumann resolvent

Let `R = (I+A)⁻¹` be the positive, contractive unit resolvent of the
physical Neumann diffusion and let `L = -A` be its semigroup generator.

A nonzero eigenvector `v` of `R` has an eigenvalue `rho` in `(0,1]`.
The SAME vector belongs to the generator domain and satisfies

  L v = (1 - rho⁻¹) v,     A v = (rho⁻¹ - 1) v.

This uses only positivity, contraction and the already formalized
resolvent-to-generator identity. It does NOT assume compactness or assert
that eigenvectors span L²: continuous spectrum may remain present.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractEigenmode

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Eigenvectors of a positive contractive unit resolvent are
nonzero-eigenvalue generator eigenvectors. No eigenbasis is assumed. -/
theorem pressure_unit_resolvent_eigenmode_generator
    (R : H →L[ℝ] H)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hNonneg : ∀ x : H, 0 ≤ ⟪R x, x⟫_ℝ)
    (hContract : ∀ x : H, ‖R x‖ ≤ ‖x‖)
    (hUnit : ∀ h : H,
      ∃ hh : R h ∈ S.generatorDomain,
        S.generator ⟨R h, hh⟩ = R h - h)
    (v : H) (hv : v ≠ 0) (rho : ℝ)
    (hEigen : R v = rho • v) :
    0 < rho ∧ rho ≤ 1 ∧
      ∃ hvDomain : v ∈ S.generatorDomain,
        S.generator ⟨v, hvDomain⟩ = (1 - rho⁻¹) • v := by
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hRhoZero : rho ≠ 0 := by
    intro hz
    have hzR : R v = 0 := by simpa [hz] using hEigen
    obtain ⟨hRDomain, hG⟩ := hUnit v
    have heq : (⟨R v, hRDomain⟩ : S.generatorDomain) = 0 :=
      Subtype.ext hzR
    have hGzero : S.generator ⟨R v, hRDomain⟩ = 0 := by
      rw [heq]
      exact map_zero S.generator
    rw [hGzero, hzR, zero_sub] at hG
    exact hv (neg_eq_zero.mp hG.symm)
  have hRhoProd : 0 ≤ rho * ‖v‖ ^ 2 := by
    calc
      0 ≤ ⟪R v, v⟫_ℝ := hNonneg v
      _ = rho * ‖v‖ ^ 2 := by
        rw [hEigen, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hRhoNonneg : 0 ≤ rho := by
    by_contra h
    have hNeg : rho < 0 := lt_of_not_ge h
    have hProdNeg : rho * ‖v‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hNeg (sq_pos_of_pos hvnorm)
    exact (not_lt_of_ge hRhoProd) hProdNeg
  have hRhoPos : 0 < rho := lt_of_le_of_ne hRhoNonneg (Ne.symm hRhoZero)
  have hRhoNorm : |rho| * ‖v‖ ≤ ‖v‖ := by
    calc
      |rho| * ‖v‖ = ‖R v‖ := by
        rw [hEigen, norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ := hContract v
  have hRhoLeOne : rho ≤ 1 := by
    have habs : |rho| ≤ 1 := by
      apply le_of_mul_le_mul_right ?_ hvnorm
      simpa only [one_mul] using hRhoNorm
    exact (le_abs_self rho).trans habs
  have hScaled : R (rho⁻¹ • v) = v := by
    rw [map_smul, hEigen, smul_smul, inv_mul_cancel₀ hRhoZero, one_smul]
  obtain ⟨hScaledDomain, hGenerator⟩ := hUnit (rho⁻¹ • v)
  have hvDomain : v ∈ S.generatorDomain := by
    rw [← hScaled]
    exact hScaledDomain
  refine ⟨hRhoPos, hRhoLeOne, hvDomain, ?_⟩
  calc
    S.generator ⟨v, hvDomain⟩ =
        S.generator ⟨R (rho⁻¹ • v), hScaledDomain⟩ :=
      congrArg S.generator (Subtype.ext hScaled.symm)
    _ = R (rho⁻¹ • v) - rho⁻¹ • v := hGenerator
    _ = (1 - rho⁻¹) • v := by rw [hScaled, sub_smul, one_smul]

end AbstractEigenmode

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- Eigenmode correspondence for the actual 3D physical Neumann operator.
This theorem only concerns eigenvectors that exist; spectral completeness
and the forced Duhamel formula are separate outstanding obligations. -/
theorem pressure_neumann_3d_physical_resolvent_eigenmode
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
      ∀ (v : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
        (rho : ℝ), v ≠ 0 → R v = rho • v →
        0 < rho ∧ rho ≤ 1 ∧
          ∃ hv : v ∈ S.generatorDomain,
            S.generator ⟨v, hv⟩ = (1 - rho⁻¹) • v := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, _hAdj, hNonneg, _hBridge, hUnit⟩ :=
    pressure_neumann_3d_physical_unit_resolvent_generator
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
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
  have hContract : ∀ h : pressureNeumann3DScalarL2
      (Ω : Set pressureNeumannE3) μ,
      ‖pressureHilbertWeakResolvent j B hB h‖ ≤ ‖h‖ :=
    pressure_hilbert_neumann_resolvent_contract j B E hB hForm hE
  refine ⟨hB, S, ?_⟩
  dsimp only
  intro v rho hv hEigen
  exact pressure_unit_resolvent_eigenmode_generator
    (pressureHilbertWeakResolvent j B hB) S hNonneg hContract hUnit
    v hv rho hEigen

end PhysicalVolume

end ReservoirSeismicityControl
