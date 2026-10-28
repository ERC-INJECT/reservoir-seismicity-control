import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorNonpositive
import ReservoirSeismicityControl.PressureNeumannMaximalAccretive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Real.Spectrum

/-!
# Physical Neumann unit resolvent is a positive contraction

The bounded unit resolvent R = (I + A)^{-1} of the actual physical
Neumann diffusion has the following order properties:

  0 <= R <= I and ||R|| <= 1.

Both `R` and `I - R` are positive in Mathlib's native sense.
Mathlib's spectral positivity certificate therefore applies to R.
This is a compactness-free step towards an operator-functional-calculus
proof of Appendix A.1, equation (A5), but it is NOT yet the spectral
representation or the forced Duhamel formula needed for (A5).
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

section AbstractResolvent

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Symmetry, nonnegative quadratic form and a contraction bound make
both the unit resolvent and its complement positive operators. -/
theorem pressure_resolvent_positive_order_of_contract
    (R : H →L[ℝ] H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hNonneg : ∀ x : H, 0 ≤ ⟪R x, x⟫_ℝ)
    (hContract : ∀ x : H, ‖R x‖ ≤ ‖x‖) :
    R.IsPositive ∧ ((1 : H →L[ℝ] H) - R).IsPositive ∧ ‖R‖ ≤ 1 := by
  have hSym : R.IsSymmetric := by
    intro x y
    calc
      ⟪R x, y⟫_ℝ = ⟪x, (ContinuousLinearMap.adjoint R) y⟫_ℝ :=
        (ContinuousLinearMap.adjoint_inner_right R x y).symm
      _ = ⟪x, R y⟫_ℝ := by rw [hAdj]
  have hPositive : R.IsPositive :=
    (ContinuousLinearMap.isPositive_iff R).2 ⟨hSym, hNonneg⟩
  have hSymComplement : ((1 : H →L[ℝ] H) - R).IsSymmetric := by
    intro x y
    change ⟪x - R x, y⟫_ℝ = ⟪x, y - R y⟫_ℝ
    have hxy : ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ := by
      calc
        ⟪R x, y⟫_ℝ = ⟪x, (ContinuousLinearMap.adjoint R) y⟫_ℝ :=
          (ContinuousLinearMap.adjoint_inner_right R x y).symm
        _ = ⟪x, R y⟫_ℝ := by rw [hAdj]
    rw [inner_sub_left, inner_sub_right, hxy]
  have hPositiveComplement : ((1 : H →L[ℝ] H) - R).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).2
    refine ⟨hSymComplement, ?_⟩
    intro x
    have hCauchy : ⟪R x, x⟫_ℝ ≤ ‖R x‖ * ‖x‖ :=
      real_inner_le_norm _ _
    have hBound : ⟪R x, x⟫_ℝ ≤ ‖x‖ * ‖x‖ :=
      hCauchy.trans
        (mul_le_mul_of_nonneg_right (hContract x) (norm_nonneg x))
    change 0 ≤ ⟪x - R x, x⟫_ℝ
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    nlinarith
  have hOpNorm : ‖R‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound R (by norm_num)
    intro x
    simpa only [one_mul] using hContract x
  exact ⟨hPositive, hPositiveComplement, hOpNorm⟩

/-- Spectral nonnegativity for any positive contractive unit resolvent.
This is a property of the bounded operator, not a full spectral measure. -/
theorem pressure_resolvent_spectrum_nonnegative_of_contract
    (R : H →L[ℝ] H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hNonneg : ∀ x : H, 0 ≤ ⟪R x, x⟫_ℝ)
    (hContract : ∀ x : H, ‖R x‖ ≤ ‖x‖) :
    SpectrumRestricts R ContinuousMap.realToNNReal := by
  exact (pressure_resolvent_positive_order_of_contract
    R hAdj hNonneg hContract).1.spectrumRestricts

/-- The full real spectrum of a positive contractive resolvent lies in
`[0,1]`. This supplies the compact spectral-parameter interval used by
continuous functional calculus, but not an operator spectral measure. -/
theorem pressure_resolvent_spectrum_unit_interval
    (R : H →L[ℝ] H)
    (hAdj : ContinuousLinearMap.adjoint R = R)
    (hNonneg : ∀ x : H, 0 ≤ ⟪R x, x⟫_ℝ)
    (hContract : ∀ x : H, ‖R x‖ ≤ ‖x‖) :
    ∀ ρ ∈ spectrum ℝ R, ρ ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hPos, _, hOpNorm⟩ :=
    pressure_resolvent_positive_order_of_contract R hAdj hNonneg hContract
  intro ρ hρ
  have hρ0 : 0 ≤ ρ :=
    (SpectrumRestricts.nnreal_iff.mp hPos.spectrumRestricts) ρ hρ
  have hρAbs : |ρ| ≤ ‖R‖ := by
    have hOne : ‖(1 : H →L[ℝ] H)‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℝ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    calc
      |ρ| ≤ ‖R‖ * ‖(1 : H →L[ℝ] H)‖ := by
        simpa only [Real.norm_eq_abs] using
          (spectrum.norm_le_norm_mul_of_mem hρ)
      _ ≤ ‖R‖ * 1 :=
        mul_le_mul_of_nonneg_left hOne (norm_nonneg R)
      _ = ‖R‖ := mul_one _
  exact ⟨hρ0, (le_abs_self ρ).trans (hρAbs.trans hOpNorm)⟩

end AbstractResolvent

section PhysicalVolume

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- Actual physical coefficient `k/(beta*eta)`, physical volume measure,
and the constructed Neumann weak resolvent. This result needs neither
compact embedding nor any source derivative assumption. -/
theorem pressure_neumann_3d_physical_unit_resolvent_order
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
      R.IsPositive ∧
      ((1 : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ →L[ℝ]
          pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) - R).IsPositive ∧
      ‖R‖ ≤ 1 ∧
      SpectrumRestricts R ContinuousMap.realToNNReal ∧
      (∀ ρ ∈ spectrum ℝ R, ρ ∈ Set.Icc (0 : ℝ) 1) := by
  intro μ embed negDiv D hTests G C j E B
  obtain ⟨hB, S, hAdj, hNonneg, _hBridge, _hUnit⟩ :=
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
  have hPos := pressure_resolvent_positive_order_of_contract
    (pressureHilbertWeakResolvent j B hB) hAdj hNonneg hContract
  refine ⟨hB, S, ?_⟩
  dsimp only
  exact ⟨hPos.1, hPos.2.1, hPos.2.2,
    hPos.1.spectrumRestricts,
    pressure_resolvent_spectrum_unit_interval
      (pressureHilbertWeakResolvent j B hB) hAdj hNonneg hContract⟩

end PhysicalVolume

end ReservoirSeismicityControl
