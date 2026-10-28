import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeA3Semigroup
import ReservoirSeismicityControl.PressureNeumannGeneratorWeakIdentity

/-!
# Physical three-dimensional Neumann unit resolvent and generator

This theorem identifies the **actual unit weak resolvent** from the
three-dimensional physical coefficient `k/(beta*eta)` with the generator
of the physical Neumann contraction semigroup. It does not require a
compact embedding, discrete spectrum, or a bound on derivatives of Q.

Let A be the nonnegative weak Neumann diffusion operator. The equation
`R (u+f)=u` means `Au=f`, and the associated semigroup generator is `-A`.
Thus the unit resolvent is exactly `(I+A)^{-1}` in graph form.

This still does NOT construct a spectral measure or prove the forced
Duhamel representation; those remain separate steps for the physical A5.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix

variable (Ω : Opens pressureNeumannE3)

set_option maxHeartbeats 2000000

/-- Under the paper's physical ellipticity assumptions, the weak Neumann
unit resolvent and the contraction semigroup generator have exactly the same
operator graph. No Rellich compactness or additional forcing regularity is
assumed. -/
theorem pressure_neumann_3d_physical_unit_resolvent_generator
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
      ContinuousLinearMap.adjoint (pressureHilbertWeakResolvent j B hB) =
        pressureHilbertWeakResolvent j B hB ∧
      (∀ h : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        0 ≤ ⟪pressureHilbertWeakResolvent j B hB h, h⟫_ℝ) ∧
      (∀ u f : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f) ↔
        pressureHilbertWeakResolvent j B hB (u + f) = u) ∧
      (∀ h : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        ∃ hRh : pressureHilbertWeakResolvent j B hB h ∈ S.generatorDomain,
          S.generator ⟨pressureHilbertWeakResolvent j B hB h, hRh⟩ =
            pressureHilbertWeakResolvent j B hB h - h) := by
  intro μ embed negDiv D hTests G C j E B
  letI : IsFiniteMeasure μ :=
    pressure_neumann_3d_restricted_measure_finite Ω
      (volume : Measure pressureNeumannE3) hΩ
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hA3 := pressure_neumann_physical_A3_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNeumann3DVectorL2
        (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω (volume : Measure pressureNeumannE3)),
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hB : IsCoercive B :=
    pressure_neumann_graph_coefficient_unit_form_coercive
      D G C (km / (beta * etaM)) hc hEll
  obtain ⟨S, hS⟩ := pressure_neumann_3d_physical_volume_A3_semigroup
    Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hSymC : ∀ z w : pressureNeumann3DVectorL2
        (Ω : Set pressureNeumannE3)
        (pressureNeumann3DRestrictedMeasure Ω (volume : Measure pressureNeumannE3)),
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  have hSymE : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric
      (pressureNeumannGraphHilbertGradient D G) C hSymC
  have hForm : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B x y = ⟪j x, j y⟫_ℝ + E x y := by
    intro x y
    exact pressure_neumann_graph_coefficient_unit_form_apply D G C x y
  have hSymB : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B x y = B y x := by
    intro x y
    calc
      B x y = ⟪j x, j y⟫_ℝ + E x y := hForm x y
      _ = ⟪j y, j x⟫_ℝ + E y x := by
        rw [real_inner_comm (j x) (j y), hSymE x y]
      _ = B y x := (hForm y x).symm
  have hSelfAdjoint :
      ContinuousLinearMap.adjoint (pressureHilbertWeakResolvent j B hB) =
        pressureHilbertWeakResolvent j B hB :=
    pressure_hilbert_resolvent_selfadjoint j B hB hSymB
  have hNonneg : ∀ h : pressureNeumann3DScalarL2
      (Ω : Set pressureNeumannE3) μ,
      0 ≤ ⟪pressureHilbertWeakResolvent j B hB h, h⟫_ℝ := by
    intro h
    exact pressure_hilbert_resolvent_nonneg j B hB h
  have hBridge : ∀ u f : pressureNeumann3DScalarL2
      (Ω : Set pressureNeumannE3) μ,
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔
      pressureHilbertWeakResolvent j B hB (u + f) = u := by
    intro u f
    have hWeak :
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          j x = u ∧ ∀ v : pressureNeumannGraphHilbertDomain D G,
            E x v = ⟪f, j v⟫_ℝ) ↔
        (∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f) := by
      simpa only [E, pressureNeumannGraphCoefficientEnergy,
        pressure_neumann_bounded_coefficient_form_apply] using hS u f
    have hResolvent := pressure_neumann_weak_energy_graph_iff
      j B E hB hForm u f
    exact hWeak.symm.trans hResolvent
  refine ⟨hB, S, hSelfAdjoint, hNonneg, hBridge, ?_⟩
  intro h
  have hh : pressureHilbertWeakResolvent j B hB
      (pressureHilbertWeakResolvent j B hB h +
        (h - pressureHilbertWeakResolvent j B hB h)) =
      pressureHilbertWeakResolvent j B hB h := by
    have hsum : pressureHilbertWeakResolvent j B hB h +
        (h - pressureHilbertWeakResolvent j B hB h) = h := by
      abel
    rw [hsum]
  obtain ⟨hRh, hGen⟩ := (hBridge
    (pressureHilbertWeakResolvent j B hB h)
    (h - pressureHilbertWeakResolvent j B hB h)).mpr hh
  exact ⟨hRh, by simpa only [neg_sub] using hGen⟩

end ReservoirSeismicityControl
