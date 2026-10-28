import ReservoirSeismicityControl.PaperA5CanonicalPhysicalWeakPath
import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeA3Semigroup
import ReservoirSeismicityControl.PaperNearWeakNeumannMovingDerivative
import Mathlib.Tactic

/-!
# Stage 78 — canonical A5 pressure trajectory for the actual 3D reservoir

The pressure Hilbert space is the physical L² of a bounded open subset
of Euclidean 3-space, with Lebesgue volume. The energy domain is the
completed maximal distributional-gradient graph, and the diffusion
coefficient is the actual anisotropic multiplier k/(beta*eta).

The previously proved smooth physical integration by parts, test densities,
closed-gradient uniqueness, tensor coercivity and symmetry construct the
canonical form semigroup. This particular semigroup is shown to have the
exact weak 3D physical Neumann graph, not merely to be an arbitrary abstract
semigroup of unspecified relation to the PDE.

Stage 77 then constructs the physical multiwell mild pressure path as a
canonical weak-domain-valued path, with strongly continuous weak Neumann
operator image, without assuming time derivatives of well rates.

The differentiability and operator-domain properties of moving seismicity
observation weights remain open, as do the far-field and SR estimates.
No equivalence with a separately defined Mathlib Sobolev H¹ space is claimed.
-/

namespace ReservoirSeismicityControl

-- Stage 78 physical 3D realization requires extra elaboration budget.
set_option maxHeartbeats 2000000

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace BigOperators Matrix NNReal

/-- Specialize Stage 77 to the canonical *physical three-dimensional* weak
Neumann operator with bounded measurable anisotropic permeability and
positive bounded viscosity.

The existential proof objects `hInj` and `hDense` are constructed from the
physical smooth-test integration by parts and density lemmas. They are not
independent hypotheses. The semigroup `S` is exactly the form-generated
semigroup, not a separately chosen semigroup whose identification would
require a uniqueness theorem.

For every physical finite-well mild solution (with bounded locally
integrable rates) this provides a weak-domain pressure path and a continuous
weak Neumann image. This result does not assert time differentiability or
SR-weight regularity. -/
theorem pressure_A5_physical_3d_canonical_weak_path
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
      (∀ u f : pressureNeumann3DScalarL2
          (Ω : Set pressureNeumannE3) μ,
        (∃ x : U, j x = u ∧
          ∀ v : U,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
              ⟪f, j v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f) ∧
      (∀ (T : NNReal) (p₀ : S.generatorDomain)
          (m : ℕ) (f : Fin m → pressureNeumann3DScalarL2
            (Ω : Set pressureNeumannE3) μ)
          (q : Fin m → ℝ → ℝ)
          (hq : ∀ i : Fin m, Integrable (q i)
            (volume.restrict (Set.Ico 0 (T : ℝ))))
          (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
          (hBound : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
            ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i),
        ∃ p : ℝ → pressureWeakNeumannDomain
            (LinearMap.range j.toLinearMap)
            (pressureA5CanonicalRangeEnergy j E hInj),
          (∀ τ : ℝ,
            (((p τ : LinearMap.range j.toLinearMap) :
                pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)) =
              S (pressureA5HorizonClip T τ) (p₀ :
                pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ) +
              pressureA5ForwardDuhamel S
                (pressureA5HorizonClip T τ) m f q) ∧
          Continuous (fun τ : ℝ =>
            pressureWeakNeumannOperator
              (LinearMap.range j.toLinearMap)
              (pressureA5CanonicalRangeEnergy j E hInj)
              (pressure_A5_canonical_range_separates j hInj hDense)
              (p τ))) := by
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
  let g := pressureNeumannGraphHilbertGradient D G
  let E := pressureNeumannGraphCoefficientEnergy D G C
  let B₁ := pressureNeumannGraphCoefficientUnitForm D G C
  have hScalarDense : DenseRange
      (D.subtype : D → pressureNeumann3DScalarL2
        (Ω : Set pressureNeumannE3) μ) :=
    pressure_neumann_3d_restricted_weak_H1_dense_of_smooth_ibp
      Ω (volume : Measure pressureNeumannE3) hΩ
      (pressure_neumann_3d_physical_smooth_ibp_l2 Ω hΩ)
  have hInj : Function.Injective j :=
    pressure_neumann_3d_weak_graph_embedding_injective
      μ embed negDiv hTests
  have hDense : DenseRange j :=
    pressure_neumann_3d_weak_graph_embedding_dense
      μ embed negDiv hTests hScalarDense
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hA3 := pressure_neumann_physical_A3_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNeumann3DVectorL2
      (Ω : Set pressureNeumannE3) μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hSym : ∀ z w : pressureNeumann3DVectorL2
      (Ω : Set pressureNeumannE3) μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  have hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + E x y := by
    intro x y
    exact pressure_neumann_graph_coefficient_unit_form_apply D G C x y
  have hE : ∀ x : U, 0 ≤ E x x := by
    intro x
    exact pressure_neumann_bounded_coefficient_form_nonneg
      g C (km / (beta * etaM)) hc hEll x
  have hSymE : ∀ x y : U, E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric g C hSym
  have hSymB : ∀ x y : U, B₁ x y = B₁ y x := by
    intro x y
    calc
      B₁ x y = ⟪j x, j y⟫_ℝ + E x y := hForm₁ x y
      _ = ⟪j y, j x⟫_ℝ + E y x := by
        exact congrArg₂ (fun a b : ℝ => a + b)
          (real_inner_comm (j x) (j y)).symm (hSymE x y)
      _ = B₁ y x := (hForm₁ y x).symm
  have hB₁ : IsCoercive B₁ :=
    pressure_neumann_graph_coefficient_unit_form_coercive
      D G C (km / (beta * etaM)) hc hEll
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ E hB₁ hForm₁ hE hSymB hInj hDense
  refine ⟨hInj, hDense, S, ?_, ?_⟩
  · intro u f
    change (∃ x : U, j x = u ∧
      ∀ v : U, E x v = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f
    exact pressure_neumann_dense_generator_weak_iff
      j B₁ E hB₁ hForm₁ hE hSymB hInj hDense u f
  · intro T p₀ m f q hq M hM hBound
    exact pressure_A5_canonical_physical_weak_path_exists
      j B₁ E hB₁ hForm₁ hE hSymB hInj hDense
      T p₀ m f q hq M hM hBound

end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_physical_3d_canonical_weak_path
