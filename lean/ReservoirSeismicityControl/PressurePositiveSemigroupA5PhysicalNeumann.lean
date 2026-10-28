import ReservoirSeismicityControl.PressurePositiveSemigroupA5MeasurableElapsed
import ReservoirSeismicityControl.PressurePositiveSemigroupCanonicalBridge
import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSelfAdjointGraph
import ReservoirSeismicityControl.PressureNeumannGeneratorWeakIdentity
import ReservoirSeismicityControl.PressureNeumann3DPhysicalVolumeA3Semigroup

/-!
# Sharp measurable-rate A5 for symmetric weak Neumann diffusion

The two hypotheses `hSelf` and `hGraph` in the previously verified
elapsed-time theorem are now derived directly from a symmetric coercive
weak Neumann form and its Lax--Milgram resolvent. The second theorem
specializes the construction to the physical 3D tensor k/(beta*eta).

No derivative of a well rate, spectral eigenbasis, compact resolvent,
or independent self-adjoint-generator assumption is used.

Remaining distinction: the forcing is written in *elapsed* time. The
forward-time Duhamel change of variables is not claimed here. The rate
approximation currently takes a refining grid as an explicit input.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

section CanonicalForm

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Both self-adjointness conditions needed by the sharp A5 theorem
follow from the actual symmetric weak Neumann form. In particular the
second conclusion is the *maximal* generator graph identity. -/
theorem pressure_dense_neumann_semigroup_selfadjoint_and_graph
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j)
    (hjDense : DenseRange j) :
    let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense
    (∀ t : NNReal, IsSelfAdjoint (S t)) ∧
    (∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g) := by
  intro S
  let R : H →L[ℝ] H := pressureHilbertWeakResolvent j B₁ hB₁
  have hAdj : ContinuousLinearMap.adjoint R = R :=
    pressure_hilbert_resolvent_selfadjoint j B₁ hB₁ hSymB
  have hBridge (u f : H) :
      (∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f) ↔ R (u + f) = u := by
    change (∃ hu : u ∈ S.generatorDomain,
      S.generator ⟨u, hu⟩ = -f) ↔
      (u, f) ∈ pressureNeumannResolventGraph R
    exact (pressure_neumann_dense_generated_graph_iff
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense u f).symm
  have hUnit (z : H) :
      ∃ hz : R z ∈ S.generatorDomain,
        S.generator ⟨R z, hz⟩ = R z - z := by
    have hz : R (R z + (z - R z)) = R z := by
      have hsum : R z + (z - R z) = z := by abel
      rw [hsum]
    obtain ⟨hu, hLu⟩ := (hBridge (R z) (z - R z)).mpr hz
    exact ⟨hu, by simpa only [neg_sub] using hLu⟩
  have hDense : ∀ (lam : ℝ) (hlam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent
        lam j B₁ E hB₁ hForm₁ hE hlam) := by
    intro lam hlam
    exact pressure_neumann_canonical_denseRange
      lam j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense hlam
  have hSelf : ∀ t : NNReal, IsSelfAdjoint (S t) := by
    intro t
    change IsSelfAdjoint ((pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense) t)
    exact pressure_canonical_semigroup_isSelfAdjoint
      j B₁ E hB₁ hForm₁ hE hDense hSymB t
  refine ⟨hSelf, ?_⟩
  intro u g
  exact pressure_unit_resolvent_generator_selfadjoint_graph
    R S hAdj hBridge hUnit u g

/-- Full multiwell A5 for the semigroup constructed from a symmetric,
nonnegative, densely embedded weak Neumann form. No `hSelf` or `hGraph`
premise remains. The time partition and signed measurable well rates
are handled by the preceding verified A5 modules. -/
theorem pressure_dense_neumann_A5_measurable_elapsed
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j)
    (hjDense : DenseRange j) :
    let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense
    ∀ (t : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f : Fin m → H) (r : Fin m → ℝ → ℝ)
      (hr : ∀ q, Integrable (r q)
        (volume.restrict (Set.Ico 0 (t : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q)
      (hBound : ∀ q, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
        |r q s| ≤ M q)
      (N : ℕ → ℕ) (τ h : ℕ → ℕ → NNReal)
      (hMono : ∀ k, Monotone (τ k))
      (hStrict : ∀ k i, i < N k → τ k i < τ k (i + 1))
      (hStart : ∀ k, τ k 0 = 0)
      (hEnd : ∀ k, τ k (N k) = t)
      (hStep : ∀ k i, i < N k → τ k (i + 1) = τ k i + h k i)
      (mesh : ℕ → ℝ)
      (hLength : ∀ k i, i < N k →
        (τ k (i + 1) : ℝ) - (τ k i : ℝ) ≤ mesh k)
      (hMesh : Tendsto mesh atTop (𝓝 0)),
      ∃ hp : (S t (p₀ : H) +
          pressureMultiwellBochnerForcing S
            (volume.restrict (Set.Ico 0 (t : ℝ)))
            Real.toNNReal m f r) ∈ S.generatorDomain,
        ‖S.generator ⟨S t (p₀ : H) +
            pressureMultiwellBochnerForcing S
              (volume.restrict (Set.Ico 0 (t : ℝ)))
              Real.toNNReal m f r, hp⟩‖ ≤
          ‖S.generator p₀‖ + ∑ q : Fin m, M q * ‖f q‖ := by
  intro S t p₀ m f r hr M hM hBound N τ h hMono hStrict
    hStart hEnd hStep mesh hLength hMesh
  obtain ⟨hSelf, hGraph⟩ :=
    pressure_dense_neumann_semigroup_selfadjoint_and_graph
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense
  exact pressure_multiwell_A5_measurable_elapsed
    S hSelf hGraph t p₀ m f r hr M hM hBound
    N τ h hMono hStrict hStart hEnd hStep mesh hLength hMesh

end CanonicalForm

section PhysicalThreeD

open TopologicalSpace

set_option maxHeartbeats 2000000

/-- **Physical 3D sharp elapsed-time A5.** For the restricted Lebesgue
L²-space over a bounded open reservoir and the actual symmetric
permeability/viscosity tensor `k/(beta*eta)`, one can construct a C₀
contraction semigroup whose generator is the *negative weak Neumann
operator*, and the sharp A5 estimate holds for every finite family of
bounded, measurable, signed elapsed-time well rates. The admissibility
of a refining time grid is explicit. The physical-forward-time change
of variables is still a separate step. -/
theorem pressure_neumann_3d_physical_A5_measurable_elapsed
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
    let hTests := pressure_neumann_3d_canonical_vector_tests_dense Ω
      (volume : Measure pressureNeumannE3) hΩ
    let G := pressureNeumann3DWeakGradient μ embed negDiv hTests
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    let j := pressureNeumannGraphHilbertEmbedding D G
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
          (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ),
      (∀ u g : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          j x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
                ⟪g, j v⟫_ℝ) ↔
          ∃ hu : u ∈ S.generatorDomain,
            S.generator ⟨u, hu⟩ = -g) ∧
      (∀ (t : NNReal) (p₀ : S.generatorDomain)
        (m : ℕ)
        (f : Fin m → pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
        (r : Fin m → ℝ → ℝ)
        (hr : ∀ q, Integrable (r q)
          (volume.restrict (Set.Ico 0 (t : ℝ))))
        (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q)
        (hBound : ∀ q, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
          |r q s| ≤ M q)
        (N : ℕ → ℕ) (τ h : ℕ → ℕ → NNReal)
        (hMono : ∀ k, Monotone (τ k))
        (hStrict : ∀ k i, i < N k → τ k i < τ k (i + 1))
        (hStart : ∀ k, τ k 0 = 0)
        (hEnd : ∀ k, τ k (N k) = t)
        (hStep : ∀ k i, i < N k → τ k (i + 1) = τ k i + h k i)
        (mesh : ℕ → ℝ)
        (hLength : ∀ k i, i < N k →
          (τ k (i + 1) : ℝ) - (τ k i : ℝ) ≤ mesh k)
        (hMesh : Tendsto mesh atTop (𝓝 0)),
        ∃ hp : (S t (p₀ : pressureNeumann3DScalarL2
              (Ω : Set pressureNeumannE3) μ) +
            pressureMultiwellBochnerForcing S
              (volume.restrict (Set.Ico 0 (t : ℝ)))
              Real.toNNReal m f r) ∈ S.generatorDomain,
          ‖S.generator ⟨S t (p₀ : pressureNeumann3DScalarL2
                (Ω : Set pressureNeumannE3) μ) +
              pressureMultiwellBochnerForcing S
                (volume.restrict (Set.Ico 0 (t : ℝ)))
                Real.toNNReal m f r, hp⟩‖ ≤
            ‖S.generator p₀‖ + ∑ q : Fin m, M q * ‖f q‖) := by
  intro μ embed negDiv D hTests G C j
  letI : IsFiniteMeasure μ :=
    pressure_neumann_3d_restricted_measure_finite Ω
      (volume : Measure pressureNeumannE3) hΩ
  let E := pressureNeumannGraphCoefficientEnergy D G C
  let B := pressureNeumannGraphCoefficientUnitForm D G C
  have hA3 := pressure_neumann_physical_A3_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : pressureNeumann3DVectorL2
      (Ω : Set pressureNeumannE3) μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ := hA3.2.1
  have hSymC : ∀ z w : pressureNeumann3DVectorL2
      (Ω : Set pressureNeumannE3) μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hB : IsCoercive B :=
    pressure_neumann_graph_coefficient_unit_form_coercive
      D G C (km / (beta * etaM)) hc hEll
  have hForm : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B x y = ⟪j x, j y⟫_ℝ + E x y :=
    pressure_neumann_graph_coefficient_unit_form_apply D G C
  have hE : ∀ x : pressureNeumannGraphHilbertDomain D G,
      0 ≤ E x x :=
    pressure_neumann_bounded_coefficient_form_nonneg
      (pressureNeumannGraphHilbertGradient D G)
      C (km / (beta * etaM)) hc hEll
  have hSymE : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric
      (pressureNeumannGraphHilbertGradient D G) C hSymC
  have hSymB : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B x y = B y x := by
    intro x y
    calc
      B x y = ⟪j x, j y⟫_ℝ + E x y := hForm x y
      _ = ⟪j y, j x⟫_ℝ + E y x := by
        rw [real_inner_comm (j x) (j y), hSymE x y]
      _ = B y x := (hForm y x).symm
  have hjInj : Function.Injective j :=
    pressure_neumann_3d_weak_graph_embedding_injective
      μ embed negDiv hTests
  have hScalarDense : DenseRange
      ((D.subtype : D → pressureNeumann3DScalarL2
        (Ω : Set pressureNeumannE3) μ)) :=
    pressure_neumann_3d_restricted_weak_H1_dense_of_smooth_ibp
      Ω (volume : Measure pressureNeumannE3) hΩ
      (pressure_neumann_3d_physical_smooth_ibp_l2 Ω hΩ)
  have hjDense : DenseRange j :=
    pressure_neumann_3d_weak_graph_embedding_dense
      μ embed negDiv hTests hScalarDense
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B E hB hForm hE hSymB hjInj hjDense
  refine ⟨S, ?_, ?_⟩
  · intro u g
    simpa only [S, E, pressureNeumannGraphCoefficientEnergy,
      pressure_neumann_bounded_coefficient_form_apply] using
      (pressure_neumann_dense_generator_weak_iff
        j B E hB hForm hE hSymB hjInj hjDense u g)
  · intro t p₀ m f r hr M hM hBound N τ h hMono hStrict
      hStart hEnd hStep mesh hLength hMesh
    exact pressure_dense_neumann_A5_measurable_elapsed
      j B E hB hForm hE hSymB hjInj hjDense
      t p₀ m f r hr M hM hBound N τ h hMono hStrict
      hStart hEnd hStep mesh hLength hMesh

end PhysicalThreeD

end ReservoirSeismicityControl
