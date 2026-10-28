import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDGeneratedOperator20261027
import Mathlib.Tactic

/-!
# Physical A3 positive Neumann generator in n_d = 1,2,3

This is the concrete physical A10 operator step. The existing canonical Green
semigroup theorem produces S and the weak generator characterization. The
physical A3 ellipticity and symmetry theorem then implies that A = -generator
is symmetric and nonnegative on S.generatorDomain. No independent operator
symmetry, positivity, or abstract weak-characterization premise is introduced.

The standard interior approximation and smooth Green identity are explicit
geometric inputs inherited from the passing canonical pressure theorem.
This theorem does not identify A10's separately chosen pressure path with
this canonical S, nor discharge the A7 local cutoff regularity input.
-/

namespace ReservoirSeismicityControl

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ENNReal Distributions BigOperators

variable {n_d : ℕ}

/-- The physical A3 Neumann semigroup's positive operator is symmetric and
nonnegative in each of the three manuscript spatial dimensions. -/
theorem pressure_nd_physical_volume_canonical_A3_positive_generator
    (hd : Paper2026.PaperSpatialDimension n_d)
    (Ω : Opens (Paper2026.PaperSpatial n_d))
    (hΩ : Bornology.IsBounded (Ω : Set (Paper2026.PaperSpatial n_d)))
    (hVectorApprox : ∀ (f : Paper2026.PaperSpatial n_d →
        EuclideanSpace ℝ (Fin n_d)),
      MemLp f 2 ((volume : Measure (Paper2026.PaperSpatial n_d)).restrict
        (Ω : Set (Paper2026.PaperSpatial n_d))) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ φ : pressureNDSmoothVectorTests Ω,
          eLpNorm (f - (φ : Paper2026.PaperSpatial n_d →
              EuclideanSpace ℝ (Fin n_d))) 2
            ((volume : Measure (Paper2026.PaperSpatial n_d)).restrict
              (Ω : Set (Paper2026.PaperSpatial n_d))) ≤ ENNReal.ofReal ε)
    (hScalarApprox : ∀ (f : Paper2026.PaperSpatial n_d → ℝ),
      MemLp f 2 ((volume : Measure (Paper2026.PaperSpatial n_d)).restrict
        (Ω : Set (Paper2026.PaperSpatial n_d))) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ ψ : pressureNDSmoothScalarTests Ω,
          eLpNorm (f - (ψ : Paper2026.PaperSpatial n_d → ℝ)) 2
            ((volume : Measure (Paper2026.PaperSpatial n_d)).restrict
              (Ω : Set (Paper2026.PaperSpatial n_d))) ≤ ENNReal.ofReal ε)
    (hGreen : ∀ (ψ : pressureNDSmoothScalarTests Ω)
        (φ : pressureNDSmoothVectorTests Ω),
      (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
        ⟪φ x.val, (pressureNDSmoothGradient Ω ψ) x.val⟫_ℝ
          ∂(pressureNDRestrictedMeasure Ω
            (volume : Measure (Paper2026.PaperSpatial n_d)))) =
      (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
        (pressureNDSmoothNegDiv Ω φ) x.val * ψ x.val
          ∂(pressureNDRestrictedMeasure Ω
            (volume : Measure (Paper2026.PaperSpatial n_d)))))
    (k : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) →
      Fin n_d → Fin n_d → ℝ)
    (eta : ↥(Ω : Set (Paper2026.PaperSpatial n_d)) → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (z i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j) ≤
        kM * (∑ i : Fin n_d, (z i) ^ 2))
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let μ := pressureNDRestrictedMeasure Ω
      (volume : Measure (Paper2026.PaperSpatial n_d))
    letI : IsFiniteMeasure μ :=
      pressure_nd_restricted_measure_finite Ω
        (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ
    let embed := pressureNDSmoothVectorL2Embed Ω μ
    let negDiv := pressureNDSmoothNegDivL2 Ω μ
    let hDense := pressure_nd_canonical_smooth_vector_tests_dense Ω
      (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ hVectorApprox
    let C := paperPressureL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
        (pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ),
      (∀ u f : pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ,
        (∃ x : pressureNeumannGraphHilbertDomain
            (pressureNDWeakH1Candidate μ embed negDiv)
            (pressureNDWeakGradient μ embed negDiv hDense),
          pressureNeumannGraphHilbertEmbedding _ _ x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain
              (pressureNDWeakH1Candidate μ embed negDiv)
              (pressureNDWeakGradient μ embed negDiv hDense),
            ⟪C (pressureNeumannGraphHilbertGradient _ _ x),
              pressureNeumannGraphHilbertGradient _ _ v⟫_ℝ =
              ⟪f, pressureNeumannGraphHilbertEmbedding _ _ v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f ) ∧
      (∀ a b : S.generatorDomain,
        ⟪-S.generator a, (b : pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ)⟫_ℝ =
          ⟪(a : pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ), -S.generator b⟫_ℝ) ∧
      (∀ a : S.generatorDomain,
        0 ≤ ⟪-S.generator a,
          (a : pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ)⟫_ℝ) := by
  classical
  let μ := pressureNDRestrictedMeasure Ω
    (volume : Measure (Paper2026.PaperSpatial n_d))
  letI : IsFiniteMeasure μ := pressure_nd_restricted_measure_finite Ω
    (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ
  let embed := pressureNDSmoothVectorL2Embed Ω μ
  let negDiv := pressureNDSmoothNegDivL2 Ω μ
  let hDense := pressure_nd_canonical_smooth_vector_tests_dense Ω
    (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ hVectorApprox
  let C := paperPressureL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  let D := pressureNDWeakH1Candidate μ embed negDiv
  let grad := pressureNDWeakGradient μ embed negDiv hDense
  let j := pressureNeumannGraphHilbertEmbedding D grad
  let g := pressureNeumannGraphHilbertGradient D grad
  obtain ⟨S, hWeak⟩ :=
    pressure_nd_physical_volume_canonical_A3_semigroup
      hd Ω hΩ hVectorApprox hScalarApprox hGreen
      k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  obtain ⟨hCSym, hCLower, _⟩ :=
    paper_pressure_A3_nd_l2_coefficient_properties
      μ k eta beta km kM etam etaM
      hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hCNonneg (z : pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) :
      0 ≤ ⟪C z, z⟫_ℝ := by
    have hc : 0 ≤ km / (beta * etaM) :=
      le_of_lt (div_pos hkm (mul_pos hbeta hetaM))
    exact le_trans (mul_nonneg hc (mul_self_nonneg (‖z‖))) (hCLower z)
  refine ⟨S, hWeak, ?_, ?_⟩
  · intro a b
    exact pressure_nd_positive_generator_symmetric_of_weak_characterization
      S j g C hCSym hWeak a b
  · intro a
    exact pressure_nd_positive_generator_nonnegative_of_weak_characterization
      S j g C hCNonneg hWeak a

end ReservoirSeismicityControl

#check ReservoirSeismicityControl.pressure_nd_physical_volume_canonical_A3_positive_generator
#print axioms ReservoirSeismicityControl.pressure_nd_physical_volume_canonical_A3_positive_generator
