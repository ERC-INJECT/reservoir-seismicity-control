import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDCanonicalSmooth20261027
import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDMaximalSemigroup20261027
import Mathlib.Tactic

/-!
# Actual physical-volume Neumann realization, uniformly in n_d ∈ {1,2,3}

This module removes the *abstract* vector-test embedding, scalar-test embedding,
weak gradient, and L² integration-by-parts witness from the generic maximal
Neumann semigroup interface.  Both L² test embeddings and the negative
divergence are the canonical maps of the already verified dimension-generic
smooth-test module.  The vector gradient of a scalar smooth test is built
from its actual coordinate directional derivatives.

The only geometrical inputs are the usual interior smooth L² approximation
and the compactly-supported smooth Green formula, made explicit below as
standard analytic hypotheses.  This file does NOT claim that those analytic
results have been proved from arbitrary-domain geometry, or that A7/A10
physical regularity has already been discharged.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions BigOperators InnerProductSpace ENNReal

variable {n_d : ℕ}

/-- The actual n_d-dimensional smooth gradient as a compactly supported
vector test: a sum of directional derivatives in the coordinate basis. -/
noncomputable def pressureNDSmoothGradient
    (Ω : Opens (Paper2026.PaperSpatial n_d)) :
    pressureNDSmoothScalarTests Ω →L[ℝ] pressureNDSmoothVectorTests Ω :=
  ∑ i : Fin n_d,
    (TestFunction.postcompCLM
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (EuclideanSpace.single i (1 : ℝ))) :
      pressureNDSmoothScalarTests Ω →L[ℝ] pressureNDSmoothVectorTests Ω) ∘L
    (TestFunction.lineDerivCLM ℝ (Paper2026.paperCoordinateDirection i) :
      pressureNDSmoothScalarTests Ω →L[ℝ] pressureNDSmoothScalarTests Ω)

/-- Physical n_d-dimensional Neumann semigroup from the actual smooth tests.
The Green formula is a standard analytic fact for C_c^∞ vector/scalar fields,
not a postulated abstract gradient operator or arbitrary L² IBP witness.
Both smooth approximation hypotheses are explicitly tied to the physical
volume measure, not to an unspecified finite measure. -/
theorem pressure_nd_physical_volume_canonical_A3_semigroup
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
      ∀ u f : pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ,
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
        ∃ hu : u ∈ S.generatorDomain, S.generator ⟨u, hu⟩ = -f := by
  let μ := pressureNDRestrictedMeasure Ω
    (volume : Measure (Paper2026.PaperSpatial n_d))
  letI : IsFiniteMeasure μ := pressure_nd_restricted_measure_finite Ω
    (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ
  let embed := pressureNDSmoothVectorL2Embed Ω μ
  let negDiv := pressureNDSmoothNegDivL2 Ω μ
  have hVectorDense : DenseRange
      (embed : pressureNDSmoothVectorTests Ω →
        pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) :=
    pressure_nd_canonical_smooth_vector_tests_dense Ω
      (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ hVectorApprox
  have hScalarDense : DenseRange
      (pressureNDSmoothToL2CLM Ω μ ℝ :
        pressureNDSmoothScalarTests Ω → pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) :=
    pressure_nd_canonical_smooth_scalar_tests_dense Ω
      (volume : Measure (Paper2026.PaperSpatial n_d)) hΩ hScalarApprox
  have hIBP : ∀ ψ : pressureNDSmoothScalarTests Ω,
      ∃ g : pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ,
        ∀ φ : pressureNDSmoothVectorTests Ω,
          ⟪embed φ, g⟫_ℝ =
            ⟪negDiv φ, pressureNDSmoothToL2CLM Ω μ ℝ ψ⟫_ℝ := by
    intro ψ
    refine ⟨pressureNDSmoothVectorL2Embed Ω μ
      (pressureNDSmoothGradient Ω ψ), ?_⟩
    intro φ
    change ⟪pressureNDSmoothVectorL2Embed Ω μ φ,
        pressureNDSmoothVectorL2Embed Ω μ (pressureNDSmoothGradient Ω ψ)⟫_ℝ =
      ⟪pressureNDSmoothNegDivL2 Ω μ φ,
        pressureNDSmoothToL2CLM Ω μ ℝ ψ⟫_ℝ
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    have hφ := pressure_nd_smooth_vector_embed_ae Ω μ φ
    have hGrad := pressure_nd_smooth_vector_embed_ae Ω μ
      (pressureNDSmoothGradient Ω ψ)
    have hDiv := pressure_nd_smooth_negDiv_embed_ae Ω μ φ
    have hψ := pressure_nd_smooth_toL2_ae Ω μ ℝ ψ
    calc
      (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
        ⟪(pressureNDSmoothVectorL2Embed Ω μ φ :
            pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) x,
          (pressureNDSmoothVectorL2Embed Ω μ (pressureNDSmoothGradient Ω ψ) :
            pressureNDVectorL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) x⟫_ℝ ∂μ) =
        (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
          ⟪φ x.val, (pressureNDSmoothGradient Ω ψ) x.val⟫_ℝ ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hφ, hGrad] with x hx hy
        rw [hx, hy]
      _ = (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
          (pressureNDSmoothNegDiv Ω φ) x.val * ψ x.val ∂μ) :=
            hGreen ψ φ
      _ = (∫ x : ↥(Ω : Set (Paper2026.PaperSpatial n_d)),
          ⟪(pressureNDSmoothNegDivL2 Ω μ φ :
              pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) x,
            (pressureNDSmoothToL2CLM Ω μ ℝ ψ :
              pressureNDScalarL2 (Ω : Set (Paper2026.PaperSpatial n_d)) μ) x⟫_ℝ ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hDiv, hψ] with x hx hy
        rw [hx, hy]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
  exact pressure_nd_maximal_weak_A3_semigroup_exists
    μ hd embed negDiv hVectorDense
    (pressureNDSmoothToL2CLM Ω μ ℝ)
    hScalarDense hIBP
    k eta beta km kM etam etaM
    hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor

end ReservoirSeismicityControl

#check ReservoirSeismicityControl.pressure_nd_physical_volume_canonical_A3_semigroup
#print axioms ReservoirSeismicityControl.pressure_nd_physical_volume_canonical_A3_semigroup
