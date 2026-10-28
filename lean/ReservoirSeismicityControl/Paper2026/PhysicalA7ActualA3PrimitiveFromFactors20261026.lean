import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3WeakProductClosure20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalTimeIntegratedCoefficient
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl Appendix A.2 — causal weak-H² primitive of the physical A3 product

This *constructs* the time-dependent weak-H² graph of gamma2(·,q)*Rstar
from its individual Sobolev factor approximations, via the preceding passed
A3 strong-product and weak-closure modules, then integrates those graphs.

Unlike the older coefficient-primitive theorem, no arbitrary time-indexed
weak-H² coefficient graph is assumed here. Unlike that theorem, time
integrability of all 13 spatial fields is DERIVED from strong measurability,
finite causal measure, and uniform component bounds.

External bounded-Lipschitz Sobolev results supply smooth factor approximants,
the corresponding ordinary smooth integration by parts, and factor convergence.
The spatial Lp representatives and their embeddings must describe the same
physical fields. Time measurability/uniform estimates and Bochner-to-pointwise
representative identification remain separate physical applicability facts.
Nothing in this file asserts an unproved spatial H² regularity of the signed
reciprocal Y or rate R, and no diffusion proof is duplicated.
-/

namespace ReservoirSeismicityControl.Paper2026

open Filter MeasureTheory
open scoped InnerProductSpace
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Closure
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence
open ReservoirSeismicityControl.SeismicitySignedPhysicalTimeIntegratedCoefficient

private instance primitiveFact2 : Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩
private instance primitiveFact4 : Fact ((1 : ENNReal) ≤ 4) :=
  ⟨by norm_num⟩
private instance primitiveFactTop : Fact ((1 : ENNReal) ≤ ⊤) :=
  ⟨by simp⟩

private instance primitiveHolder2Inf :
    (2 : ENNReal).HolderTriple ⊤ 2 := by
  constructor
  simp

private instance primitiveHolderInf2 :
    (⊤ : ENNReal).HolderTriple 2 2 := by
  constructor
  simp

private instance primitiveHolder44 :
    (4 : ENNReal).HolderTriple 4 2 := by
  constructor
  change ((4 : NNReal) : ENNReal)⁻¹ + ((4 : NNReal) : ENNReal)⁻¹ =
    ((2 : NNReal) : ENNReal)⁻¹
  rw [← ENNReal.coe_inv (show (4 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_inv (show (2 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_add]
  apply congrArg (fun z : NNReal => (z : ENNReal))
    (show (4 : NNReal)⁻¹ + (4 : NNReal)⁻¹ = (2 : NNReal)⁻¹ by
      apply Subtype.ext
      norm_num)

/-- Genuine A3 factor smoothing *data* at all physical times. No weak
    derivatives of the nonsmooth PRODUCT occur among the fields. -/
structure PhysicalA7A3FactorSmoothing
    (U : Set (Fin 3 → ℝ)) (Φ : Type*)
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U) where
  gamma2 : ℝ → PhysicalThreeL2 U
  gammaInf : ℝ → Lp ℝ ⊤ (volume.restrict U)
  starInf : Lp ℝ ⊤ (volume.restrict U)
  gamma2N : ℝ → ℕ → PhysicalThreeL2 U
  gammaInfN : ℝ → ℕ → Lp ℝ ⊤ (volume.restrict U)
  starInfN : ℕ → Lp ℝ ⊤ (volume.restrict U)
  Dgamma2 : ℝ → Fin 3 → PhysicalThreeL2 U
  Dstar2 : Fin 3 → PhysicalThreeL2 U
  Dgamma2N : ℝ → ℕ → Fin 3 → PhysicalThreeL2 U
  Dstar2N : ℕ → Fin 3 → PhysicalThreeL2 U
  Dgamma4 : ℝ → Fin 3 → Lp ℝ 4 (volume.restrict U)
  Dstar4 : Fin 3 → Lp ℝ 4 (volume.restrict U)
  Dgamma4N : ℝ → ℕ → Fin 3 → Lp ℝ 4 (volume.restrict U)
  Dstar4N : ℕ → Fin 3 → Lp ℝ 4 (volume.restrict U)
  DDgamma2 : ℝ → Fin 3 → Fin 3 → PhysicalThreeL2 U
  DDstar2 : Fin 3 → Fin 3 → PhysicalThreeL2 U
  DDgamma2N : ℝ → ℕ → Fin 3 → Fin 3 → PhysicalThreeL2 U
  DDstar2N : ℕ → Fin 3 → Fin 3 → PhysicalThreeL2 U
  gamma2_converges : ∀ q, Tendsto (gamma2N q) atTop (nhds (gamma2 q))
  gammaInf_converges : ∀ q, Tendsto (gammaInfN q) atTop (nhds (gammaInf q))
  starInf_converges : Tendsto starInfN atTop (nhds starInf)
  Dgamma2_converges : ∀ q i, Tendsto (fun n => Dgamma2N q n i)
    atTop (nhds (Dgamma2 q i))
  Dstar2_converges : ∀ i, Tendsto (fun n => Dstar2N n i)
    atTop (nhds (Dstar2 i))
  Dgamma4_converges : ∀ q i, Tendsto (fun n => Dgamma4N q n i)
    atTop (nhds (Dgamma4 q i))
  Dstar4_converges : ∀ i, Tendsto (fun n => Dstar4N n i)
    atTop (nhds (Dstar4 i))
  DDgamma2_converges : ∀ q i j, Tendsto (fun n => DDgamma2N q n i j)
    atTop (nhds (DDgamma2 q i j))
  DDstar2_converges : ∀ i j, Tendsto (fun n => DDstar2N n i j)
    atTop (nhds (DDstar2 i j))
  /-- Smooth integration by parts, using the already PROVED classical
      product derivative formula; this is not an assumption on the limit. -/
  smoothFirst : ∀ q n i φ,
    (innerSL ℝ (D i φ))
      ((ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
        (ContinuousLinearMap.mul ℝ ℝ) (gamma2N q n)) (starInfN n)) =
    -(innerSL ℝ (testValue φ))
      ((ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
          (ContinuousLinearMap.mul ℝ ℝ) (Dgamma2N q n i)) (starInfN n) +
        (ContinuousLinearMap.holderL (volume.restrict U) ⊤ 2 2
          (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN q n)) (Dstar2N n i))
  smoothSecond : ∀ q n i j φ,
    (innerSL ℝ (D j φ))
      ((ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
          (ContinuousLinearMap.mul ℝ ℝ) (Dgamma2N q n i)) (starInfN n) +
        (ContinuousLinearMap.holderL (volume.restrict U) ⊤ 2 2
          (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN q n)) (Dstar2N n i)) =
    -(innerSL ℝ (testValue φ))
      ((ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
          (ContinuousLinearMap.mul ℝ ℝ) (DDgamma2N q n i j)) (starInfN n) +
        (ContinuousLinearMap.holderL (volume.restrict U) 4 4 2
          (ContinuousLinearMap.mul ℝ ℝ) (Dgamma4N q n i)) (Dstar4N n j) +
        (ContinuousLinearMap.holderL (volume.restrict U) 4 4 2
          (ContinuousLinearMap.mul ℝ ℝ) (Dgamma4N q n j)) (Dstar4N n i) +
        (ContinuousLinearMap.holderL (volume.restrict U) ⊤ 2 2
          (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN q n)) (DDstar2N n i j))

/-- Construct, rather than assume, the actual coefficient weak-derivative
    graph at every time from smooth factors and strong Hölder limits. -/
noncomputable def PhysicalA7A3FactorSmoothing.weakCoefficient
    {U : Set (Fin 3 → ℝ)} {Φ : Type*}
    {testValue : Φ → PhysicalThreeL2 U}
    {D : Fin 3 → Φ → PhysicalThreeL2 U}
    (S : PhysicalA7A3FactorSmoothing U Φ testValue D) (q : ℝ) :
    PhysicalWeakH2Test U Φ testValue D :=
  physical_A7_actual_A3_coefficient_weak_H2_from_factor_limits
    (volume.restrict U)
    (fun φ : Φ => innerSL ℝ (testValue φ))
    (fun i φ => innerSL ℝ (D i φ))
    (S.gamma2 q) (S.gammaInf q) S.starInf
    (S.gamma2N q) (S.gammaInfN q) S.starInfN
    (S.Dgamma2 q) S.Dstar2 (S.Dgamma2N q) S.Dstar2N
    (S.Dgamma4 q) S.Dstar4 (S.Dgamma4N q) S.Dstar4N
    (S.DDgamma2 q) S.DDstar2 (S.DDgamma2N q) S.DDstar2N
    (S.gamma2_converges q) (S.gammaInf_converges q)
    S.starInf_converges (S.Dgamma2_converges q) S.Dstar2_converges
    (S.Dgamma4_converges q) S.Dstar4_converges
    (S.DDgamma2_converges q) S.DDstar2_converges
    (S.smoothFirst q) (S.smoothSecond q)

/-- Actual A3 product coefficient primitive with all three first and all
    nine mixed second weak spatial derivatives and their linear-lag bounds.
    Time integrability is proved here; it is not a hypothesis. -/
theorem physical_A7_actual_A3_product_primitive_weak_H2_from_factors
    (U : Set (Fin 3 → ℝ)) {Φ : Type*}
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U)
    (S : PhysicalA7A3FactorSmoothing U Φ testValue D)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (v t M0 M1 M2 : ℝ)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hmass : ν.real Set.univ ≤ t - v)
    (hMeas0 : AEStronglyMeasurable (fun q => (S.weakCoefficient q).value) ν)
    (hMeas1 : ∀ i, AEStronglyMeasurable
      (fun q => (S.weakCoefficient q).first i) ν)
    (hMeas2 : ∀ i j, AEStronglyMeasurable
      (fun q => (S.weakCoefficient q).second i j) ν)
    (hbound0 : ∀ᵐ q ∂ν, ‖(S.weakCoefficient q).value‖ ≤ M0)
    (hbound1 : ∀ i, ∀ᵐ q ∂ν,
      ‖(S.weakCoefficient q).first i‖ ≤ M1)
    (hbound2 : ∀ i j, ∀ᵐ q ∂ν,
      ‖(S.weakCoefficient q).second i j‖ ≤ M2) :
    ∃ A : PhysicalWeakH2Test U Φ testValue D,
      A.value = ∫ q, (S.weakCoefficient q).value ∂ν ∧
      (∀ i, A.first i = ∫ q, (S.weakCoefficient q).first i ∂ν) ∧
      (∀ i j, A.second i j = ∫ q, (S.weakCoefficient q).second i j ∂ν) ∧
      ‖A.value‖ ≤ M0 * (t - v) ∧
      (∀ i, ‖A.first i‖ ≤ M1 * (t - v)) ∧
      (∀ i j, ‖A.second i j‖ ≤ M2 * (t - v)) := by
  have hInt0 : Integrable (fun q => (S.weakCoefficient q).value) ν :=
    Integrable.of_bound hMeas0 M0 hbound0
  have hInt1 : ∀ i, Integrable
      (fun q => (S.weakCoefficient q).first i) ν := by
    intro i
    exact Integrable.of_bound (hMeas1 i) M1 (hbound1 i)
  have hInt2 : ∀ i j, Integrable
      (fun q => (S.weakCoefficient q).second i j) ν := by
    intro i j
    exact Integrable.of_bound (hMeas2 i j) M2 (hbound2 i j)
  exact physicalThreeCoefficientPrimitiveWeakH2
    U testValue D S.weakCoefficient ν v t M0 M1 M2
    hM0 hM1 hM2 hmass hInt0 hInt1 hInt2
    hbound0 hbound1 hbound2

#print axioms PhysicalA7A3FactorSmoothing.weakCoefficient
#print axioms physical_A7_actual_A3_product_primitive_weak_H2_from_factors

end ReservoirSeismicityControl.Paper2026
