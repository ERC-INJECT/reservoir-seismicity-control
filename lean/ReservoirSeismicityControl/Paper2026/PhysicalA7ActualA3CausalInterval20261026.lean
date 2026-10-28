import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3PrimitiveFromFactorBounds20261026
import ReservoirSeismicityControl.PressurePositiveSemigroupTimeIntervalCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# A7 physical causal interval, not an arbitrary finite time measure

This eliminates two independent inputs from the preceding factor-bounds
primitive theorem:
* the arbitrary finite time measure `ν`, now the real Lebesgue measure
  restricted to the actual causal interval `[v,t)`;
* the separately assumed mass estimate, now the already proved geometric
  identity `pressure_time_Ico_real_mass`.

The resulting coefficient value, three first weak derivatives, and nine
second weak derivatives are actual interval Bochner integrals over `v..t`,
not merely integrals against an unrelated time measure. Standard Sobolev
factor smoothing and smooth integration by parts remain external inputs.
No kernel estimate, diffusion argument, custom axiom, or `sorry` is added.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence

private instance causalFact2 : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
private instance causalFact4 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
private instance causalFactTop : Fact ((1 : ENNReal) ≤ ⊤) := ⟨by simp⟩

private instance causalHolder2Inf : (2 : ENNReal).HolderTriple ⊤ 2 := by
  constructor
  simp

private instance causalHolderInf2 : (⊤ : ENNReal).HolderTriple 2 2 := by
  constructor
  simp

private instance causalHolder44 : (4 : ENNReal).HolderTriple 4 2 := by
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

/-- Convert Bochner integration on the physical half-open time interval
    into the conventional causal interval-integral notation. -/
private theorem physical_A7_causal_bochner_eq_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (v t : ℝ) (hvt : v ≤ t) :
    (∫ q, f q ∂(volume.restrict (Set.Ico v t))) = ∫ q in v..t, f q := by
  rw [intervalIntegral.integral_of_le hvt]
  rw [Measure.restrict_congr_set (α := ℝ) (μ := volume) Ico_ae_eq_Ioc]

/-- The *physical* time primitive of the A3 coefficient product, including
    its entire weak H² graph, with canonical Lebesgue interval integration.

    Measurability and norm bounds are required only for the original A3
    factor curves, not for any product jet or for the primitive. -/
theorem physical_A7_actual_A3_causal_primitive_from_factor_bounds
    (U : Set (Fin 3 → ℝ)) {Φ : Type*}
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U)
    (S : PhysicalA7A3FactorSmoothing U Φ testValue D)
    (v t G0 GInf G1 G4 G2 S1 S4 S2 : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t)
    (hG0 : 0 ≤ G0) (hGInf : 0 ≤ GInf) (hG1 : 0 ≤ G1)
    (hG4 : 0 ≤ G4) (hG2 : 0 ≤ G2)
    (hS1 : 0 ≤ S1) (hS4 : 0 ≤ S4) (hS2 : 0 ≤ S2)
    (hMeasG0 : AEStronglyMeasurable S.gamma2
      (volume.restrict (Set.Ico v t)))
    (hMeasGInf : AEStronglyMeasurable S.gammaInf
      (volume.restrict (Set.Ico v t)))
    (hMeasG1 : ∀ i, AEStronglyMeasurable (fun q => S.Dgamma2 q i)
      (volume.restrict (Set.Ico v t)))
    (hMeasG4 : ∀ i, AEStronglyMeasurable (fun q => S.Dgamma4 q i)
      (volume.restrict (Set.Ico v t)))
    (hMeasG2 : ∀ i j, AEStronglyMeasurable (fun q => S.DDgamma2 q i j)
      (volume.restrict (Set.Ico v t)))
    (hBoundG0 : ∀ᵐ q ∂(volume.restrict (Set.Ico v t)),
      ‖S.gamma2 q‖ ≤ G0)
    (hBoundGInf : ∀ᵐ q ∂(volume.restrict (Set.Ico v t)),
      ‖S.gammaInf q‖ ≤ GInf)
    (hBoundG1 : ∀ i, ∀ᵐ q ∂(volume.restrict (Set.Ico v t)),
      ‖S.Dgamma2 q i‖ ≤ G1)
    (hBoundG4 : ∀ i, ∀ᵐ q ∂(volume.restrict (Set.Ico v t)),
      ‖S.Dgamma4 q i‖ ≤ G4)
    (hBoundG2 : ∀ i j, ∀ᵐ q ∂(volume.restrict (Set.Ico v t)),
      ‖S.DDgamma2 q i j‖ ≤ G2)
    (hBoundS1 : ∀ i, ‖S.Dstar2 i‖ ≤ S1)
    (hBoundS4 : ∀ i, ‖S.Dstar4 i‖ ≤ S4)
    (hBoundS2 : ∀ i j, ‖S.DDstar2 i j‖ ≤ S2) :
    let B20 := ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
      (ContinuousLinearMap.mul ℝ ℝ)
    let B02 := ContinuousLinearMap.holderL (volume.restrict U) ⊤ 2 2
      (ContinuousLinearMap.mul ℝ ℝ)
    let B44 := ContinuousLinearMap.holderL (volume.restrict U) 4 4 2
      (ContinuousLinearMap.mul ℝ ℝ)
    let M0 := ‖B20‖ * G0 * ‖S.starInf‖
    let M1 := ‖B20‖ * G1 * ‖S.starInf‖ + ‖B02‖ * GInf * S1
    let M2 := ‖B20‖ * G2 * ‖S.starInf‖ +
      ‖B44‖ * G4 * S4 + ‖B44‖ * G4 * S4 + ‖B02‖ * GInf * S2
    ∃ A : PhysicalWeakH2Test U Φ testValue D,
      A.value = ∫ q in v..t, (S.weakCoefficient q).value ∧
      (∀ i, A.first i = ∫ q in v..t, (S.weakCoefficient q).first i) ∧
      (∀ i j, A.second i j = ∫ q in v..t,
        (S.weakCoefficient q).second i j) ∧
      ‖A.value‖ ≤ M0 * (t - v) ∧
      (∀ i, ‖A.first i‖ ≤ M1 * (t - v)) ∧
      (∀ i j, ‖A.second i j‖ ≤ M2 * (t - v)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ico v t)) :=
    ReservoirSeismicityControl.pressure_time_Ico_finite v t
  have hmass : (volume.restrict (Set.Ico v t)).real Set.univ ≤ t - v := by
    exact le_of_eq (ReservoirSeismicityControl.pressure_time_Ico_real_mass v t hvt)
  have hcore := physical_A7_actual_A3_primitive_from_factor_bounds
    U testValue D S (volume.restrict (Set.Ico v t))
    v t G0 GInf G1 G4 G2 S1 S4 S2
    hG0 hGInf hG1 hG4 hG2 hS1 hS4 hS2 hmass
    hMeasG0 hMeasGInf hMeasG1 hMeasG4 hMeasG2
    hBoundG0 hBoundGInf hBoundG1 hBoundG4 hBoundG2
    hBoundS1 hBoundS4 hBoundS2
  dsimp only at hcore ⊢
  rcases hcore with ⟨A, h0, h1, h2, hb0, hb1, hb2⟩
  refine ⟨A, ?_, ?_, ?_, hb0, hb1, hb2⟩
  · exact h0.trans (physical_A7_causal_bochner_eq_interval
      (fun q => (S.weakCoefficient q).value) v t hvt)
  · intro i
    exact (h1 i).trans (physical_A7_causal_bochner_eq_interval
      (fun q => (S.weakCoefficient q).first i) v t hvt)
  · intro i j
    exact (h2 i j).trans (physical_A7_causal_bochner_eq_interval
      (fun q => (S.weakCoefficient q).second i j) v t hvt)

#print axioms physical_A7_actual_A3_causal_primitive_from_factor_bounds

end ReservoirSeismicityControl.Paper2026
