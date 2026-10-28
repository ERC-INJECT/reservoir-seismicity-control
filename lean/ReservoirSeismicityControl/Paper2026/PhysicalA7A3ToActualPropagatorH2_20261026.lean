import ReservoirSeismicityControl.Paper2026.PhysicalA7ConcreteBanachH2Gate20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualDampedHessianFromA3_20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3CausalInterval20261026
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# A7-M1: connect the actual A3 weak H² primitive to the actual physical propagator

This module closes the previously disconnected A3-primitive and propagator
branches. It uses the *concrete* closed thirteen-component H² space on U,
not an arbitrary H or an arbitrarily chosen propagator E.

There are two explicitly marked STANDARD ANALYSIS dependencies, neither of
which asserts a regularity conclusion for the seismicity solution:

* `hPrimitiveFubini` is the representative theorem for the Bochner time
  integral of the coefficient `gamma2 Rstar`. This is exactly the ordinary
  time-space Fubini theorem that must be instantiated from measurable A3
  coefficient paths.
* `hSobolevExp` is the universal bounded-domain weak-H² exponential
  composition theorem, with its quantitative derivative estimate. The
  hypothesis ranges over *every* weak-H² test graph and does not assert
  H² of the physical propagator, of Y or of R.

The conclusion builds a concrete weak-H² spatial primitive AND an element E
of the real A7PhysicalH2 U Banach space, identifies E with the physical
exp(-∫ gamma2 Rstar), and proves its exponentially damped quadratic envelope.
The coefficient product, all 13 causal derivative estimates, and the damping
bound are obtained by existing proofs, not postulated. This is a large
physical subgoal, NOT full M1 or A7; the forcing-kernel Bochner representative
and positive reciprocal reconstruction remain separate tasks.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence

private abbrev Spatial3 := Fin 3 → ℝ

set_option maxHeartbeats 1200000

/-- Physical A3 → actual H² propagator. No hypotheses about H²(Y), H²(R),
    the propagator's H² norm, or about its physical weak derivatives.
    `hSobolevExp` is one universally quantified *standard* Sobolev
    composition interface, not a manuscript-specific assumption. -/
theorem physical_A7_actual_A3_to_propagator_H2
    (U : Set Spatial3) [IsFiniteMeasure (volume.restrict U)]
    (gamma2 : Spatial3 → ℝ → ℝ) (Rstar : Spatial3 → ℝ)
    (S : PhysicalA7A3FactorSmoothing U (A7SmoothCompactTest U)
      (a7TestL2 U) (a7TestDerivativeL2 U))
    (v t gamma2m Rstarm : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t)
    (hg2m : 0 < gamma2m) (hRstarm : 0 < Rstarm)
    (hA3 : ∀ᵐ z ∂((volume.restrict U).prod (volume : Measure ℝ)),
      0 ≤ z.2 → gamma2m ≤ gamma2 z.1 z.2)
    (hRstar : ∀ᵐ x ∂(volume.restrict U), Rstarm ≤ Rstar x)
    (hTimeInt : ∀ᵐ x ∂(volume.restrict U),
      ∀ r q : ℝ, 0 ≤ r → r ≤ q →
        IntervalIntegrable
          (physicalA7CausalCoefficient gamma2 Rstar
            (gamma2m * Rstarm) x) volume r q)
    (G0 GInf G1 G4 G2 S1 S4 S2 : ℝ)
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
    (hBoundS2 : ∀ i j, ‖S.DDstar2 i j‖ ≤ S2)
    /- Ordinary L² Bochner–pointwise time-Fubini for the coefficient. -/
    (hPrimitiveFubini : ∀ᵐ x ∂(volume.restrict U),
      ((∫ q in v..t, (S.weakCoefficient q).value) x : ℝ) =
        ∫ q in v..t, gamma2 x q * Rstar x)
    /- Universal *standard* bounded-domain H² exponential rule. The
       constants depend on the domain and Sobolev embedding, not v,t.
       The graph norm is the verified sum of its actual 13 L² jets. -/
    (Cexp0 Cexp1 Cexp2 : ℝ)
    (hCexp0 : 0 ≤ Cexp0) (hCexp1 : 0 ≤ Cexp1)
    (hCexp2 : 0 ≤ Cexp2)
    (hSobolevExp : ∀ (A : A7ConcreteWeakH2 U) (lag minCoeff : ℝ),
      0 ≤ lag → 0 < minCoeff →
      (∀ᵐ x ∂(volume.restrict U),
        minCoeff * lag ≤ (A.value x : ℝ)) →
      ∃ E : A7PhysicalH2 U,
        (∀ᵐ x ∂(volume.restrict U),
          (a7PhysicalH2Embedding U E x : ℝ) =
            Real.exp (-(A.value x : ℝ))) ∧
        ‖E‖ ≤ Real.exp (-(minCoeff * lag)) *
          (Cexp0 + Cexp1 * a7ConcreteH2GraphSize U A +
            Cexp2 * (a7ConcreteH2GraphSize U A) ^ 2)) :
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
    let MA := M0 + 3 * M1 + 9 * M2
    ∃ (A : A7ConcreteWeakH2 U) (E : A7PhysicalH2 U),
      (a7PhysicalH2Embedding U (a7ConcreteWeakToBanach U A) = A.value) ∧
      (∀ᵐ x ∂(volume.restrict U),
        (A.value x : ℝ) = ∫ q in v..t, gamma2 x q * Rstar x) ∧
      a7ConcreteH2GraphSize U A ≤ MA * (t - v) ∧
      (∀ᵐ x ∂(volume.restrict U),
        (a7PhysicalH2Embedding U E x : ℝ) =
          Real.exp (-(∫ q in v..t, gamma2 x q * Rstar x))) ∧
      ‖E‖ ≤ Real.exp (-(gamma2m * Rstarm * (t - v))) *
        (Cexp0 + Cexp1 * (MA * (t - v)) +
          Cexp2 * (MA * (t - v)) ^ 2) := by
  dsimp only
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
  let MA := M0 + 3 * M1 + 9 * M2
  have hcore := physical_A7_A3_causal_primitive_concrete_test_graph
    U S v t G0 GInf G1 G4 G2 S1 S4 S2 hv hvt
    hG0 hGInf hG1 hG4 hG2 hS1 hS4 hS2
    hMeasG0 hMeasGInf hMeasG1 hMeasG4 hMeasG2
    hBoundG0 hBoundGInf hBoundG1 hBoundG4 hBoundG2
    hBoundS1 hBoundS4 hBoundS2
  dsimp only at hcore
  obtain ⟨A, hAvalue, _hAf, _hAs, _hFirstTest, _hSecondTest,
    _hA0, _hA1, _hA2, hAgraph⟩ := hcore
  have hAactual : ∀ᵐ x ∂(volume.restrict U),
      (A.value x : ℝ) = ∫ q in v..t, gamma2 x q * Rstar x := by
    filter_upwards [hPrimitiveFubini] with x hx
    calc
      (A.value x : ℝ) =
          ((∫ q in v..t, (S.weakCoefficient q).value) x : ℝ) := by
            rw [hAvalue]
      _ = ∫ q in v..t, gamma2 x q * Rstar x := hx
  have hLower := physical_A7_actual_primitive_lower_linear_from_A3
    (volume.restrict U) gamma2 Rstar gamma2m Rstarm
    hg2m hRstarm hA3 hRstar hTimeInt
  have hAmin : ∀ᵐ x ∂(volume.restrict U),
      gamma2m * Rstarm * (t - v) ≤ (A.value x : ℝ) := by
    filter_upwards [hLower, hAactual] with x hx ha
    rw [ha]
    exact hx v t hv hvt
  have hLag : 0 ≤ t - v := sub_nonneg.mpr hvt
  have hMin : 0 < gamma2m * Rstarm := mul_pos hg2m hRstarm
  obtain ⟨E, hErep, hEnorm⟩ :=
    hSobolevExp A (t - v) (gamma2m * Rstarm) hLag hMin hAmin
  have hGraphNonneg : 0 ≤ a7ConcreteH2GraphSize U A := by
    dsimp [a7ConcreteH2GraphSize]
    positivity
  have hMAgraph : a7ConcreteH2GraphSize U A ≤ MA * (t - v) := by
    exact hAgraph
  have hMaxNonneg : 0 ≤ MA * (t - v) :=
    le_trans hGraphNonneg hMAgraph
  have hGraphSquare :
      (a7ConcreteH2GraphSize U A) ^ 2 ≤ (MA * (t - v)) ^ 2 := by
    calc
      (a7ConcreteH2GraphSize U A) ^ 2 =
          (a7ConcreteH2GraphSize U A) *
            (a7ConcreteH2GraphSize U A) := pow_two _
      _ ≤ (MA * (t - v)) * (a7ConcreteH2GraphSize U A) :=
        mul_le_mul_of_nonneg_right hMAgraph hGraphNonneg
      _ ≤ (MA * (t - v)) * (MA * (t - v)) :=
        mul_le_mul_of_nonneg_left hMAgraph hMaxNonneg
      _ = (MA * (t - v)) ^ 2 := (pow_two _).symm
  have hPoly :
      Cexp0 + Cexp1 * a7ConcreteH2GraphSize U A +
        Cexp2 * (a7ConcreteH2GraphSize U A) ^ 2 ≤
      Cexp0 + Cexp1 * (MA * (t - v)) +
        Cexp2 * (MA * (t - v)) ^ 2 := by
    have hlin := mul_le_mul_of_nonneg_left hMAgraph hCexp1
    have hquad := mul_le_mul_of_nonneg_left hGraphSquare hCexp2
    linarith
  refine ⟨A, E, a7PhysicalH2Embedding_of_weak U A, hAactual,
    hMAgraph, ?_, ?_⟩
  · filter_upwards [hErep, hAactual] with x he ha
    rw [he, ha]
  · exact hEnorm.trans (mul_le_mul_of_nonneg_left hPoly
      (le_of_lt (Real.exp_pos _)))

#print axioms physical_A7_actual_A3_to_propagator_H2

end ReservoirSeismicityControl.Paper2026
