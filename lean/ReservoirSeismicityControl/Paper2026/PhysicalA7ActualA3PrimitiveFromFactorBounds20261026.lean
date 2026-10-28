import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3PrimitiveFromFactors20261026
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# A7: eliminate separate time measurability and bounds of A3 product jets

The previous physical A3 primitive theorem proved weak H² of the actual
coefficient gamma2(·,q)*Rstar and its time primitive, but requested 13
additional hypotheses asserting measurability and uniform L² bounds of
THE PRODUCT value, gradient and Hessian curves.

This module derives all thirteen from the measurable factor curves and
uniform factor Sobolev norms. Rstar is fixed in time. Only the factor
smoothing/IBP data required by the standard external Sobolev approximation
result are retained. No kernel estimate or diffusion argument is repeated.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Closure
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence

private instance factorBoundsFactTwo : Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩
private instance factorBoundsFactFour : Fact ((1 : ENNReal) ≤ 4) :=
  ⟨by norm_num⟩
private instance factorBoundsFactTop : Fact ((1 : ENNReal) ≤ ⊤) :=
  ⟨by simp⟩

private instance factorBoundsHolder2Inf :
    (2 : ENNReal).HolderTriple ⊤ 2 := by
  constructor
  simp

private instance factorBoundsHolderInf2 :
    (⊤ : ENNReal).HolderTriple 2 2 := by
  constructor
  simp

private instance factorBoundsHolder44 :
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

/-- Separate factor-path measurability suffices for measurable
    multiplication by a fixed spatial factor, in any Hölder triple. -/
private theorem fixed_bilinear_aestronglyMeasurable
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G)
    (ν : Measure ℝ) (f : ℝ → E) (g : F)
    (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (fun q => (B (f q)) g) ν := by
  have hcont : Continuous (fun p : E × F => (B p.1) p.2) :=
    B.continuous₂
  exact hcont.comp_aestronglyMeasurable
    (hf.prodMk aestronglyMeasurable_const)

/-- Bilinear norm bounds, with the actual operator norm of Mathlib's
    continuous Hölder multiplication map. -/
private theorem bilinear_bound_of_factors
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G)
    (x : E) (y : F) (Mx My : ℝ)
    (hx : ‖x‖ ≤ Mx) (hy : ‖y‖ ≤ My)
    (hMx : 0 ≤ Mx) (hMy : 0 ≤ My) :
    ‖B x y‖ ≤ ‖B‖ * Mx * My := by
  calc
    ‖B x y‖ ≤ ‖B x‖ * ‖y‖ := (B x).le_opNorm y
    _ ≤ (‖B‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y)
    _ ≤ (‖B‖ * Mx) * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (norm_nonneg B)) (norm_nonneg y)
    _ ≤ (‖B‖ * Mx) * My :=
      mul_le_mul_of_nonneg_left hy
        (mul_nonneg (norm_nonneg B) hMx)

/-- A3 measurable and uniformly bounded *factor* paths supply the
    entire weak-H² causal primitive of a=gamma2*Rstar, with all 3+9
    derivative bounds. No independent measurability, integrability or
    norm estimate of any PRODUCT jet is assumed. -/
theorem physical_A7_actual_A3_primitive_from_factor_bounds
    (U : Set (Fin 3 → ℝ)) {Φ : Type*}
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U)
    (S : PhysicalA7A3FactorSmoothing U Φ testValue D)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (v t G0 GInf G1 G4 G2 S1 S4 S2 : ℝ)
    (hG0 : 0 ≤ G0) (hGInf : 0 ≤ GInf) (hG1 : 0 ≤ G1)
    (hG4 : 0 ≤ G4) (hG2 : 0 ≤ G2)
    (hS1 : 0 ≤ S1) (hS4 : 0 ≤ S4) (hS2 : 0 ≤ S2)
    (hmass : ν.real Set.univ ≤ t - v)
    (hMeasG0 : AEStronglyMeasurable S.gamma2 ν)
    (hMeasGInf : AEStronglyMeasurable S.gammaInf ν)
    (hMeasG1 : ∀ i, AEStronglyMeasurable (fun q => S.Dgamma2 q i) ν)
    (hMeasG4 : ∀ i, AEStronglyMeasurable (fun q => S.Dgamma4 q i) ν)
    (hMeasG2 : ∀ i j, AEStronglyMeasurable (fun q => S.DDgamma2 q i j) ν)
    (hBoundG0 : ∀ᵐ q ∂ν, ‖S.gamma2 q‖ ≤ G0)
    (hBoundGInf : ∀ᵐ q ∂ν, ‖S.gammaInf q‖ ≤ GInf)
    (hBoundG1 : ∀ i, ∀ᵐ q ∂ν, ‖S.Dgamma2 q i‖ ≤ G1)
    (hBoundG4 : ∀ i, ∀ᵐ q ∂ν, ‖S.Dgamma4 q i‖ ≤ G4)
    (hBoundG2 : ∀ i j, ∀ᵐ q ∂ν, ‖S.DDgamma2 q i j‖ ≤ G2)
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
      ‖B44‖ * G4 * S4 + ‖B44‖ * G4 * S4 +
      ‖B02‖ * GInf * S2
    ∃ A : PhysicalWeakH2Test U Φ testValue D,
      A.value = ∫ q, (S.weakCoefficient q).value ∂ν ∧
      (∀ i, A.first i = ∫ q, (S.weakCoefficient q).first i ∂ν) ∧
      (∀ i j, A.second i j = ∫ q, (S.weakCoefficient q).second i j ∂ν) ∧
      ‖A.value‖ ≤ M0 * (t - v) ∧
      (∀ i, ‖A.first i‖ ≤ M1 * (t - v)) ∧
      (∀ i j, ‖A.second i j‖ ≤ M2 * (t - v)) := by
  dsimp only
  let B20 := ContinuousLinearMap.holderL (volume.restrict U) 2 ⊤ 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let B02 := ContinuousLinearMap.holderL (volume.restrict U) ⊤ 2 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let B44 := ContinuousLinearMap.holderL (volume.restrict U) 4 4 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let M0 : ℝ := ‖B20‖ * G0 * ‖S.starInf‖
  let M1 : ℝ := ‖B20‖ * G1 * ‖S.starInf‖ + ‖B02‖ * GInf * S1
  let M2 : ℝ := ‖B20‖ * G2 * ‖S.starInf‖ +
    ‖B44‖ * G4 * S4 + ‖B44‖ * G4 * S4 + ‖B02‖ * GInf * S2
  have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hM1 : 0 ≤ M1 := by dsimp [M1]; positivity
  have hM2 : 0 ≤ M2 := by dsimp [M2]; positivity
  have hm0 : AEStronglyMeasurable
      (fun q => (S.weakCoefficient q).value) ν := by
    change AEStronglyMeasurable (fun q => (B20 (S.gamma2 q)) S.starInf) ν
    exact fixed_bilinear_aestronglyMeasurable B20 ν S.gamma2 S.starInf hMeasG0
  have hm1 : ∀ i, AEStronglyMeasurable
      (fun q => (S.weakCoefficient q).first i) ν := by
    intro i
    change AEStronglyMeasurable (fun q =>
      (B20 (S.Dgamma2 q i)) S.starInf +
        (B02 (S.gammaInf q)) (S.Dstar2 i)) ν
    exact (fixed_bilinear_aestronglyMeasurable B20 ν
      (fun q => S.Dgamma2 q i) S.starInf (hMeasG1 i)).add
      (fixed_bilinear_aestronglyMeasurable B02 ν
        S.gammaInf (S.Dstar2 i) hMeasGInf)
  have hm2 : ∀ i j, AEStronglyMeasurable
      (fun q => (S.weakCoefficient q).second i j) ν := by
    intro i j
    change AEStronglyMeasurable (fun q =>
      (B20 (S.DDgamma2 q i j)) S.starInf +
        (B44 (S.Dgamma4 q i)) (S.Dstar4 j) +
        (B44 (S.Dgamma4 q j)) (S.Dstar4 i) +
        (B02 (S.gammaInf q)) (S.DDstar2 i j)) ν
    exact (((fixed_bilinear_aestronglyMeasurable B20 ν
      (fun q => S.DDgamma2 q i j) S.starInf (hMeasG2 i j)).add
      (fixed_bilinear_aestronglyMeasurable B44 ν
        (fun q => S.Dgamma4 q i) (S.Dstar4 j) (hMeasG4 i))).add
      (fixed_bilinear_aestronglyMeasurable B44 ν
        (fun q => S.Dgamma4 q j) (S.Dstar4 i) (hMeasG4 j))).add
      (fixed_bilinear_aestronglyMeasurable B02 ν
        S.gammaInf (S.DDstar2 i j) hMeasGInf)
  have hb0 : ∀ᵐ q ∂ν, ‖(S.weakCoefficient q).value‖ ≤ M0 := by
    filter_upwards [hBoundG0] with q hq
    change ‖(B20 (S.gamma2 q)) S.starInf‖ ≤ M0
    exact bilinear_bound_of_factors B20 _ _ G0 ‖S.starInf‖
      hq (le_refl _) hG0 (norm_nonneg _)
  have hb1 : ∀ i, ∀ᵐ q ∂ν,
      ‖(S.weakCoefficient q).first i‖ ≤ M1 := by
    intro i
    filter_upwards [hBoundG1 i, hBoundGInf] with q hq1 hqInf
    change ‖(B20 (S.Dgamma2 q i)) S.starInf +
      (B02 (S.gammaInf q)) (S.Dstar2 i)‖ ≤ M1
    calc
      _ ≤ ‖(B20 (S.Dgamma2 q i)) S.starInf‖ +
          ‖(B02 (S.gammaInf q)) (S.Dstar2 i)‖ := norm_add_le _ _
      _ ≤ M1 := by
        exact add_le_add
          (bilinear_bound_of_factors B20 _ _ G1 ‖S.starInf‖
            hq1 (le_refl _) hG1 (norm_nonneg _))
          (bilinear_bound_of_factors B02 _ _ GInf S1
            hqInf (hBoundS1 i) hGInf hS1)
  have hb2 : ∀ i j, ∀ᵐ q ∂ν,
      ‖(S.weakCoefficient q).second i j‖ ≤ M2 := by
    intro i j
    filter_upwards [hBoundG2 i j, hBoundG4 i, hBoundG4 j,
      hBoundGInf] with q hq2 hq4i hq4j hqInf
    change ‖(B20 (S.DDgamma2 q i j)) S.starInf +
      (B44 (S.Dgamma4 q i)) (S.Dstar4 j) +
      (B44 (S.Dgamma4 q j)) (S.Dstar4 i) +
      (B02 (S.gammaInf q)) (S.DDstar2 i j)‖ ≤ M2
    calc
      _ ≤ ‖(B20 (S.DDgamma2 q i j)) S.starInf‖ +
          ‖(B44 (S.Dgamma4 q i)) (S.Dstar4 j)‖ +
          ‖(B44 (S.Dgamma4 q j)) (S.Dstar4 i)‖ +
          ‖(B02 (S.gammaInf q)) (S.DDstar2 i j)‖ := by
        have h01 := norm_add_le
          ((B20 (S.DDgamma2 q i j)) S.starInf)
          ((B44 (S.Dgamma4 q i)) (S.Dstar4 j))
        have h012 := norm_add_le
          ((B20 (S.DDgamma2 q i j)) S.starInf +
            (B44 (S.Dgamma4 q i)) (S.Dstar4 j))
          ((B44 (S.Dgamma4 q j)) (S.Dstar4 i))
        have h0123 := norm_add_le
          ((B20 (S.DDgamma2 q i j)) S.starInf +
            (B44 (S.Dgamma4 q i)) (S.Dstar4 j) +
            (B44 (S.Dgamma4 q j)) (S.Dstar4 i))
          ((B02 (S.gammaInf q)) (S.DDstar2 i j))
        linarith
      _ ≤ M2 := by
        dsimp only [M2]
        exact add_le_add
          (add_le_add
            (add_le_add
              (bilinear_bound_of_factors B20 _ _ G2 ‖S.starInf‖
                hq2 (le_refl _) hG2 (norm_nonneg _))
              (bilinear_bound_of_factors B44 _ _ G4 S4
                hq4i (hBoundS4 j) hG4 hS4))
            (bilinear_bound_of_factors B44 _ _ G4 S4
              hq4j (hBoundS4 i) hG4 hS4))
          (bilinear_bound_of_factors B02 _ _ GInf S2
            hqInf (hBoundS2 i j) hGInf hS2)
  exact physical_A7_actual_A3_product_primitive_weak_H2_from_factors
    U testValue D S ν v t M0 M1 M2
    hM0 hM1 hM2 hmass hm0 hm1 hm2 hb0 hb1 hb2

#print axioms physical_A7_actual_A3_primitive_from_factor_bounds

end ReservoirSeismicityControl.Paper2026
