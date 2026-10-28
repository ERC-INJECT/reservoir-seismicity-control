import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3CausalInterval20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualL2FromBox20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalKernelWeakIntegration
import Mathlib.Tactic

/-!
# Physical A7: concrete compactly supported smooth spatial tests

This is a necessary *concrete* Sobolev identification step, not an abstract
empty test-type specialization and not the completed physical A7 theorem.

The earlier coefficient graph is formulated with an arbitrary test type Φ.
This file specializes its 3+9 weak derivative identities to the complete
class of spatial C∞ functions with compact support contained in the near-well
region U and their *actual* Frechet-coordinate derivatives. L² membership of
these smooth compactly supported tests is made explicit so their L² pairings
are genuine. No weak derivatives of the product or the time primitive are
postulated.

It also records the scalar signed SR reconstruction and its L² existence
from the already proved comparison/pressure box. Neither construction
introduces an arbitrary substitute for the physical solution.

Remaining, NOT proved here: factor mollifications supplied by A3, cross-Lp
representatives, scalar/Bochner Fubini, H² chain/product for the actual
exponential, and uniform H² of the signed physical R field. Passing this
module must not be described as completion of A7.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence

private abbrev Spatial3 := Fin 3 → ℝ

/-- Exactly the real compactly supported smooth spatial tests, equipped with
    the automatically available square-integrable representatives. In the
    future these two `MemLp` fields can be discharged by the standard
    compact-support boundedness theorem, independently of the A7 coefficients.
    In particular no arbitrary `Φ` or arbitrary test-function derivatives are
    used in the weak test identities below. -/
structure A7SmoothCompactTest (U : Set Spatial3) where
  field : Spatial3 → ℝ
  smooth : ContDiff ℝ ⊤ field
  compact_support : IsCompact (tsupport field)
  support_inside : tsupport field ⊆ U
  square_integrable : MemLp field (2 : ENNReal) (volume.restrict U)
  derivative_square_integrable : ∀ i : Fin 3,
    MemLp (fun x => (fderiv ℝ field x)
        (ReservoirSeismicityControl.SeismicitySignedPhysicalKernelWeakIntegration.coordinateDirection3 i))
      (2 : ENNReal) (volume.restrict U)

/-- Spatial test as a concrete L² field on the local region. -/
noncomputable def a7TestL2 (U : Set Spatial3)
    (φ : A7SmoothCompactTest U) : PhysicalThreeL2 U :=
  φ.square_integrable.toLp

/-- Its ACTUAL coordinate Frechet derivative as an L² field. -/
noncomputable def a7TestDerivativeL2 (U : Set Spatial3)
    (i : Fin 3) (φ : A7SmoothCompactTest U) : PhysicalThreeL2 U :=
  (φ.derivative_square_integrable i).toLp

/-- The concrete local distributional H² graph, tested against every smooth
    compactly supported field (and its true spatial coordinate derivatives).
    This is not an arbitrary test-type graph. -/
noncomputable abbrev A7ConcreteWeakH2 (U : Set Spatial3) :=
  PhysicalWeakH2Test U (A7SmoothCompactTest U)
    (a7TestL2 U) (a7TestDerivativeL2 U)

/-- All three first and all nine ordered second weak derivative identities
    are actual tests against the local smooth compact test class. The graph's
    fields are L²(volume.restrict U). -/
theorem a7_concrete_weak_derivative_identities
    (U : Set Spatial3) (A : A7ConcreteWeakH2 U) :
    (∀ i (φ : A7SmoothCompactTest U),
      (innerSL ℝ (a7TestDerivativeL2 U i φ)) A.value =
        -(innerSL ℝ (a7TestL2 U φ)) (A.first i)) ∧
    (∀ i j (φ : A7SmoothCompactTest U),
      (innerSL ℝ (a7TestDerivativeL2 U j φ)) (A.first i) =
        -(innerSL ℝ (a7TestL2 U φ)) (A.second i j)) := by
  constructor
  · intro i φ
    exact A.weak_first i φ
  · intro i j φ
    exact A.weak_second i j φ

/-- Equivalent finite graph-size control for all thirteen Sobolev jets.
    This explicit estimate is useful when applying exponential composition:
    the primitive grows at most linearly with the causal lag. -/
noncomputable def a7ConcreteH2GraphSize (U : Set Spatial3)
    (A : A7ConcreteWeakH2 U) : ℝ :=
  ‖A.value‖ + (∑ i : Fin 3, ‖A.first i‖) +
    (∑ i : Fin 3, ∑ j : Fin 3, ‖A.second i j‖)

theorem a7_concrete_H2_graph_size_bound
    (U : Set Spatial3) (A : A7ConcreteWeakH2 U)
    (M0 M1 M2 τ : ℝ)
    (h0 : ‖A.value‖ ≤ M0 * τ)
    (h1 : ∀ i, ‖A.first i‖ ≤ M1 * τ)
    (h2 : ∀ i j, ‖A.second i j‖ ≤ M2 * τ) :
    a7ConcreteH2GraphSize U A ≤ (M0 + 3 * M1 + 9 * M2) * τ := by
  have hs1 : (∑ i : Fin 3, ‖A.first i‖) ≤
      ∑ _i : Fin 3, M1 * τ := by
    apply Finset.sum_le_sum
    intro i _
    exact h1 i
  have hs2 : (∑ i : Fin 3, ∑ j : Fin 3, ‖A.second i j‖) ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3, M2 * τ := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact h2 i j
  calc
    a7ConcreteH2GraphSize U A ≤ M0 * τ +
        (∑ _i : Fin 3, M1 * τ) +
        (∑ _i : Fin 3, ∑ _j : Fin 3, M2 * τ) := by
      exact add_le_add (add_le_add h0 hs1) hs2
    _ = (M0 + 3 * M1 + 9 * M2) * τ := by
      simp [Fin.sum_univ_succ] <;> ring

/-- The new A3 causal primitive applies to the concrete, non-vacuous
    distributional test class. In particular, it supplies the *actual*
    weak-test identities along with all 13 quantitative L² bounds, rather
    than merely providing an abstract graph against arbitrary Φ.

    `S` contains the ordinary factor Sobolev approximations. Deriving S
    from the manuscript A3 and identifying the scalar primitive with its
    Bochner representative remain separate standard-analysis inputs.
-/
theorem physical_A7_A3_causal_primitive_concrete_test_graph
    (U : Set Spatial3)
    (S : PhysicalA7A3FactorSmoothing U (A7SmoothCompactTest U)
      (a7TestL2 U) (a7TestDerivativeL2 U))
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
    ∃ A : A7ConcreteWeakH2 U,
      A.value = ∫ q in v..t, (S.weakCoefficient q).value ∧
      (∀ i, A.first i = ∫ q in v..t, (S.weakCoefficient q).first i) ∧
      (∀ i j, A.second i j = ∫ q in v..t,
        (S.weakCoefficient q).second i j) ∧
      (∀ i (φ : A7SmoothCompactTest U),
        (innerSL ℝ (a7TestDerivativeL2 U i φ)) A.value =
          -(innerSL ℝ (a7TestL2 U φ)) (A.first i)) ∧
      (∀ i j (φ : A7SmoothCompactTest U),
        (innerSL ℝ (a7TestDerivativeL2 U j φ)) (A.first i) =
          -(innerSL ℝ (a7TestL2 U φ)) (A.second i j)) ∧
      ‖A.value‖ ≤ M0 * (t - v) ∧
      (∀ i, ‖A.first i‖ ≤ M1 * (t - v)) ∧
      (∀ i j, ‖A.second i j‖ ≤ M2 * (t - v)) ∧
      a7ConcreteH2GraphSize U A ≤
        (M0 + 3 * M1 + 9 * M2) * (t - v) := by
  have hcore := physical_A7_actual_A3_causal_primitive_from_factor_bounds
    U (a7TestL2 U) (a7TestDerivativeL2 U) S
    v t G0 GInf G1 G4 G2 S1 S4 S2
    hv hvt hG0 hGInf hG1 hG4 hG2 hS1 hS4 hS2
    hMeasG0 hMeasGInf hMeasG1 hMeasG4 hMeasG2
    hBoundG0 hBoundGInf hBoundG1 hBoundG4 hBoundG2
    hBoundS1 hBoundS4 hBoundS2
  dsimp only at hcore ⊢
  rcases hcore with ⟨A, hval, hfirst, hsecond, hvalb, hfirstb, hsecondb⟩
  obtain ⟨hfirstTests, hsecondTests⟩ :=
    a7_concrete_weak_derivative_identities U A
  exact ⟨A, hval, hfirst, hsecond, hfirstTests, hsecondTests,
    hvalb, hfirstb, hsecondb,
    a7_concrete_H2_graph_size_bound U A _ _ _ _ hvalb hfirstb hsecondb⟩

#print axioms a7_concrete_weak_derivative_identities
#print axioms a7_concrete_H2_graph_size_bound
#print axioms physical_A7_A3_causal_primitive_concrete_test_graph

end ReservoirSeismicityControl.Paper2026
