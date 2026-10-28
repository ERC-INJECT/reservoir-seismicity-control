import ReservoirSeismicityControl.SeismicitySignedPhysicalKernelWeakIntegration
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1 — smooth physical 3D kernel derivative-to-weak bridge

The previous classical kernel module computed all coordinate-section derivatives
of `K = exp(-A) b`. The subsequent integration-by-parts module required as
*separate hypotheses* that the Fréchet directional derivatives of K and its
first derivatives agree with those formulas. This module **proves that
identification** by composing Fréchet derivatives with `Function.update`.

The consolidated result therefore derives all 12 smooth weak test identities
from classical coefficient derivative assumptions and genuine Fréchet
smoothness, without assuming the 12 test identities or the two kernel
Fréchet-directional formulas.

Caution: final physical coefficient fields are H², not necessarily C¹/C².
This is the smooth-approximant bridge, NOT the Sobolev approximation theorem.
The missing physical step is construction/convergence of the approximants,
followed by weak H² closure and Bochner reconstruction of Y and R.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalKernelDerivativeBridge

open MeasureTheory
open SeismicitySignedPhysicalThreeDimensionalKernel
open SeismicitySignedPhysicalKernelWeakIntegration

private abbrev Spatial3 := Fin 3 → ℝ

private theorem update_at_same_coordinate (x : Spatial3) (i : Fin 3) :
    Function.update x i (x i) = x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

private theorem direction_eq_single (i : Fin 3) :
    coordinateDirection3 i = Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateDirection3]
  · simp [coordinateDirection3, h]

/-- Frechet smoothness supplies the directional derivative *on the
coordinate section*. This is what makes the classical spatial formulas
usable in the multivariate integration-by-parts theorem. -/
theorem section3_fderiv_coordinate
    (f : Spatial3 → ℝ) (i : Fin 3) (x : Spatial3)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (section3 f i x)
      ((fderiv ℝ f x) (coordinateDirection3 i)) (x i) := by
  have hu : Function.update x i (x i) = x :=
    update_at_same_coordinate x i
  have hdiff : HasFDerivAt f (fderiv ℝ f x)
      (Function.update x i (x i)) := by
    rw [hu]
    exact hf.hasFDerivAt
  have hupdate : HasDerivAt (Function.update x i)
      (Pi.single i (1 : ℝ)) (x i) :=
    hasDerivAt_update x i (x i)
  have hc := hdiff.comp_hasDerivAt (x i) hupdate
  -- The composition theorem returns the *expanded* coordinate section.
  -- Unfold the named section in the goal first; do not ask `simpa` to
  -- identify two differently elaborated applications of HasDerivAt.
  change HasDerivAt (fun z : ℝ => f (Function.update x i z))
    ((fderiv ℝ f x) (coordinateDirection3 i)) (x i)
  rw [direction_eq_single]
  exact hc

/-- Classical 3D coefficient derivatives plus Frechet smoothness imply
all twelve integration-by-parts identities for the *actual smooth*
exponential kernel. The kernel direction-identification hypotheses of
`spatialKernel3_smooth_all_weak_test_identities` are eliminated. -/
theorem spatialKernel3_smooth_weak_test_from_sections
    (A b : Spatial3 → ℝ)
    (DA Db : Fin 3 → Spatial3 → ℝ)
    (DDA DDb : Fin 3 → Fin 3 → Spatial3 → ℝ)
    (φ : Spatial3 → ℝ) (Dφ : Fin 3 → Spatial3 → ℝ)
    (hA : ∀ i x, HasDerivAt (section3 A i x) (DA i x) (x i))
    (hb : ∀ i x, HasDerivAt (section3 b i x) (Db i x) (x i))
    (hDA : ∀ i j x, HasDerivAt (section3 (DA i) j x)
      (DDA i j x) (x j))
    (hDb : ∀ i j x, HasDerivAt (section3 (Db i) j x)
      (DDb i j x) (x j))
    (hKdiff : ∀ x, DifferentiableAt ℝ (spatialKernel3 A b) x)
    (hFirstDiff : ∀ i x,
      DifferentiableAt ℝ (spatialKernelFirst3 A b DA Db i) x)
    (hφdiff : ∀ x, DifferentiableAt ℝ φ x)
    (hφsection : ∀ i x, HasDerivAt (section3 φ i x)
      (Dφ i x) (x i))
    (hIntK : Integrable
      (fun x : Spatial3 => spatialKernel3 A b x * φ x) volume)
    (hIntKDir : ∀ i, Integrable (fun x : Spatial3 =>
      (fderiv ℝ (spatialKernel3 A b) x) (coordinateDirection3 i) * φ x)
      volume)
    (hIntKTest : ∀ i, Integrable (fun x : Spatial3 =>
      spatialKernel3 A b x * (fderiv ℝ φ x) (coordinateDirection3 i))
      volume)
    (hIntFirst : ∀ i, Integrable (fun x : Spatial3 =>
      spatialKernelFirst3 A b DA Db i x * φ x) volume)
    (hIntSecondDir : ∀ i j, Integrable (fun x : Spatial3 =>
      (fderiv ℝ (spatialKernelFirst3 A b DA Db i) x)
      (coordinateDirection3 j) * φ x) volume)
    (hIntFirstTest : ∀ i j, Integrable (fun x : Spatial3 =>
      spatialKernelFirst3 A b DA Db i x *
        (fderiv ℝ φ x) (coordinateDirection3 j)) volume) :
    (∀ i, (∫ x : Spatial3, spatialKernel3 A b x * Dφ i x) =
      -(∫ x : Spatial3, spatialKernelFirst3 A b DA Db i x * φ x)) ∧
    (∀ i j, (∫ x : Spatial3,
      spatialKernelFirst3 A b DA Db i x * Dφ j x) =
      -(∫ x : Spatial3,
        spatialKernelSecond3 A b DA Db DDA DDb i j x * φ x)) := by
  have hfirst := spatialKernel3_first_all A b DA Db hA hb
  have hsecond := spatialKernel3_second_all A b DA Db DDA DDb
    hA hb hDA hDb
  have hKdir : ∀ i x,
      (fderiv ℝ (spatialKernel3 A b) x) (coordinateDirection3 i) =
      spatialKernelFirst3 A b DA Db i x := by
    intro i x
    exact (section3_fderiv_coordinate _ i x (hKdiff x)).unique (hfirst i x)
  have hSecondDir : ∀ i j x,
      (fderiv ℝ (spatialKernelFirst3 A b DA Db i) x)
        (coordinateDirection3 j) =
        spatialKernelSecond3 A b DA Db DDA DDb i j x := by
    intro i j x
    exact (section3_fderiv_coordinate _ j x (hFirstDiff i x)).unique
      (hsecond i j x)
  have hTestDir : ∀ i x,
      (fderiv ℝ φ x) (coordinateDirection3 i) = Dφ i x := by
    intro i x
    exact (section3_fderiv_coordinate _ i x (hφdiff x)).unique
      (hφsection i x)
  exact spatialKernel3_smooth_all_weak_test_identities
    A b DA Db DDA DDb φ Dφ
    (fun x _ => hKdiff x)
    (fun i x _ => hFirstDiff i x)
    (fun x _ => hφdiff x)
    (fun i x _ => hφdiff x)
    hKdir hSecondDir hTestDir
    hIntK hIntKDir hIntKTest hIntFirst hIntSecondDir hIntFirstTest

#print axioms section3_fderiv_coordinate
#print axioms spatialKernel3_smooth_weak_test_from_sections

end SeismicitySignedPhysicalKernelDerivativeBridge
end ReservoirSeismicityControl
