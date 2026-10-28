import ReservoirSeismicityControl.SeismicitySignedPhysicalThreeDimensionalKernel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1 — genuine three-dimensional weak test identities for smooth kernels

For each smooth approximation of the *actual* exponential Duhamel kernel
  K = exp(-A) b,
we derive the 3 first and 9 ordered second integration-by-parts relations
on R³ using the multivariate Haar-measure integration-by-parts theorem.
The derivative candidates are the exact five-term expressions already
constructed in `SeismicitySignedPhysicalThreeDimensionalKernel`.

This removes the need to POSTULATE the weak-test identities for smooth
approximants, and the test derivative is the ACTUAL Frechet derivative
in the corresponding coordinate direction.

Scope: the hypotheses state classical Frechet differentiability of smooth
approximants, the identification of their directional derivatives with the
explicit kernel expressions, and integrability of products with test fields.
These are genuine prerequisites, not conclusions about nonsmooth physical
coefficients. Passing to L²(U_j) weak limits, obtaining the approximants
from the physical H² assumptions, and the final uniform H² bound on R
remain to be proved. This theorem does not assert M1 is complete.

No sorry, admit, or extra axioms.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalKernelWeakIntegration

open MeasureTheory
open SeismicitySignedPhysicalThreeDimensionalKernel

private abbrev Spatial3 := Fin 3 → ℝ

/-- Coordinate vector in Cartesian 3-space. -/
noncomputable def coordinateDirection3 (i : Fin 3) : Spatial3 :=
  fun j => if j = i then 1 else 0

/-- Genuine weak integration by parts for a smooth field and test function,
with their identified spatial directional derivatives. This invokes the
multivariate integration-by-parts theorem in R³, rather than assuming the
pairing identity as a hypothesis. -/
private theorem smoothDirectionalWeakIdentity3
    (f φ Df Dφ : Spatial3 → ℝ) (e : Spatial3)
    (hf : ∀ x ∈ tsupport φ, DifferentiableAt ℝ f x)
    (hφ : ∀ x ∈ tsupport f, DifferentiableAt ℝ φ x)
    (hDf : ∀ x, (fderiv ℝ f x) e = Df x)
    (hDφ : ∀ x, (fderiv ℝ φ x) e = Dφ x)
    (hDfφ : Integrable
      (fun x : Spatial3 => (fderiv ℝ f x) e * φ x) volume)
    (hfDφ : Integrable
      (fun x : Spatial3 => f x * (fderiv ℝ φ x) e) volume)
    (hfφ : Integrable (fun x : Spatial3 => f x * φ x) volume) :
    (∫ x : Spatial3, f x * Dφ x) =
      -(∫ x : Spatial3, Df x * φ x) := by
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Spatial3)) (f := f) (g := φ)
    (v := e) hDfφ hfDφ hfφ hf hφ
  calc
    (∫ x : Spatial3, f x * Dφ x) =
        (∫ x : Spatial3, f x * (fderiv ℝ φ x) e) := by
          simp_rw [hDφ]
    _ = -(∫ x : Spatial3, (fderiv ℝ f x) e * φ x) := hIBP
    _ = -(∫ x : Spatial3, Df x * φ x) := by
          simp_rw [hDf]

/-- For the *actual* smooth 3D exponential Duhamel kernel, all 12
weak test identities follow directly from its Frechet derivatives,
without assuming any of those identities. The second derivatives use the
complete five-term physical expression, including `(∂ᵢA)(∂ⱼA)b`.

The hypotheses are checked on the smooth approximants, prior to the
weak-limit construction. In particular no C² or W¹,∞ condition is imposed
on the final physical coefficients. -/
theorem spatialKernel3_smooth_all_weak_test_identities
    (A b : Spatial3 → ℝ)
    (DA Db : Fin 3 → Spatial3 → ℝ)
    (DDA DDb : Fin 3 → Fin 3 → Spatial3 → ℝ)
    (φ : Spatial3 → ℝ) (Dφ : Fin 3 → Spatial3 → ℝ)
    (hKdiff : ∀ x ∈ tsupport φ,
      DifferentiableAt ℝ (spatialKernel3 A b) x)
    (hKfirstDiff : ∀ i, ∀ x ∈ tsupport φ,
      DifferentiableAt ℝ (spatialKernelFirst3 A b DA Db i) x)
    (hφKdiff : ∀ x ∈ tsupport (spatialKernel3 A b),
      DifferentiableAt ℝ φ x)
    (hφFirstDiff : ∀ i, ∀ x ∈ tsupport (spatialKernelFirst3 A b DA Db i),
      DifferentiableAt ℝ φ x)
    (hKdir : ∀ i x, (fderiv ℝ (spatialKernel3 A b) x)
      (coordinateDirection3 i) = spatialKernelFirst3 A b DA Db i x)
    (hKsecondDir : ∀ i j x,
      (fderiv ℝ (spatialKernelFirst3 A b DA Db i) x)
        (coordinateDirection3 j) =
          spatialKernelSecond3 A b DA Db DDA DDb i j x)
    (hφDir : ∀ i x, (fderiv ℝ φ x) (coordinateDirection3 i) = Dφ i x)
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
  constructor
  · intro i
    exact smoothDirectionalWeakIdentity3
      (spatialKernel3 A b) φ
      (spatialKernelFirst3 A b DA Db i) (Dφ i)
      (coordinateDirection3 i)
      hKdiff hφKdiff (hKdir i) (hφDir i)
      (hIntKDir i) (hIntKTest i) hIntK
  · intro i j
    exact smoothDirectionalWeakIdentity3
      (spatialKernelFirst3 A b DA Db i) φ
      (spatialKernelSecond3 A b DA Db DDA DDb i j) (Dφ j)
      (coordinateDirection3 j)
      (hKfirstDiff i) (hφFirstDiff i) (hKsecondDir i j)
      (hφDir j) (hIntSecondDir i j) (hIntFirstTest i j)
      (hIntFirst i)

#print axioms spatialKernel3_smooth_all_weak_test_identities

end SeismicitySignedPhysicalKernelWeakIntegration
end ReservoirSeismicityControl
