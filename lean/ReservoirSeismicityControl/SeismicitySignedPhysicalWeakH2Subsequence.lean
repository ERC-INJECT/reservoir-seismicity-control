import ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Closure
import ReservoirSeismicityControl.SeismicitySignedSpatialWeakGradientIdentification
import Mathlib.Tactic

/-!
# M1: physical three-dimensional weak-H² compactness/identification interface

This is the next consolidated step after `SeismicitySignedPhysicalWeakH2Closure`.
Instead of imposing *strong* L² convergence of all mollified kernel Hessians,
we show that it is enough to converge strongly in L² for the scalar kernel,
and *weakly* for its three gradient and nine Hessian fields. Weak convergence
means testing against every element of the physical real Hilbert L² space.

The physical space is exactly L²(volume.restrict U) for a region
U ⊆ (Fin 3 → ℝ). The weak test functionals are genuine L² Hilbert
pairings with L² realizations of test functions and their coordinate
derivatives. An independent test space Φ is used: differentiation of
*arbitrary* L² functions would be mathematically invalid. Concrete
compactly supported smooth realizations are still to be constructed.

Crucially, uniform L² bounds pass to the weak limits. Consequently, the
Hessian bracket estimate in `SeismicitySignedPhysicalKernelHessian` can be
used with weak compactness; nonlinear strong convergence of the five terms
is not required for the weak-derivative *identification* step.

**Not yet discharged here:** physical bounded-Lipschitz C_c^∞ tests and
mollifier construction, extraction of weakly converging subsequences,
spatial H² product/composition for the actual exp(-A)b kernel, the
L² representative of the Duhamel integral, and uniform H² of actual R.
No `sorry`, `admit`, or new axioms.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalWeakH2Subsequence

open Filter MeasureTheory
open scoped InnerProductSpace
open SeismicitySignedPhysicalWeakH2Closure

section WeakHilbertLimit

variable {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Φ : Type*}

/-- A weak second-order graph limit needs only strong scalar convergence;
the gradients and Hessians converge weakly. No strong convergence of
quadratic-gradient cross terms is postulated. -/
noncomputable def weakH2ThreeOfWeakHilbertLimit
    (testValue : Φ → F) (testDerivative : Fin 3 → Φ → F)
    (approximants : ℕ →
      WeakH2Three
        (fun φ : Φ => innerSL ℝ (testValue φ))
        (fun i φ => innerSL ℝ (testDerivative i φ)))
    (v : F) (g : Fin 3 → F) (h : Fin 3 → Fin 3 → F)
    (hv : Tendsto (fun n => (approximants n).value) atTop (nhds v))
    (hg : ∀ i η, Tendsto
      (fun n => ⟪η, (approximants n).first i⟫_ℝ) atTop
      (nhds ⟪η, g i⟫_ℝ))
    (hh : ∀ i j η, Tendsto
      (fun n => ⟪η, (approximants n).second i j⟫_ℝ) atTop
      (nhds ⟪η, h i j⟫_ℝ)) :
    WeakH2Three
      (fun φ : Φ => innerSL ℝ (testValue φ))
      (fun i φ => innerSL ℝ (testDerivative i φ)) where
  value := v
  first := g
  second := h
  weak_first := by
    intro i φ
    change ⟪testDerivative i φ, v⟫_ℝ = -⟪testValue φ, g i⟫_ℝ
    have hleft : Tendsto
        (fun n => ⟪testDerivative i φ, (approximants n).value⟫_ℝ)
        atTop (nhds ⟪testDerivative i φ, v⟫_ℝ) := by
      have hc : Continuous (fun z : F => ⟪testDerivative i φ, z⟫_ℝ) := by
        fun_prop
      exact (hc.tendsto v).comp hv
    have hright : Tendsto
        (fun n => -⟪testValue φ, (approximants n).first i⟫_ℝ)
        atTop (nhds (-⟪testValue φ, g i⟫_ℝ)) := (hg i (testValue φ)).neg
    have hid :
        (fun n => ⟪testDerivative i φ, (approximants n).value⟫_ℝ) =
        (fun n => -⟪testValue φ, (approximants n).first i⟫_ℝ) := by
      funext n
      simpa only [innerSL_apply_apply] using
        (approximants n).weak_first i φ
    rw [hid] at hleft
    exact tendsto_nhds_unique hleft hright
  weak_second := by
    intro i j φ
    change ⟪testDerivative j φ, g i⟫_ℝ = -⟪testValue φ, h i j⟫_ℝ
    have hleft : Tendsto
        (fun n => ⟪testDerivative j φ, (approximants n).first i⟫_ℝ)
        atTop (nhds ⟪testDerivative j φ, g i⟫_ℝ) :=
      hg i (testDerivative j φ)
    have hright : Tendsto
        (fun n => -⟪testValue φ, (approximants n).second i j⟫_ℝ)
        atTop (nhds (-⟪testValue φ, h i j⟫_ℝ)) := (hh i j (testValue φ)).neg
    have hid :
        (fun n => ⟪testDerivative j φ, (approximants n).first i⟫_ℝ) =
        (fun n => -⟪testValue φ, (approximants n).second i j⟫_ℝ) := by
      funext n
      simpa only [innerSL_apply_apply] using
        (approximants n).weak_second i j φ
    rw [hid] at hleft
    exact tendsto_nhds_unique hleft hright

/-- Weak convergence preserves the quantitative L² estimates of every
first and second derivative. No strong Hessian convergence is needed. -/
theorem weakH2ThreeWeakLimitBounds
    (testValue : Φ → F) (testDerivative : Fin 3 → Φ → F)
    (approximants : ℕ →
      WeakH2Three
        (fun φ : Φ => innerSL ℝ (testValue φ))
        (fun i φ => innerSL ℝ (testDerivative i φ)))
    (g : Fin 3 → F) (h : Fin 3 → Fin 3 → F)
    (M₁ M₂ : ℝ)
    (hg : ∀ i η, Tendsto
      (fun n => ⟪η, (approximants n).first i⟫_ℝ) atTop
      (nhds ⟪η, g i⟫_ℝ))
    (hh : ∀ i j η, Tendsto
      (fun n => ⟪η, (approximants n).second i j⟫_ℝ) atTop
      (nhds ⟪η, h i j⟫_ℝ))
    (hgBound : ∀ i n, ‖(approximants n).first i‖ ≤ M₁)
    (hhBound : ∀ i j n, ‖(approximants n).second i j‖ ≤ M₂) :
    (∀ i, ‖g i‖ ≤ M₁) ∧ (∀ i j, ‖h i j‖ ≤ M₂) := by
  constructor
  · intro i
    exact sr_spatial_weak_gradient_norm_bound
      (fun n => (approximants n).first i) (g i) M₁
      (hg i) (hgBound i)
  · intro i j
    exact sr_spatial_weak_gradient_norm_bound
      (fun n => (approximants n).second i j) (h i j) M₂
      (hh i j) (hhBound i j)

end WeakHilbertLimit

/-- The genuinely physical scalar space: 3D Cartesian coordinates and
volume restricted to the near-well neighborhood U. -/
abbrev PhysicalThreeL2 (U : Set (Fin 3 → ℝ)) :=
  PhysicalL2Three U

/-- The test pairing is now concrete L² duality, not an arbitrary map.
`D` is the coordinate derivative of smooth tests, represented in L². -/
noncomputable abbrev PhysicalWeakH2Test
    (U : Set (Fin 3 → ℝ)) (Φ : Type*)
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U) :=
  WeakH2Three
    (fun φ : Φ => innerSL ℝ (testValue φ))
    (fun i φ => innerSL ℝ (D i φ))

/-- Physical 3D specialization of weak-H² graph closure, with all
coordinate first/Hessian bounds inherited from uniformly bounded smooth
approximants. Weak convergence is supplied by subsequence extraction,
which remains a separate genuine compactness obligation. -/
theorem physicalThreeDimensionalH2OfWeakMollifications
    (U : Set (Fin 3 → ℝ))
    {Φ : Type*} (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U)
    (approximants : ℕ → PhysicalWeakH2Test U Φ testValue D)
    (v : PhysicalThreeL2 U)
    (g : Fin 3 → PhysicalThreeL2 U)
    (h : Fin 3 → Fin 3 → PhysicalThreeL2 U)
    (M₁ M₂ : ℝ)
    (hv : Tendsto (fun n => (approximants n).value) atTop (nhds v))
    (hg : ∀ i η, Tendsto
      (fun n => ⟪η, (approximants n).first i⟫_ℝ) atTop
      (nhds ⟪η, g i⟫_ℝ))
    (hh : ∀ i j η, Tendsto
      (fun n => ⟪η, (approximants n).second i j⟫_ℝ) atTop
      (nhds ⟪η, h i j⟫_ℝ))
    (hgBound : ∀ i n, ‖(approximants n).first i‖ ≤ M₁)
    (hhBound : ∀ i j n, ‖(approximants n).second i j‖ ≤ M₂) :
    ∃ w : PhysicalWeakH2Test U Φ testValue D,
      w.value = v ∧ w.first = g ∧ w.second = h ∧
        (∀ i, ‖w.first i‖ ≤ M₁) ∧
        (∀ i j, ‖w.second i j‖ ≤ M₂) := by
  let w : PhysicalWeakH2Test U Φ testValue D :=
    weakH2ThreeOfWeakHilbertLimit testValue D approximants v g h hv hg hh
  obtain ⟨hG, hH⟩ :=
    weakH2ThreeWeakLimitBounds testValue D approximants g h M₁ M₂
      hg hh hgBound hhBound
  exact ⟨w, rfl, rfl, rfl, hG, hH⟩

-- These should all report only propext / Classical.choice / Quot.sound
-- following an actual successful user-side Lake build.
#print axioms weakH2ThreeOfWeakHilbertLimit
#print axioms weakH2ThreeWeakLimitBounds
#print axioms physicalThreeDimensionalH2OfWeakMollifications

end SeismicitySignedPhysicalWeakH2Subsequence
end ReservoirSeismicityControl
