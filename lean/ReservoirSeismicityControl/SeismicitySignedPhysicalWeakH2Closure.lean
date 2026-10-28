import Mathlib

/-!
# ReservoirSeismicityControl M1: weak 3D second derivatives and parameter integration

This file formalizes two *structural*, but useful, operations on weak spatial
H² data:

* strong L² limits of a smooth approximation sequence preserve both spatial
  integration-by-parts identities (three first derivatives, nine ordered second
  derivatives);
* Bochner integration of the value and derivative fields commutes with all
  these weak derivatives, on an arbitrary time measure and hence on a time
  interval.

The spatial dimensions are indexed by `Fin 3`. The ambient Banach space should
be instantiated with `Lp ℝ 2 (volume.restrict U)`. The `pair` and `testDeriv`
continuous linear functionals should be instantiated by L² pairings with a
compactly supported smooth test function and its coordinate derivatives.

The existence of such concrete test functionals, Sobolev mollifications, and
strong L² convergence of the five-term exponential Hessian formula are NOT
asserted here. In particular, this file alone does not close physical M1.

No proof holes or extra axioms are used.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalWeakH2Closure

open Filter MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {Test : Type*}

/-- A test function `φ` has an L² pairing with a spatial field, and each
`testDeriv i φ` is the pairing with the ith weak derivative of the test.
The concrete interpretation is `(pair φ) f = ∫_U f φ` and
`(testDeriv i φ) f = ∫_U f (∂ᵢφ)`.
The *derivative of the test* is not defined merely by this interface; it
must be supplied when specializing to compactly supported smooth tests. -/
structure WeakH2Three
    (pair : Test → F →L[ℝ] ℝ)
    (testDeriv : Fin 3 → Test → F →L[ℝ] ℝ) where
  value : F
  first : Fin 3 → F
  second : Fin 3 → Fin 3 → F
  weak_first : ∀ (i : Fin 3) (φ : Test),
    testDeriv i φ value = -pair φ (first i)
  weak_second : ∀ (i j : Fin 3) (φ : Test),
    testDeriv j φ (first i) = -pair φ (second i j)

section StrongLimit

variable [CompleteSpace F]
variable (pair : Test → F →L[ℝ] ℝ)
  (testDeriv : Fin 3 → Test → F →L[ℝ] ℝ)

/-- Closedness of three-dimensional first and second weak derivatives under
strong L² convergence of *all* fields. In the physical application the second
fields are exactly the five-term kernel Hessians, whose strong convergence
must follow from H² mollification and the 3D L⁶×L⁶→L² estimate. -/
def WeakH2Three.ofStrongLimit
    (approximants : ℕ → WeakH2Three pair testDeriv)
    (v : F) (g : Fin 3 → F) (h : Fin 3 → Fin 3 → F)
    (hv : Tendsto (fun n => (approximants n).value) atTop (nhds v))
    (hg : ∀ i, Tendsto (fun n => (approximants n).first i)
      atTop (nhds (g i)))
    (hh : ∀ i j, Tendsto (fun n => (approximants n).second i j)
      atTop (nhds (h i j))) :
    WeakH2Three pair testDeriv where
  value := v
  first := g
  second := h
  weak_first := by
    intro i φ
    have hleft :
        Tendsto (fun n => testDeriv i φ (approximants n).value)
          atTop (nhds (testDeriv i φ v)) :=
      ((testDeriv i φ).continuous.tendsto v).comp hv
    have hright :
        Tendsto (fun n => -pair φ ((approximants n).first i))
          atTop (nhds (-pair φ (g i))) :=
      (((pair φ).continuous.tendsto (g i)).comp (hg i)).neg
    have hid :
        (fun n => testDeriv i φ (approximants n).value) =
          (fun n => -pair φ ((approximants n).first i)) := by
      funext n
      exact (approximants n).weak_first i φ
    rw [hid] at hleft
    exact tendsto_nhds_unique hleft hright
  weak_second := by
    intro i j φ
    have hleft :
        Tendsto (fun n => testDeriv j φ ((approximants n).first i))
          atTop (nhds (testDeriv j φ (g i))) :=
      ((testDeriv j φ).continuous.tendsto (g i)).comp (hg i)
    have hright :
        Tendsto (fun n => -pair φ ((approximants n).second i j))
          atTop (nhds (-pair φ (h i j))) :=
      (((pair φ).continuous.tendsto (h i j)).comp (hh i j)).neg
    have hid :
        (fun n => testDeriv j φ ((approximants n).first i)) =
          (fun n => -pair φ ((approximants n).second i j)) := by
      funext n
      exact (approximants n).weak_second i j φ
    rw [hid] at hleft
    exact tendsto_nhds_unique hleft hright

end StrongLimit

section BochnerIntegral

variable [CompleteSpace F]
variable (pair : Test → F →L[ℝ] ℝ)
  (testDeriv : Fin 3 → Test → F →L[ℝ] ℝ)
variable {T : Type*} [MeasurableSpace T] (μ : Measure T)

/-- Weak differentiation under a Bochner integral. The hypotheses require
integrability of the value, every first field, and every second field: no
unjustified differentiation under a pointwise integral takes place. -/
noncomputable def WeakH2Three.bochnerIntegral
    (k : T → WeakH2Three pair testDeriv)
    (hvalue : Integrable (fun t => (k t).value) μ)
    (hfirst : ∀ i, Integrable (fun t => (k t).first i) μ)
    (hsecond : ∀ i j, Integrable (fun t => (k t).second i j) μ) :
    WeakH2Three pair testDeriv where
  value := ∫ t, (k t).value ∂μ
  first := fun i => ∫ t, (k t).first i ∂μ
  second := fun i j => ∫ t, (k t).second i j ∂μ
  weak_first := by
    intro i φ
    calc
      testDeriv i φ (∫ t, (k t).value ∂μ) =
          ∫ t, testDeriv i φ (k t).value ∂μ :=
        ((testDeriv i φ).integral_comp_comm hvalue).symm
      _ = ∫ t, -pair φ ((k t).first i) ∂μ := by
        congr 1
        funext t
        exact (k t).weak_first i φ
      _ = -(∫ t, pair φ ((k t).first i) ∂μ) := by
        rw [integral_neg]
      _ = -pair φ (∫ t, (k t).first i ∂μ) := by
        rw [(pair φ).integral_comp_comm (hfirst i)]
  weak_second := by
    intro i j φ
    calc
      testDeriv j φ (∫ t, (k t).first i ∂μ) =
          ∫ t, testDeriv j φ ((k t).first i) ∂μ :=
        ((testDeriv j φ).integral_comp_comm (hfirst i)).symm
      _ = ∫ t, -pair φ ((k t).second i j) ∂μ := by
        congr 1
        funext t
        exact (k t).weak_second i j φ
      _ = -(∫ t, pair φ ((k t).second i j) ∂μ) := by
        rw [integral_neg]
      _ = -pair φ (∫ t, (k t).second i j ∂μ) := by
        rw [(pair φ).integral_comp_comm (hsecond i j)]

end BochnerIntegral

/-- The physical spatial base: three Cartesian coordinates, restricted to an
arbitrary region U. For a bounded Lipschitz U this is the ambient L² in the
usual weak-Sobolev definition. -/
abbrev PhysicalL2Three (U : Set (Fin 3 → ℝ)) : Type :=
  MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict U)

-- Standard axioms check: expected `propext`, `Classical.choice`, `Quot.sound`.
#print axioms WeakH2Three.ofStrongLimit
#print axioms WeakH2Three.bochnerIntegral

end SeismicitySignedPhysicalWeakH2Closure
end ReservoirSeismicityControl
