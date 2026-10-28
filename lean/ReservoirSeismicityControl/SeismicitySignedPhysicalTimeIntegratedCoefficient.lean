import ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Subsequence
import Mathlib.Tactic

/-!
# M1: physical three-dimensional weak-H² time-integrated damping coefficient

The Duhamel multiplier depends on A(x,t,v) = ∫_{v}^{t} a(x,q) dq.
This module does **not** postulate weak H² derivatives of A: it constructs
all three first and nine second weak derivatives by Bochner integration of
the weak H² data of a, reusing the already verified integration-by-parts
identity from `SeismicitySignedPhysicalWeakH2Closure`.

The theorem works on the actual 3D Hilbert space L²(volume.restrict U).
It derives quantitative bounds linear in the elapsed interval `t-v`
from a uniform coefficient estimate and the mass of the causal measure.

There remains a genuine physical interface: the coefficient
`a(x,q)=γ₂(x,q) R*(x)` must be constructed as weak H² data from the
paper's spatial assumptions, the time maps must be strongly measurable,
and the canonical L² representative of the Bochner integral must be
identified with the pointwise coefficient primitive. The theorem does
not assume spatial derivatives of A, but it does require the coefficient
a to have genuine weak H² data and their time integrability.

Neither the nonlinear exponential composition nor the final H² bound of
R is asserted here. No `sorry`, `admit`, or custom `axiom` is used.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalTimeIntegratedCoefficient

open MeasureTheory
open scoped InnerProductSpace
open SeismicitySignedPhysicalWeakH2Closure
open SeismicitySignedPhysicalWeakH2Subsequence

/-- Build the actual L²-valued spatial weak-H² graph of the causal time
primitive from the coefficient's weak-H² graph; in particular the nine
Hessian components are *constructed* as time integrals and are not
postulated derivatives of the primitive. The volume measure is
restricted to an arbitrary 3D region `U` (eventually a Lipschitz U_j).

`ν` is intended to be Lebesgue measure restricted to `(v,t]`; the mass
hypothesis is separated to allow the physical causal measure from the
existing project without requiring an additional measure representation.
-/
theorem physicalThreeCoefficientPrimitiveWeakH2
    (U : Set (Fin 3 → ℝ)) {Φ : Type*}
    (testValue : Φ → PhysicalThreeL2 U)
    (D : Fin 3 → Φ → PhysicalThreeL2 U)
    (a : ℝ → PhysicalWeakH2Test U Φ testValue D)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (v t M0 M1 M2 : ℝ)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hmass : ν.real Set.univ ≤ t - v)
    (hvalue : Integrable (fun q => (a q).value) ν)
    (hfirst : ∀ i, Integrable (fun q => (a q).first i) ν)
    (hsecond : ∀ i j, Integrable (fun q => (a q).second i j) ν)
    (hbound0 : ∀ᵐ q ∂ν, ‖(a q).value‖ ≤ M0)
    (hbound1 : ∀ i, ∀ᵐ q ∂ν, ‖(a q).first i‖ ≤ M1)
    (hbound2 : ∀ i j, ∀ᵐ q ∂ν, ‖(a q).second i j‖ ≤ M2) :
    ∃ A : PhysicalWeakH2Test U Φ testValue D,
      A.value = ∫ q, (a q).value ∂ν ∧
      (∀ i, A.first i = ∫ q, (a q).first i ∂ν) ∧
      (∀ i j, A.second i j = ∫ q, (a q).second i j ∂ν) ∧
      ‖A.value‖ ≤ M0 * (t - v) ∧
      (∀ i, ‖A.first i‖ ≤ M1 * (t - v)) ∧
      (∀ i j, ‖A.second i j‖ ≤ M2 * (t - v)) := by
  let A : PhysicalWeakH2Test U Φ testValue D :=
    WeakH2Three.bochnerIntegral
      (fun φ : Φ => innerSL ℝ (testValue φ))
      (fun i φ => innerSL ℝ (D i φ))
      ν a hvalue hfirst hsecond
  refine ⟨A, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i j
    rfl
  · calc
      ‖A.value‖ = ‖∫ q, (a q).value ∂ν‖ := rfl
      _ ≤ M0 * ν.real Set.univ :=
        norm_integral_le_of_norm_le_const (μ := ν) hbound0
      _ ≤ M0 * (t - v) :=
        mul_le_mul_of_nonneg_left hmass hM0
  · intro i
    calc
      ‖A.first i‖ = ‖∫ q, (a q).first i ∂ν‖ := rfl
      _ ≤ M1 * ν.real Set.univ :=
        norm_integral_le_of_norm_le_const (μ := ν) (hbound1 i)
      _ ≤ M1 * (t - v) :=
        mul_le_mul_of_nonneg_left hmass hM1
  · intro i j
    calc
      ‖A.second i j‖ = ‖∫ q, (a q).second i j ∂ν‖ := rfl
      _ ≤ M2 * ν.real Set.univ :=
        norm_integral_le_of_norm_le_const (μ := ν) (hbound2 i j)
      _ ≤ M2 * (t - v) :=
        mul_le_mul_of_nonneg_left hmass hM2

-- Axiom report must contain only the normal kernel axioms after a
-- successful user-side build; there must be no `sorryAx`.
#print axioms physicalThreeCoefficientPrimitiveWeakH2

end SeismicitySignedPhysicalTimeIntegratedCoefficient
end ReservoirSeismicityControl
