import ReservoirSeismicityControl.PressureNeumannL2TensorMultiplier
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Block 70: the physical A3 tensor supplies the L² multiplier norm bound

A symmetric positive coefficient whose quadratic form is bounded by M times
squared Hilbert norm has operator norm at most M. Apply this fact to the
three-dimensional permeability tensor and obtain a *physical* vector-L²
multiplication operator with the norm bound following from A3.

Measurability of the nine physical tensor entries is required, as for any
Bochner-L² multiplier. No additional independent operator-norm hypothesis
is made. This file does not yet establish the physical distributional
H¹ gradient or the integrated ellipticity inequality of the multiplier.
No well-flux time derivatives are assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

section QuadraticBound

/-- For symmetric nonnegative real Hilbert-space operators, an upper quadratic
bound controls the operator norm. -/
theorem pressure_neumann_positive_symmetric_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : E →L[ℝ] E) (M : ℝ) (hM : 0 ≤ M)
    (hSym : C.IsSymmetric)
    (hNonneg : ∀ z : E, 0 ≤ ⟪C z, z⟫_ℝ)
    (hUpper : ∀ z : E, ⟪C z, z⟫_ℝ ≤ M * ‖z‖ ^ 2) :
    ‖C‖ ≤ M := by
  rw [C.norm_eq_iSup_rayleighQuotient hSym]
  refine ciSup_le fun z => ?_
  by_cases hz : z = 0
  · subst z
    simpa [ContinuousLinearMap.rayleighQuotient] using hM
  have hsq : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hq : C.rayleighQuotient z = ⟪C z, z⟫_ℝ / ‖z‖ ^ 2 := by
    simp [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [hq, abs_of_nonneg (div_nonneg (hNonneg z) hsq.le)]
  exact (div_le_iff₀ hsq).2 (hUpper z)

end QuadraticBound

section A3PhysicalBound

/-- Assumption A3 gives the pointwise operator-norm upper bound directly.
The lower ellipticity bound is used to guarantee positivity of the
quadratic form. There is no independent norm-bound assumption. -/
theorem pressure_neumann_physical_pointwise_opNorm_le_of_A3
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (g : Fin 3 → ℝ),
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (hKHi : ∀ x (g : Fin 3 → ℝ),
      (∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j) ≤
        kM * (∑ i : Fin 3, (g i) ^ 2))
    (x : Ω) :
    ‖pressureNeumannPhysicalPointwiseCLM k eta beta x‖ ≤
      kM / (beta * etam) := by
  let C := pressureNeumannPhysicalPointwiseCLM k eta beta x
  have hM : 0 ≤ kM / (beta * etam) :=
    div_nonneg hkM (le_of_lt (mul_pos hbeta hetam))
  have hSym : C.IsSymmetric := by
    intro z w
    exact pressure_neumann_physical_pointwise_symmetric
      k eta beta x (hKSym x) z w
  have hUpper : ∀ z : EuclideanSpace ℝ (Fin 3),
      ⟪C z, z⟫_ℝ ≤ (kM / (beta * etam)) * ‖z‖ ^ 2 := by
    intro z
    have h := pressure_neumann_physical_pointwise_upper
      k eta beta kM etam hbeta hkM hetam x (hEtaLo x)
      (hKHi x) (WithLp.ofLp z)
    simpa only [C, WithLp.toLp_ofLp, PiLp.toLp_apply,
      EuclideanSpace.real_norm_sq_eq] using h
  have hNonneg : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ ⟪C z, z⟫_ℝ := by
    intro z
    have hEtaM : 0 < etaM :=
      lt_of_lt_of_le hetam ((hEtaLo x).trans (hEtaHi x))
    have hCoeff : 0 ≤ km / (beta * etaM) :=
      le_of_lt (div_pos hkm (mul_pos hbeta hEtaM))
    have h := pressure_neumann_physical_pointwise_lower
      k eta beta km etam etaM hbeta hkm hetam x
      (hEtaLo x) (hEtaHi x) (hKLo x) (WithLp.ofLp z)
    have hlo : (km / (beta * etaM)) * ‖z‖ ^ 2 ≤ ⟪C z, z⟫_ℝ := by
      simpa only [C, WithLp.toLp_ofLp, PiLp.toLp_apply,
        EuclideanSpace.real_norm_sq_eq] using h
    exact (mul_nonneg hCoeff (sq_nonneg _)).trans hlo
  exact pressure_neumann_positive_symmetric_opNorm_le
    C (kM / (beta * etam)) hM hSym hNonneg hUpper

/-- The measurable physical tensor from A3 defines a bounded operator on
vector-valued L². All pointwise bounds follow from the tensor assumptions. -/
noncomputable def pressureNeumannPhysicalL2MultiplierOfA3
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (g : Fin 3 → ℝ),
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (hKHi : ∀ x (g : Fin 3 → ℝ),
      (∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j) ≤
        kM * (∑ i : Fin 3, (g i) ^ 2))
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    Lp (EuclideanSpace ℝ (Fin 3)) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin 3)) 2 μ :=
  pressureNeumannPhysicalL2TensorMultiplier μ k eta beta hTensor
    (kM / (beta * etam))
    (div_nonneg hkM (le_of_lt (mul_pos hbeta hetam)))
    (Filter.Eventually.of_forall
      (pressure_neumann_physical_pointwise_opNorm_le_of_A3
        k eta beta km kM etam etaM hbeta hkm hkM hetam
        hEtaLo hEtaHi hKSym hKLo hKHi))

end A3PhysicalBound

end ReservoirSeismicityControl
