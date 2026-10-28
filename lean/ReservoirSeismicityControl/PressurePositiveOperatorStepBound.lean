import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorResolventRange
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Uniform bound for weighted sums of positive Hilbert-space operators

This is a compactness-free ingredient for Appendix A.1, (A5).
For positive operators B_i with sum bounded above by the identity
(in quadratic-form order), and scalar coefficients |q_i| ≤ M, we prove

    ‖∑ i, q_i • B_i f‖ ≤ M ‖f‖.

The proof uses the Rayleigh-quotient characterization of the norm of
symmetric operators. It does NOT assume an eigenbasis or spectral measure.

The intended next step is to instantiate B_i using increments of the
physical Neumann semigroup, and then pass from stepwise rates to the
Bochner/Duhamel integral. Those steps are NOT proved in this module.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace BigOperators

section AbstractPositiveStepBound

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A quadratic bound on a symmetric bounded operator gives the
same operator-norm bound. This is the Rayleigh-quotient theorem. -/
theorem pressure_symmetric_opNorm_le_of_quadratic
    (T : H →L[ℝ] H)
    (hSym : (T : H →ₗ[ℝ] H).IsSymmetric)
    (M : ℝ) (hM : 0 ≤ M)
    (hQuad : ∀ x : H, |⟪T x, x⟫_ℝ| ≤ M * ‖x‖ ^ 2) :
    ‖T‖ ≤ M := by
  rw [T.norm_eq_iSup_rayleighQuotient hSym]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.rayleighQuotient, hM]
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
    change |⟪T x, x⟫_ℝ / ‖x‖ ^ 2| ≤ M
    rw [abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact (div_le_iff₀ hsq).mpr (hQuad x)

/-- A finite positive-operator partition has the same sharp bound as a
scalar subprobability partition: coefficients bounded by M cannot amplify
any vector f by more than M. No commuting hypothesis is needed. -/
theorem pressure_positive_operator_weighted_sum_bound
    {ι : Type*} (s : Finset ι)
    (B : ι → H →L[ℝ] H)
    (hB : ∀ i ∈ s, (B i).IsPositive)
    (hMass : ∀ x : H,
      (∑ i ∈ s, ⟪B i x, x⟫_ℝ) ≤ ‖x‖ ^ 2)
    (q : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i ∈ s, |q i| ≤ M)
    (f : H) :
    ‖∑ i ∈ s, q i • B i f‖ ≤ M * ‖f‖ := by
  classical
  let T : H →L[ℝ] H := ∑ i ∈ s, q i • B i
  have hTapply (x : H) : T x = ∑ i ∈ s, q i • B i x := by
    simp [T]
  have hTinner (x y : H) :
      ⟪T x, y⟫_ℝ = ∑ i ∈ s, q i * ⟪B i x, y⟫_ℝ := by
    rw [hTapply]
    simp only [sum_inner, real_inner_smul_left]
  have hTinnerRight (x y : H) :
      ⟪x, T y⟫_ℝ = ∑ i ∈ s, q i * ⟪x, B i y⟫_ℝ := by
    rw [hTapply]
    simp only [inner_sum, real_inner_smul_right]
  have hSym : (T : H →ₗ[ℝ] H).IsSymmetric := by
    intro x y
    change ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ
    rw [hTinner, hTinnerRight]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hB i hi).inner_left_eq_inner_right x y]
  have hQuad (x : H) : |⟪T x, x⟫_ℝ| ≤ M * ‖x‖ ^ 2 := by
    rw [hTinner]
    calc
      |∑ i ∈ s, q i * ⟪B i x, x⟫_ℝ| ≤
          ∑ i ∈ s, |q i * ⟪B i x, x⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, |q i| * ⟪B i x, x⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg ((hB i hi).inner_nonneg_left x)]
      _ ≤ ∑ i ∈ s, M * ⟪B i x, x⟫_ℝ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hq i hi)
          ((hB i hi).inner_nonneg_left x)
      _ = M * ∑ i ∈ s, ⟪B i x, x⟫_ℝ := by
        rw [Finset.mul_sum]
      _ ≤ M * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hMass x) hM
  have hBound := pressure_symmetric_opNorm_le_of_quadratic
    T hSym M hM hQuad
  calc
    ‖∑ i ∈ s, q i • B i f‖ = ‖T f‖ := by rw [hTapply]
    _ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ ≤ M * ‖f‖ :=
      mul_le_mul_of_nonneg_right hBound (norm_nonneg f)

end AbstractPositiveStepBound

end ReservoirSeismicityControl
