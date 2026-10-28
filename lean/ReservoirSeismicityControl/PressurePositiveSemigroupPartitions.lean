import ReservoirSeismicityControl.PressurePositiveSemigroupIncrements

/-!
# Weighted time partitions of a positive semigroup

The weighted finite-partition estimate for self-adjoint contraction
semigroups. No differentiability of the scalar weights is required.

The partition times `τ i` begin at zero, with increments `step i`.
The coefficients `q i` can have arbitrary signs and need only satisfy
`|q i| ≤ M`. The semigroup differences telescope to `I-S (τ n)`.

The theorem is about finite sums; it makes no claim yet that these
sums converge to the generator applied to a physical Duhamel integral.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace BigOperators

section Partition

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A finite telescoping sum of bounded semigroup operators. -/
theorem pressure_semigroup_partition_telescope
    (S : NNReal → H →L[ℝ] H)
    (τ : ℕ → NNReal) (n : ℕ) :
    (∑ i ∈ Finset.range n, (S (τ i) - S (τ (i + 1)))) =
      S (τ 0) - S (τ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- Uniform bound for an arbitrary signed step input on a finite
partition, independent of the partition mesh and of the number of steps.
The gain constant is exactly one. -/
theorem pressure_semigroup_partition_weighted_bound
    (S : NNReal → H →L[ℝ] H)
    (hSemigroup : ∀ s t : NNReal, S (s + t) = (S s) ∘L (S t))
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (hContract : ∀ (t : NNReal) (x : H), ‖S t x‖ ≤ ‖x‖)
    (hZero : S 0 = (1 : H →L[ℝ] H))
    (n : ℕ) (τ step : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + step i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M)
    (f : H) :
    ‖∑ i ∈ Finset.range n,
        q i • (S (τ i) - S (τ (i + 1))) f‖ ≤ M * ‖f‖ := by
  let B : ℕ → H →L[ℝ] H := fun i => S (τ i) - S (τ (i + 1))
  have hB : ∀ i ∈ Finset.range n, (B i).IsPositive := by
    intro i hi
    have hstep := hStep i (Finset.mem_range.mp hi)
    dsimp [B]
    rw [hstep]
    exact pressure_selfadjoint_contraction_semigroup_increment_positive
      S hSemigroup hSelf hContract (τ i) (step i)
  have hMass : ∀ x : H,
      (∑ i ∈ Finset.range n, ⟪B i x, x⟫_ℝ) ≤ ‖x‖ ^ 2 := by
    intro x
    have hSum :
        (∑ i ∈ Finset.range n, ⟪B i x, x⟫_ℝ) =
          ⟪(∑ i ∈ Finset.range n, B i) x, x⟫_ℝ := by
      simp only [ContinuousLinearMap.sum_apply, sum_inner]
    have hEnd := (pressure_selfadjoint_semigroup_positive
      S hSemigroup hSelf (τ n)).inner_nonneg_left x
    calc
      (∑ i ∈ Finset.range n, ⟪B i x, x⟫_ℝ) =
          ⟪(∑ i ∈ Finset.range n, B i) x, x⟫_ℝ := hSum
      _ = ⟪(S (τ 0) - S (τ n)) x, x⟫_ℝ := by
        rw [show (∑ i ∈ Finset.range n, B i) =
          S (τ 0) - S (τ n) from
            pressure_semigroup_partition_telescope S τ n]
      _ = ‖x‖ ^ 2 - ⟪S (τ n) x, x⟫_ℝ := by
        rw [hτ0, hZero]
        change ⟪x - S (τ n) x, x⟫_ℝ =
          ‖x‖ ^ 2 - ⟪S (τ n) x, x⟫_ℝ
        rw [inner_sub_left, real_inner_self_eq_norm_sq]
      _ ≤ ‖x‖ ^ 2 := sub_le_self _ hEnd
  simpa only [B] using
    (pressure_positive_operator_weighted_sum_bound
      (Finset.range n) B hB hMass q M hM
      (fun i hi => hq i (Finset.mem_range.mp hi)) f)

end Partition

end ReservoirSeismicityControl
