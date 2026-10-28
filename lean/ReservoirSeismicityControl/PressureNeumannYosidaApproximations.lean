import ReservoirSeismicityControl.PressureNeumannCanonicalShifts
import Mathlib

/-!
# Block 70 — higher resolvent bounds and bounded Yosida approximants

This module uses the *canonical*, verified Lax–Milgram family of shifts of ONE
symmetric, nonnegative weak Neumann energy form. It proves the all-powers
Hille–Yosida norm bound and the dissipativity/contraction estimates of a
bounded Yosida approximation.

The results do not construct a C₀ semigroup. Such a construction requires a
semigroup-generation theorem (and, for the reservoir, the Sobolev H¹ → L²
realization) which is not provided by the results imported here.

No assumptions on derivatives of the well flux Q are used.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The rescaled canonical resolvent is a contraction on H. -/
theorem pressure_neumann_scaled_resolvent_contract
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (f : H) :
    ‖(lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam) f‖
      ≤ ‖f‖ := by
  have h := pressure_neumann_canonical_resolvent_bound
    lam j B₁ E hB₁ hForm₁ hE hLam f
  simpa only [ContinuousLinearMap.smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos hLam] using h

/-- All powers of the rescaled resolvent act contractively. This is the
all-powers (rather than just first-power) Hille–Yosida estimate. -/
theorem pressure_neumann_scaled_resolvent_powers_contract
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam)
    (n : ℕ) (f : H) :
    ‖((lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam) ^ n) f‖
      ≤ ‖f‖ := by
  let T : H →L[ℝ] H :=
    lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam
  have hT : ∀ x : H, ‖T x‖ ≤ ‖x‖ := by
    intro x
    exact pressure_neumann_scaled_resolvent_contract
      lam j B₁ E hB₁ hForm₁ hE hLam x
  change ‖(T ^ n) f‖ ≤ ‖f‖
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    calc
      ‖(T ^ (n + 1)) f‖ = ‖(T ^ n) (T f)‖ := by
        rw [pow_succ, ContinuousLinearMap.mul_apply]
      _ ≤ ‖T f‖ := ih (T f)
      _ ≤ ‖f‖ := hT f

/-- Operator-norm form of the bound on every resolvent power. -/
theorem pressure_neumann_scaled_resolvent_powers_opNorm
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam)
    (n : ℕ) :
    ‖((lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam) ^ n)‖
      ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul] using
    pressure_neumann_scaled_resolvent_powers_contract
      lam j B₁ E hB₁ hForm₁ hE hLam n f

/-- Bounded approximation of the nonnegative Neumann operator A, with
`R_lam = (lam I + A)⁻¹`. The associated generator approximation is its
negative `-A_lam`. -/
noncomputable def pressureNeumannYosidaApprox
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) :
    H →L[ℝ] H :=
  lam • ((1 : H →L[ℝ] H) -
    lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam)

/-- The bounded approximation A_lam is accretive. This uses only the
rescaled resolvent contraction, not a semigroup or an unbounded-domain lemma. -/
theorem pressure_neumann_yosida_accretive
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam)
    (f : H) :
    0 ≤ ⟪pressureNeumannYosidaApprox lam j B₁ E hB₁ hForm₁ hE hLam f, f⟫_ℝ := by
  let T : H →L[ℝ] H :=
    lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam
  have hT : ‖T f‖ ≤ ‖f‖ :=
    pressure_neumann_scaled_resolvent_contract
      lam j B₁ E hB₁ hForm₁ hE hLam f
  have hprod : ‖T f‖ * ‖f‖ ≤ ‖f‖ ^ 2 := by
    calc
      ‖T f‖ * ‖f‖ ≤ ‖f‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg f)
      _ = ‖f‖ ^ 2 := by ring
  have hinner : ⟪T f, f⟫_ℝ ≤ ‖f‖ ^ 2 :=
    (real_inner_le_norm (T f) f).trans hprod
  have hdiff : 0 ≤ ⟪f - T f, f⟫_ℝ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  change 0 ≤ ⟪lam • (f - T f), f⟫_ℝ
  rw [real_inner_smul_left]
  exact mul_nonneg (le_of_lt hLam) hdiff

/-- The bounded approximation has the explicit operator norm bound
`‖A_lam‖ ≤ 2 lam`; it is a genuine bounded operator for each lam. -/
theorem pressure_neumann_yosida_opNorm
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) :
    ‖pressureNeumannYosidaApprox lam j B₁ E hB₁ hForm₁ hE hLam‖
      ≤ 2 * lam := by
  have hNonneg : 0 ≤ 2 * lam := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hNonneg
  intro f
  let T : H →L[ℝ] H :=
    lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam
  have hT : ‖T f‖ ≤ ‖f‖ :=
    pressure_neumann_scaled_resolvent_contract
      lam j B₁ E hB₁ hForm₁ hE hLam f
  have hsub : ‖f - T f‖ ≤ ‖f‖ + ‖T f‖ := norm_sub_le f (T f)
  change ‖lam • (f - T f)‖ ≤ (2 * lam) * ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLam]
  calc
    lam * ‖f - T f‖ ≤ lam * (‖f‖ + ‖T f‖) :=
      mul_le_mul_of_nonneg_left hsub (le_of_lt hLam)
    _ ≤ lam * (‖f‖ + ‖f‖) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hT ‖f‖) (le_of_lt hLam)
    _ = (2 * lam) * ‖f‖ := by ring

end ReservoirSeismicityControl
