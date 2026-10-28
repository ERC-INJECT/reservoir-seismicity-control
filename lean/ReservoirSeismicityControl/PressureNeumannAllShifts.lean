import ReservoirSeismicityControl.PressureNeumannMaximalAccretive
import Mathlib

/-!
# Block 70 — the full positive resolvent family of the weak Neumann operator

The unit shifted form B₁ = inner(j·, j·) + E is already known to be coercive.
For each lam > 0, this module considers a bounded form
  BLam(x,y) = lam * inner(jx,jy) + E(x,y).
It proves coercivity of BLam from that of B₁ and E >= 0, with no new
coercivity assumption. The corresponding Lax–Milgram resolvents satisfy:

* lam ‖RLam f‖ <= ‖f‖;
* RLam f belongs to the SAME unbounded graph constructed using R₁;
* RLam - RMu = (mu - lam) RMu RLam.

The forms BLam and their identities with the physical energy are arguments.
Their realization on the concrete reservoir H¹ domain is not formalized here.
No generator theorem, semigroup, or off-diagonal estimate is assumed or proved.
No derivative of any applied well flux is used.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- All positive shifts are coercive once the unit shift is coercive and
    the energy E is nonnegative. In particular there is NO separate
    coercivity hypothesis at each lam. -/
theorem pressure_neumann_shifted_form_coercive
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ BLam E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hFormLam : ∀ x y : V, BLam x y = lam * ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hLam : 0 < lam) : IsCoercive BLam := by
  rcases hB₁ with ⟨c, hc, hcoerc⟩
  rcases le_total lam 1 with hle | hge
  · refine ⟨lam * c, mul_pos hLam hc, ?_⟩
    intro x
    have hb : c * ‖x‖ * ‖x‖ ≤ ⟪j x, j x⟫_ℝ + E x x := by
      calc
        c * ‖x‖ * ‖x‖ ≤ B₁ x x := hcoerc x
        _ = ⟪j x, j x⟫_ℝ + E x x := hForm₁ x x
    calc
      (lam * c) * ‖x‖ * ‖x‖ = lam * (c * ‖x‖ * ‖x‖) := by ring
      _ ≤ lam * (⟪j x, j x⟫_ℝ + E x x) :=
        mul_le_mul_of_nonneg_left hb (le_of_lt hLam)
      _ ≤ lam * ⟪j x, j x⟫_ℝ + E x x := by
        have hh := mul_nonneg (sub_nonneg.mpr hle) (hE x)
        nlinarith
      _ = BLam x x := (hFormLam x x).symm
  · refine ⟨c, hc, ?_⟩
    intro x
    have hp : 0 ≤ ⟪j x, j x⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
      positivity
    calc
      c * ‖x‖ * ‖x‖ ≤ B₁ x x := hcoerc x
      _ = ⟪j x, j x⟫_ℝ + E x x := hForm₁ x x
      _ ≤ lam * ⟪j x, j x⟫_ℝ + E x x := by
        have hh := mul_nonneg (sub_nonneg.mpr hge) hp
        nlinarith
      _ = BLam x x := (hFormLam x x).symm

/-- The lam-resolvent satisfies its weak equation by construction. -/
theorem pressure_neumann_shifted_resolvent_green
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ BLam E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hFormLam : ∀ x y : V, BLam x y = lam * ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam)
    (f : H) (v : V) :
    BLam (pressureHilbertWeakSolution j BLam
      (pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam) f) v =
      ⟪f, j v⟫_ℝ := by
  exact pressure_hilbert_weak_solution_green j BLam _ f v

/-- The Lax–Milgram solution at lam lies in the same unbounded operator graph
    defined by the unit resolvent R₁. -/
theorem pressure_neumann_shifted_resolvent_same_graph
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ BLam E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hFormLam : ∀ x y : V, BLam x y = lam * ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (f : H) :
    let RLam := pressureHilbertWeakResolvent j BLam
      (pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam)
    (RLam f, f - lam • RLam f) ∈
      pressureNeumannResolventGraph (pressureHilbertWeakResolvent j B₁ hB₁) := by
  let hBLam : IsCoercive BLam :=
    pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam
  let x : V := pressureHilbertWeakSolution j BLam hBLam f
  let u : H := j x
  have hgreen (v : V) : BLam x v = ⟪f, j v⟫_ℝ :=
    pressure_hilbert_weak_solution_green j BLam hBLam f v
  have hweak (v : V) : B₁ x v = ⟪u + (f - lam • u), j v⟫_ℝ := by
    calc
      B₁ x v = (1 - lam) * ⟪j x, j v⟫_ℝ + BLam x v := by
        rw [hForm₁ x v, hFormLam x v]
        ring
      _ = (1 - lam) * ⟪u, j v⟫_ℝ + ⟪f, j v⟫_ℝ := by
        rw [hgreen]
      _ = ⟪u + (f - lam • u), j v⟫_ℝ := by
        rw [inner_add_left, inner_sub_left, real_inner_smul_left]
        ring
  have hx : x = pressureHilbertWeakSolution j B₁ hB₁
      (u + (f - lam • u)) :=
    pressure_hilbert_weak_solution_unique j B₁ hB₁
      (u + (f - lam • u)) x hweak
  have hunit : pressureHilbertWeakResolvent j B₁ hB₁
      (u + (f - lam • u)) = u := by
    rw [pressure_hilbert_resolvent_apply, ← hx]
  change pressureHilbertWeakResolvent j B₁ hB₁
    (pressureHilbertWeakResolvent j BLam hBLam f +
      (f - lam • pressureHilbertWeakResolvent j BLam hBLam f)) =
      pressureHilbertWeakResolvent j BLam hBLam f
  exact hunit

/-- Resolvent contractivity for every positive shift. This is the
    Hille–Yosida bound at the n = 1 level; higher powers follow from
    the operator-norm bound once the family is bundled. -/
theorem pressure_neumann_shifted_resolvent_contract
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ BLam E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hFormLam : ∀ x y : V, BLam x y = lam * ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (f : H) :
    let RLam := pressureHilbertWeakResolvent j BLam
      (pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam)
    lam * ‖RLam f‖ ≤ ‖f‖ := by
  let hBLam : IsCoercive BLam :=
    pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam
  let x : V := pressureHilbertWeakSolution j BLam hBLam f
  let u : H := j x
  have hgreen : BLam x x = ⟪f, u⟫_ℝ :=
    pressure_hilbert_weak_solution_green j BLam hBLam f x
  have henergy : lam * ⟪u, u⟫_ℝ ≤ ⟪f, u⟫_ℝ := by
    calc
      lam * ⟪u, u⟫_ℝ ≤ lam * ⟪u, u⟫_ℝ + E x x :=
        le_add_of_nonneg_right (hE x)
      _ = BLam x x := (hFormLam x x).symm
      _ = ⟪f, u⟫_ℝ := hgreen
  have hbound : lam * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ := by
    calc
      lam * ‖u‖ ^ 2 = lam * ⟪u, u⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      _ ≤ ⟪f, u⟫_ℝ := henergy
      _ ≤ ‖f‖ * ‖u‖ := real_inner_le_norm f u
  have hnorm : lam * ‖u‖ ≤ ‖f‖ := by
    by_cases hz : ‖u‖ = 0
    · simp [hz, norm_nonneg]
    · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz)
      have hh : (lam * ‖u‖) * ‖u‖ ≤ ‖f‖ * ‖u‖ := by nlinarith
      by_contra hnot
      have hgt : ‖f‖ < lam * ‖u‖ := lt_of_not_ge hnot
      have hprod : 0 < (lam * ‖u‖ - ‖f‖) * ‖u‖ :=
        mul_pos (sub_pos.mpr hgt) hp
      nlinarith
  change lam * ‖pressureHilbertWeakResolvent j BLam hBLam f‖ ≤ ‖f‖
  rw [pressure_hilbert_resolvent_apply]
  exact hnorm

/-- Resolvent identity for two positive shifts, proved at the variational
    level. The two resolvents correspond to the SAME energy E. -/
theorem pressure_neumann_shifted_resolvent_identity
    (lam mu : ℝ) (j : V →L[ℝ] H) (B₁ BLam BMu E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hFormLam : ∀ x y : V, BLam x y = lam * ⟪j x, j y⟫_ℝ + E x y)
    (hFormMu : ∀ x y : V, BMu x y = mu * ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (hMu : 0 < mu) (f : H) :
    let RLam := pressureHilbertWeakResolvent j BLam
      (pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam)
    let RMu := pressureHilbertWeakResolvent j BMu
      (pressure_neumann_shifted_form_coercive mu j B₁ BMu E hB₁ hForm₁ hFormMu hE hMu)
    RLam f - RMu f = (mu - lam) • RMu (RLam f) := by
  let hBLam : IsCoercive BLam :=
    pressure_neumann_shifted_form_coercive lam j B₁ BLam E hB₁ hForm₁ hFormLam hE hLam
  let hBMu : IsCoercive BMu :=
    pressure_neumann_shifted_form_coercive mu j B₁ BMu E hB₁ hForm₁ hFormMu hE hMu
  let RLam := pressureHilbertWeakResolvent j BLam hBLam
  let RMu := pressureHilbertWeakResolvent j BMu hBMu
  let x : V := pressureHilbertWeakSolution j BLam hBLam f
  have hgreen (v : V) : BLam x v = ⟪f, j v⟫_ℝ :=
    pressure_hilbert_weak_solution_green j BLam hBLam f v
  have hweak (v : V) : BMu x v = ⟪f + (mu - lam) • RLam f, j v⟫_ℝ := by
    calc
      BMu x v = (mu - lam) * ⟪j x, j v⟫_ℝ + BLam x v := by
        rw [hFormLam x v, hFormMu x v]
        ring
      _ = (mu - lam) * ⟪RLam f, j v⟫_ℝ + ⟪f, j v⟫_ℝ := by
        rw [hgreen]
        rfl
      _ = ⟪f + (mu - lam) • RLam f, j v⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left]
        ring
  have hx : x = pressureHilbertWeakSolution j BMu hBMu
      (f + (mu - lam) • RLam f) :=
    pressure_hilbert_weak_solution_unique j BMu hBMu
      (f + (mu - lam) • RLam f) x hweak
  have hresolve : RMu (f + (mu - lam) • RLam f) = RLam f := by
    change j (pressureHilbertWeakSolution j BMu hBMu
      (f + (mu - lam) • RLam f)) = j x
    exact congrArg j hx.symm
  change RLam f - RMu f = (mu - lam) • RMu (RLam f)
  calc
    RLam f - RMu f = RMu (f + (mu - lam) • RLam f) - RMu f := by rw [hresolve]
    _ = (mu - lam) • RMu (RLam f) := by
      rw [map_add, map_smul]
      abel

end ReservoirSeismicityControl
