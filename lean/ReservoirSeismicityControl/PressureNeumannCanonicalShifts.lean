import ReservoirSeismicityControl.PressureNeumannAllShifts

/-!
# Block 70 — one canonical family of shifted Neumann forms

The previous module verified the Lax–Milgram results for a supplied `BLam`
with the identity `BLam x y = lam * ⟪j x,j y⟫ + E x y`.
This file constructs that form from the unit shifted form itself:

  BLam := lam • B₁ + (1 - lam) • E.

It then derives the coercive resolvent family, its common unbounded graph,
contractivity at every positive shift, and the resolvent identity.
No independent shifted-form identity/coercivity assumption is used.

This is a precise Hille–Yosida *input*, NOT a construction of a semigroup.
The physical H¹(V) realization and the differentiated off-diagonal bounds
still require formalization. No Q derivative assumptions are introduced.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Shift the weak Neumann bilinear form without supplying a new form. -/
noncomputable def pressureNeumannCanonicalShiftForm
    (lam : ℝ) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  lam • B₁ + (1 - lam) • E

/-- The canonical shift has exactly the desired weak-energy expression. -/
theorem pressure_neumann_canonical_shift_formula
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (x y : V) :
    pressureNeumannCanonicalShiftForm lam B₁ E x y =
      lam * ⟪j x, j y⟫_ℝ + E x y := by
  simp only [pressureNeumannCanonicalShiftForm,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hForm₁ x y]
  ring

/-- Coercivity of all shifts follows from the single, physical unit form. -/
theorem pressure_neumann_canonical_shift_coercive
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) :
    IsCoercive (pressureNeumannCanonicalShiftForm lam B₁ E) := by
  exact pressure_neumann_shifted_form_coercive lam j B₁
    (pressureNeumannCanonicalShiftForm lam B₁ E) E
    hB₁ hForm₁
    (pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁)
    hE hLam

/-- Canonical positive-shift weak resolvent (not a postulated family). -/
noncomputable def pressureNeumannCanonicalResolvent
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) : H →L[ℝ] H :=
  pressureHilbertWeakResolvent j
    (pressureNeumannCanonicalShiftForm lam B₁ E)
    (pressure_neumann_canonical_shift_coercive lam j B₁ E hB₁ hForm₁ hE hLam)

/-- The canonical resolvent solves the SAME unbounded graph equation. -/
theorem pressure_neumann_canonical_resolvent_graph
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (f : H) :
    (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam f,
      f - lam • pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam f) ∈
      pressureNeumannResolventGraph (pressureHilbertWeakResolvent j B₁ hB₁) := by
  exact pressure_neumann_shifted_resolvent_same_graph lam j B₁
    (pressureNeumannCanonicalShiftForm lam B₁ E) E
    hB₁ hForm₁
    (pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁)
    hE hLam f

/-- Every canonical positive-shift resolvent has the sharp contraction rate. -/
theorem pressure_neumann_canonical_resolvent_bound
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam) (f : H) :
    lam * ‖pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam f‖
      ≤ ‖f‖ := by
  exact pressure_neumann_shifted_resolvent_contract lam j B₁
    (pressureNeumannCanonicalShiftForm lam B₁ E) E
    hB₁ hForm₁
    (pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁)
    hE hLam f

/-- The canonical resolvent family satisfies its resolvent identity, without
an independent consistency assumption for its various shifts. -/
theorem pressure_neumann_canonical_resolvent_identity
    (lam mu : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hLam : 0 < lam) (hMu : 0 < mu) (f : H) :
    pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam f -
        pressureNeumannCanonicalResolvent mu j B₁ E hB₁ hForm₁ hE hMu f =
      (mu - lam) • pressureNeumannCanonicalResolvent mu j B₁ E
        hB₁ hForm₁ hE hMu
        (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam f) := by
  exact pressure_neumann_shifted_resolvent_identity lam mu j B₁
    (pressureNeumannCanonicalShiftForm lam B₁ E)
    (pressureNeumannCanonicalShiftForm mu B₁ E) E
    hB₁ hForm₁
    (pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁)
    (pressure_neumann_canonical_shift_formula mu j B₁ E hForm₁)
    hE hLam hMu f

end ReservoirSeismicityControl
