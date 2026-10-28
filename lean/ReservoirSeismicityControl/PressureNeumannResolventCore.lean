import ReservoirSeismicityControl.PressureTensorOperatorBridge
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Block 70 — the coercive weak resolvent

This module applies Mathlib's Lax–Milgram theorem to the Hilbert form space.
It proves the variational identity, uniqueness, and symmetry of the resolvent
when the form is symmetric. This is a real step toward constructing the
Neumann operator, but NOT yet a self-adjoint Neumann realization on L²:
the physical H¹ domain, its dense embedding into L², and the corresponding
semigroup remain to be constructed.

No flux derivative assumptions appear here.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

/-- Weak inverse of a bounded, coercive bilinear form, represented in the
Hilbert form space by the Lax–Milgram equivalence. -/
noncomputable def pressureWeakFormSolve
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (f : V) : V :=
  (hB.continuousLinearEquivOfBilin).symm f

/-- The weak solution satisfies the defining variational identity. -/
theorem pressure_weak_form_solve_green
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (f v : V) :
    B (pressureWeakFormSolve B hB f) v =
      ⟪f, v⟫_ℝ := by
  calc
    B (pressureWeakFormSolve B hB f) v =
        ⟪hB.continuousLinearEquivOfBilin
            (pressureWeakFormSolve B hB f), v⟫_ℝ :=
      (hB.continuousLinearEquivOfBilin_apply _ v).symm
    _ = ⟪f, v⟫_ℝ := by
      simp [pressureWeakFormSolve]

/-- The weak solution is unique: no separate uniqueness assumption is used. -/
theorem pressure_weak_form_solve_unique
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (f u : V) (hu : ∀ v : V, B u v = ⟪f, v⟫_ℝ) :
    u = pressureWeakFormSolve B hB f := by
  have heq : f = hB.continuousLinearEquivOfBilin u :=
    hB.unique_continuousLinearEquivOfBilin (by
      intro v
      exact (hu v).symm)
  apply (hB.continuousLinearEquivOfBilin).injective
  calc
    hB.continuousLinearEquivOfBilin u = f := heq.symm
    _ = hB.continuousLinearEquivOfBilin
        (pressureWeakFormSolve B hB f) := by
      simp [pressureWeakFormSolve]

/-- Symmetry of the form implies symmetry of the associated weak inverse. -/
theorem pressure_weak_form_solve_symmetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hSym : ∀ u v : V, B u v = B v u)
    (f g : V) :
    ⟪f, pressureWeakFormSolve B hB g⟫_ℝ =
      ⟪pressureWeakFormSolve B hB f, g⟫_ℝ := by
  calc
    ⟪f, pressureWeakFormSolve B hB g⟫_ℝ =
        B (pressureWeakFormSolve B hB f)
          (pressureWeakFormSolve B hB g) :=
      (pressure_weak_form_solve_green B hB f _).symm
    _ = B (pressureWeakFormSolve B hB g)
          (pressureWeakFormSolve B hB f) := hSym _ _
    _ = ⟪g, pressureWeakFormSolve B hB f⟫_ℝ :=
      pressure_weak_form_solve_green B hB g _
    _ = ⟪pressureWeakFormSolve B hB f, g⟫_ℝ :=
      real_inner_comm _ _

end ReservoirSeismicityControl
