import ReservoirSeismicityControl.PressureNeumannResolventCore
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Block 70 — transfer the coercive weak resolvent to L²

Let `V` denote the Hilbert space of form-domain functions (eventually the
Neumann H¹ space) and `H` the pivot Hilbert space (eventually L²).
Given a continuous embedding `j : V →L[ℝ] H` and a symmetric, continuous,
coercive form `B` on `V`, we construct its bounded weak resolvent on H:

    R = j ∘ B⁻¹ ∘ j*.

We prove its variational characterization, uniqueness, symmetry,
self-adjointness, and positivity. Under injectivity and density/separation
of `j`, the resolvent is also injective.

These are actual Hilbert-space results, but the *geometric* identification
`V = H¹(Ω)` for a bounded Lipschitz Ω, the differential Neumann
realization, and semigroup/Davies–Gaffney estimates remain open. The
form coercivity and continuity are explicit assumptions, not proved from
reservoir geometry in this module.

No bound on flux derivatives is introduced.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Solve `B(u,v) = ⟪f,jv⟫` in the Hilbert form domain V. -/
noncomputable def pressureHilbertWeakSolution
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : H →L[ℝ] V :=
  ((hB.continuousLinearEquivOfBilin).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.adjoint j)

/-- The pivot-space weak resolvent. It is bounded by construction. -/
noncomputable def pressureHilbertWeakResolvent
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : H →L[ℝ] H :=
  j.comp (pressureHilbertWeakSolution j B hB)

/-- The resolvent is exactly the inclusion of its weak solution. -/
theorem pressure_hilbert_resolvent_apply
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) :
    pressureHilbertWeakResolvent j B hB f =
      j (pressureHilbertWeakSolution j B hB f) := by
  rfl

/-- The defining variational identity comes from Lax–Milgram and adjunction,
not from an independently postulated Green identity. -/
theorem pressure_hilbert_weak_solution_green
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) (v : V) :
    B (pressureHilbertWeakSolution j B hB f) v = ⟪f, j v⟫_ℝ := by
  change B (pressureWeakFormSolve B hB ((ContinuousLinearMap.adjoint j) f)) v =
    ⟪f, j v⟫_ℝ
  calc
    B (pressureWeakFormSolve B hB ((ContinuousLinearMap.adjoint j) f)) v =
        ⟪(ContinuousLinearMap.adjoint j) f, v⟫_ℝ :=
      pressure_weak_form_solve_green B hB ((ContinuousLinearMap.adjoint j) f) v
    _ = ⟪f, j v⟫_ℝ := ContinuousLinearMap.adjoint_inner_left j v f

/-- A solution of the pivot-space variational problem is unique. -/
theorem pressure_hilbert_weak_solution_unique
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) (u : V)
    (hu : ∀ v : V, B u v = ⟪f, j v⟫_ℝ) :
    u = pressureHilbertWeakSolution j B hB f := by
  have hu' : ∀ v : V,
      B u v = ⟪(ContinuousLinearMap.adjoint j) f, v⟫_ℝ := by
    intro v
    rw [hu v]
    exact (ContinuousLinearMap.adjoint_inner_left j v f).symm
  change u = pressureWeakFormSolve B hB ((ContinuousLinearMap.adjoint j) f)
  exact pressure_weak_form_solve_unique B hB ((ContinuousLinearMap.adjoint j) f) u hu'

/-- Symmetry of the weak form implies symmetry of the bounded pivot-space
resolvent. -/
theorem pressure_hilbert_resolvent_symmetric
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hSym : ∀ u v : V, B u v = B v u)
    (f g : H) :
    ⟪pressureHilbertWeakResolvent j B hB f, g⟫_ℝ =
      ⟪f, pressureHilbertWeakResolvent j B hB g⟫_ℝ := by
  calc
    ⟪pressureHilbertWeakResolvent j B hB f, g⟫_ℝ =
        ⟪g, pressureHilbertWeakResolvent j B hB f⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪g, j (pressureHilbertWeakSolution j B hB f)⟫_ℝ := by
      rw [pressure_hilbert_resolvent_apply]
    _ = B (pressureHilbertWeakSolution j B hB g)
          (pressureHilbertWeakSolution j B hB f) :=
      (pressure_hilbert_weak_solution_green j B hB g _).symm
    _ = B (pressureHilbertWeakSolution j B hB f)
          (pressureHilbertWeakSolution j B hB g) := hSym _ _
    _ = ⟪f, j (pressureHilbertWeakSolution j B hB g)⟫_ℝ :=
      pressure_hilbert_weak_solution_green j B hB f _
    _ = ⟪f, pressureHilbertWeakResolvent j B hB g⟫_ℝ := by
      rw [pressure_hilbert_resolvent_apply]

/-- Self-adjointness is proved, rather than assumed, for the bounded resolvent. -/
theorem pressure_hilbert_resolvent_selfadjoint
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hSym : ∀ u v : V, B u v = B v u) :
    ContinuousLinearMap.adjoint (pressureHilbertWeakResolvent j B hB) =
      pressureHilbertWeakResolvent j B hB := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (pressureHilbertWeakResolvent j B hB)
    (pressureHilbertWeakResolvent j B hB)).2
  intro f g
  exact pressure_hilbert_resolvent_symmetric j B hB hSym f g

/-- Coercivity implies that the weak resolvent is positive semidefinite. -/
theorem pressure_hilbert_resolvent_nonneg
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) :
    0 ≤ ⟪pressureHilbertWeakResolvent j B hB f, f⟫_ℝ := by
  have hFormNonneg (v : V) : 0 ≤ B v v := by
    rcases hB with ⟨c, hc, hcoerc⟩
    have h0 : 0 ≤ c * ‖v‖ * ‖v‖ :=
      mul_nonneg (mul_nonneg (le_of_lt hc) (norm_nonneg v)) (norm_nonneg v)
    exact le_trans h0 (hcoerc v)
  rw [pressure_hilbert_resolvent_apply]
  calc
    0 ≤ B (pressureHilbertWeakSolution j B hB f)
          (pressureHilbertWeakSolution j B hB f) := hFormNonneg _
    _ = ⟪f, j (pressureHilbertWeakSolution j B hB f)⟫_ℝ :=
      pressure_hilbert_weak_solution_green j B hB f _
    _ = ⟪j (pressureHilbertWeakSolution j B hB f), f⟫_ℝ :=
      real_inner_comm _ _

/-- If the form-domain inclusion is injective and has separating (dense)
range, the weak resolvent is injective. These are precisely the standard
properties to establish for the actual H¹ to L² embedding. -/
theorem pressure_hilbert_resolvent_injective
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hjinj : Function.Injective j)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, j v⟫_ℝ = 0) → f = 0) :
    Function.Injective (pressureHilbertWeakResolvent j B hB) := by
  intro f g hfg
  have hzero : pressureHilbertWeakResolvent j B hB (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hu : pressureHilbertWeakSolution j B hB (f - g) = 0 := by
    apply hjinj
    change pressureHilbertWeakResolvent j B hB (f - g) = j (0 : V)
    simpa only [map_zero] using hzero
  apply sub_eq_zero.mp
  apply hsep (f - g)
  intro v
  calc
    ⟪f - g, j v⟫_ℝ =
        B (pressureHilbertWeakSolution j B hB (f - g)) v :=
      (pressure_hilbert_weak_solution_green j B hB (f - g) v).symm
    _ = 0 := by rw [hu]; simp

end ReservoirSeismicityControl
