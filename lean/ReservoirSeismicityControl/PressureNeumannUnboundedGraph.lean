import ReservoirSeismicityControl.PressureNeumannHilbertResolvent
import Mathlib

/-!
# Block 70 — the closed, maximal symmetric operator graph associated with the weak resolvent

For a bounded Hilbert-space resolvent `R`, the shifted unbounded operator
is represented by its graph `(u,Au)` satisfying `R (u+Au) = u`.

We prove:
* the graph is closed and closed under addition and real scaling
* the shifted equation `u+Au=h` is solvable for every `h`
* when `R` is injective, `Au` is unique
* when `R` is symmetric, the graph is symmetric and maximally symmetric in
  the Hilbert graph-adjoint sense
* for the Lax–Milgram resolvent, the graph gives the weak diffusion equation
  whenever `B = inner + E` is the shifted energy form
* if `E` is nonnegative then so is the unbounded operator.

This is a *Hilbert-form* theorem. It does not instantiate the reservoir
Sobolev space, produce a Neumann heat semigroup, or prove off-diagonal bounds.
It assumes no derivative bound on Q.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Graph of the operator `A = R⁻¹ - I` on `range R`, without pretending
that the unbounded operator acts continuously on all of H. -/
def pressureNeumannResolventGraph (R : H →L[ℝ] H) : Set (H × H) :=
  {p | R (p.1 + p.2) = p.1}

/-- The graph of the unbounded operator is a closed subset of H × H. -/
theorem pressure_neumann_resolvent_graph_closed
    (R : H →L[ℝ] H) : IsClosed (pressureNeumannResolventGraph R) := by
  change IsClosed {p : H × H | R (p.1 + p.2) = p.1}
  exact isClosed_eq
    (R.continuous.comp (continuous_fst.add continuous_snd))
    continuous_fst

/-- Zero belongs to the resolvent graph. -/
theorem pressure_neumann_resolvent_graph_zero
    (R : H →L[ℝ] H) :
    ((0 : H), (0 : H)) ∈ pressureNeumannResolventGraph R := by
  change R (0 + 0) = (0 : H)
  simp

/-- The graph is closed under addition. -/
theorem pressure_neumann_resolvent_graph_add
    (R : H →L[ℝ] H) (u f v g : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph R)
    (hv : (v, g) ∈ pressureNeumannResolventGraph R) :
    (u + v, f + g) ∈ pressureNeumannResolventGraph R := by
  change R (u + f) = u at hu
  change R (v + g) = v at hv
  change R ((u + v) + (f + g)) = u + v
  calc
    R ((u + v) + (f + g)) = R ((u + f) + (v + g)) := by
      congr 1
      abel
    _ = R (u + f) + R (v + g) := map_add R _ _
    _ = u + v := by rw [hu, hv]

/-- The graph is closed under real scalar multiplication. -/
theorem pressure_neumann_resolvent_graph_smul
    (R : H →L[ℝ] H) (a : ℝ) (u f : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph R) :
    (a • u, a • f) ∈ pressureNeumannResolventGraph R := by
  change R (u + f) = u at hu
  change R (a • u + a • f) = a • u
  rw [← smul_add, map_smul, hu]

/-- Every right-hand side has a solution of `(I+A)u=h`. -/
theorem pressure_neumann_resolvent_graph_surjective_shift
    (R : H →L[ℝ] H) (h : H) :
    (R h, h - R h) ∈ pressureNeumannResolventGraph R := by
  change R (R h + (h - R h)) = R h
  congr 1
  abel

/-- The domain of the operator is exactly the range of its resolvent. -/
theorem pressure_neumann_resolvent_graph_domain_iff
    (R : H →L[ℝ] H) (u : H) :
    (∃ f : H, (u, f) ∈ pressureNeumannResolventGraph R) ↔
      ∃ h : H, R h = u := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨u + f, hf⟩
  · rintro ⟨h, hh⟩
    refine ⟨h - u, ?_⟩
    change R (u + (h - u)) = u
    calc
      R (u + (h - u)) = R h := by congr 1; abel
      _ = u := hh

/-- Injectivity of the resolvent makes the output of the unbounded operator
unique on its (generally proper) domain. -/
theorem pressure_neumann_resolvent_graph_unique
    (R : H →L[ℝ] H) (hRinj : Function.Injective R)
    (u f g : H)
    (hf : (u, f) ∈ pressureNeumannResolventGraph R)
    (hg : (u, g) ∈ pressureNeumannResolventGraph R) : f = g := by
  change R (u + f) = u at hf
  change R (u + g) = u at hg
  exact add_left_cancel (hRinj (hf.trans hg.symm))

/-- A symmetric resolvent yields a symmetric unbounded operator graph. -/
theorem pressure_neumann_resolvent_graph_symmetric
    (R : H →L[ℝ] H)
    (hRsym : ∀ x y : H, ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ)
    (u f v g : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph R)
    (hv : (v, g) ∈ pressureNeumannResolventGraph R) :
    ⟪f, v⟫_ℝ = ⟪u, g⟫_ℝ := by
  change R (u + f) = u at hu
  change R (v + g) = v at hv
  calc
    ⟪f, v⟫_ℝ = ⟪u + f, v⟫_ℝ - ⟪u, v⟫_ℝ := by
      rw [inner_add_left]
      ring
    _ = ⟪u + f, R (v + g)⟫_ℝ - ⟪u, v⟫_ℝ := by rw [hv]
    _ = ⟪R (u + f), v + g⟫_ℝ - ⟪u, v⟫_ℝ := by
      rw [(hRsym (u + f) (v + g)).symm]
    _ = ⟪u, v + g⟫_ℝ - ⟪u, v⟫_ℝ := by rw [hu]
    _ = ⟪u, g⟫_ℝ := by
      rw [inner_add_right]
      ring

/-- Converse of graph symmetry (graph-adjoint criterion): if `(u,f)`
is paired symmetrically with every graph element, then it belongs to
that graph. This is the maximal-symmetry component of self-adjointness. -/
theorem pressure_neumann_resolvent_graph_adjoint_mem
    (R : H →L[ℝ] H)
    (hRsym : ∀ x y : H, ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ)
    (u f : H)
    (hAdj : ∀ v g : H, (v, g) ∈ pressureNeumannResolventGraph R →
      ⟪f, v⟫_ℝ = ⟪u, g⟫_ℝ) :
    (u, f) ∈ pressureNeumannResolventGraph R := by
  have hpair (h : H) : ⟪f, R h⟫_ℝ = ⟪u, h - R h⟫_ℝ :=
    hAdj (R h) (h - R h) (pressure_neumann_resolvent_graph_surjective_shift R h)
  have hinner (h : H) : ⟪R (u + f), h⟫_ℝ = ⟪u, h⟫_ℝ := by
    calc
      ⟪R (u + f), h⟫_ℝ = ⟪u + f, R h⟫_ℝ := hRsym (u + f) h
      _ = ⟪u, R h⟫_ℝ + ⟪f, R h⟫_ℝ := inner_add_left _ _ _
      _ = ⟪u, R h⟫_ℝ + ⟪u, h - R h⟫_ℝ := by rw [hpair]
      _ = ⟪u, h⟫_ℝ := by rw [inner_sub_right]; ring
  have hz : ⟪R (u + f) - u, R (u + f) - u⟫_ℝ = 0 := by
    rw [inner_sub_left, hinner]
    ring
  have hzero : R (u + f) - u = 0 := inner_self_eq_zero.mp hz
  exact sub_eq_zero.mp hzero

/-- The unbounded graph attached to the Lax–Milgram resolvent satisfies
both halves of the Hilbert graph-adjoint characterization. -/
theorem pressure_hilbert_neumann_graph_adjoint_iff
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hSym : ∀ a b : V, B a b = B b a)
    (u f : H) :
    (u, f) ∈ pressureNeumannResolventGraph
      (pressureHilbertWeakResolvent j B hB) ↔
    ∀ v g : H,
      (v, g) ∈ pressureNeumannResolventGraph
        (pressureHilbertWeakResolvent j B hB) →
      ⟪f, v⟫_ℝ = ⟪u, g⟫_ℝ := by
  constructor
  · intro huf v g hvg
    exact pressure_neumann_resolvent_graph_symmetric
      (pressureHilbertWeakResolvent j B hB)
      (pressure_hilbert_resolvent_symmetric j B hB hSym)
      u f v g huf hvg
  · exact pressure_neumann_resolvent_graph_adjoint_mem
      (pressureHilbertWeakResolvent j B hB)
      (pressure_hilbert_resolvent_symmetric j B hB hSym) u f

/-- The graph equation agrees with the actual weak equation: if the
coercive shifted form B is `inner + E`, its weak resolvent graph has
`E(x,v) = ⟪Au,jv⟫`, with `u=jx`.

The identification of E with the reservoir gradient integral is supplied
separately by the tensor-energy files; it is not proved for H¹ here. -/
theorem pressure_hilbert_neumann_graph_green
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H)
    (B E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hShift : ∀ x y : V, B x y = ⟪j x, j y⟫_ℝ + E x y)
    (u f : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph
      (pressureHilbertWeakResolvent j B hB))
    (v : V) :
    E (pressureHilbertWeakSolution j B hB (u + f)) v =
      ⟪f, j v⟫_ℝ := by
  let x := pressureHilbertWeakSolution j B hB (u + f)
  have hx : j x = u := by
    change pressureHilbertWeakResolvent j B hB (u + f) = u at hu
    simpa only [pressure_hilbert_resolvent_apply] using hu
  have hb : B x v = ⟪u + f, j v⟫_ℝ :=
    pressure_hilbert_weak_solution_green j B hB (u + f) v
  calc
    E x v = B x v - ⟪j x, j v⟫_ℝ := by rw [hShift x v]; ring
    _ = ⟪u + f, j v⟫_ℝ - ⟪u, j v⟫_ℝ := by rw [hb, hx]
    _ = ⟪f, j v⟫_ℝ := by rw [inner_add_left]; ring

/-- The realized diffusion operator is nonnegative if its energy form
is nonnegative. -/
theorem pressure_hilbert_neumann_graph_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H)
    (B E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hShift : ∀ x y : V, B x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (u f : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph
      (pressureHilbertWeakResolvent j B hB)) :
    0 ≤ ⟪f, u⟫_ℝ := by
  let x := pressureHilbertWeakSolution j B hB (u + f)
  have hx : j x = u := by
    change pressureHilbertWeakResolvent j B hB (u + f) = u at hu
    simpa only [pressure_hilbert_resolvent_apply] using hu
  calc
    0 ≤ E x x := hE x
    _ = ⟪f, j x⟫_ℝ := pressure_hilbert_neumann_graph_green
      j B E hB hShift u f hu x
    _ = ⟪f, u⟫_ℝ := by rw [hx]

end ReservoirSeismicityControl
