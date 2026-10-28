import ReservoirSeismicityControl.PressureNeumannUnboundedGraph
import Mathlib

/-!
# Block 70 — maximal accretivity certificate for the weak Neumann graph

We use the *constructed* Lax–Milgram resolvent and its closed graph.
There is no standalone hypothesis postulating a semigroup or an estimate on Q̇.

This module proves:
* the graph is stable under subtraction;
* the range of an injective symmetric resolvent is separating (hence dense);
* nonnegativity of the graph forces the unit resolvent to be contractive;
* the energy form supplies graph monotonicity for the physical weak resolvent;
* shift solvability + contraction + range separation are assembled for the
  constructed Hilbert-form operator.

The physical Sobolev realization, its generated semigroup, and Davies–Gaffney
estimates still require separate proofs. These results do NOT claim them.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The resolvent graph is a real linear relation, in particular closed under subtraction. -/
theorem pressure_neumann_resolvent_graph_sub
    (R : H →L[ℝ] H) (u f v g : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph R)
    (hv : (v, g) ∈ pressureNeumannResolventGraph R) :
    (u - v, f - g) ∈ pressureNeumannResolventGraph R := by
  change R (u + f) = u at hu
  change R (v + g) = v at hv
  change R ((u - v) + (f - g)) = u - v
  calc
    R ((u - v) + (f - g)) = R ((u + f) - (v + g)) := by
      congr 1
      abel
    _ = R (u + f) - R (v + g) := map_sub R _ _
    _ = u - v := by rw [hu, hv]

/-- The range of an injective symmetric Hilbert-space resolvent has trivial
orthogonal complement. This is the separating characterization of density. -/
theorem pressure_neumann_resolvent_range_separating
    (R : H →L[ℝ] H)
    (hRsym : ∀ x y : H, ⟪R x, y⟫_ℝ = ⟪x, R y⟫_ℝ)
    (hinj : Function.Injective R)
    (z : H) (hz : ∀ x : H, ⟪z, R x⟫_ℝ = 0) : z = 0 := by
  have hinner : ⟪R z, R z⟫_ℝ = 0 := by
    calc
      ⟪R z, R z⟫_ℝ = ⟪z, R (R z)⟫_ℝ := hRsym z (R z)
      _ = 0 := hz (R z)
  have hn : ‖R z‖ ^ 2 = 0 := by
    rw [real_inner_self_eq_norm_sq] at hinner
    exact hinner
  have hRz : R z = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (R z)]
  apply hinj
  simpa only [map_zero] using hRz

/-- Positivity of the unbounded graph implies a norm-one bound on the
unit resolvent. This is the contraction estimate needed for semigroup
and evolution arguments, not an assumption about the semigroup. -/
theorem pressure_neumann_graph_resolvent_contract
    (R : H →L[ℝ] H)
    (hpos : ∀ u f : H,
      (u, f) ∈ pressureNeumannResolventGraph R → 0 ≤ ⟪f, u⟫_ℝ)
    (h : H) : ‖R h‖ ≤ ‖h‖ := by
  have hgraph : (R h, h - R h) ∈ pressureNeumannResolventGraph R :=
    pressure_neumann_resolvent_graph_surjective_shift R h
  have hnonneg : 0 ≤ ⟪h - R h, R h⟫_ℝ := hpos _ _ hgraph
  have hsq : ‖R h‖ ^ 2 ≤ ⟪h, R h⟫_ℝ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hnonneg
    linarith
  have hcs : ⟪h, R h⟫_ℝ ≤ ‖h‖ * ‖R h‖ :=
    real_inner_le_norm h (R h)
  by_cases hz : ‖R h‖ = 0
  · rw [hz]
    exact norm_nonneg h
  · have hp : 0 < ‖R h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    by_contra hnot
    have hlt : ‖h‖ < ‖R h‖ := lt_of_not_ge hnot
    have hprod : 0 < (‖R h‖ - ‖h‖) * ‖R h‖ :=
      mul_pos (sub_pos.mpr hlt) hp
    nlinarith

/-- The weak energy form supplies monotonicity of the operator, by applying
its established nonnegative Green identity to differences of graph elements. -/
theorem pressure_hilbert_neumann_graph_monotone
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H) (B E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hShift : ∀ x y : V, B x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (u f v g : H)
    (hu : (u, f) ∈ pressureNeumannResolventGraph
      (pressureHilbertWeakResolvent j B hB))
    (hv : (v, g) ∈ pressureNeumannResolventGraph
      (pressureHilbertWeakResolvent j B hB)) :
    0 ≤ ⟪f - g, u - v⟫_ℝ := by
  have hdiff := pressure_neumann_resolvent_graph_sub
    (pressureHilbertWeakResolvent j B hB) u f v g hu hv
  exact pressure_hilbert_neumann_graph_nonneg
    j B E hB hShift hE (u - v) (f - g) hdiff

/-- The actual Lax–Milgram weak resolvent is a contraction when the
shifted form is `inner + E` and the diffusion energy is nonnegative. -/
theorem pressure_hilbert_neumann_resolvent_contract
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H) (B E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hShift : ∀ x y : V, B x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (f : H) :
    ‖pressureHilbertWeakResolvent j B hB f‖ ≤ ‖f‖ := by
  apply pressure_neumann_graph_resolvent_contract
    (pressureHilbertWeakResolvent j B hB)
  intro u g hug
  exact pressure_hilbert_neumann_graph_nonneg
    j B E hB hShift hE u g hug

/-- The range of the *constructed* weak resolvent is separating when the
form inclusion is injective and dense in the orthogonality sense. -/
theorem pressure_hilbert_neumann_resolvent_range_separating
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hSym : ∀ x y : V, B x y = B y x)
    (hjinj : Function.Injective j)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, j v⟫_ℝ = 0) → f = 0)
    (z : H)
    (hz : ∀ x : H, ⟪z, pressureHilbertWeakResolvent j B hB x⟫_ℝ = 0) :
    z = 0 := by
  exact pressure_neumann_resolvent_range_separating
    (pressureHilbertWeakResolvent j B hB)
    (pressure_hilbert_resolvent_symmetric j B hB hSym)
    (pressure_hilbert_resolvent_injective j B hB hjinj hsep) z hz

/-- One combined maximal-accretivity certificate for the constructed
Neumann graph: nonnegative graph, surjective unit shift, contractive
resolvent, and a separating operator domain. -/
theorem pressure_hilbert_neumann_maximal_accretive_certificate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (j : V →L[ℝ] H) (B E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B)
    (hShift : ∀ x y : V, B x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym : ∀ x y : V, B x y = B y x)
    (hjinj : Function.Injective j)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, j v⟫_ℝ = 0) → f = 0) :
    (∀ u f : H,
      (u, f) ∈ pressureNeumannResolventGraph
        (pressureHilbertWeakResolvent j B hB) → 0 ≤ ⟪f, u⟫_ℝ) ∧
    (∀ f : H, (pressureHilbertWeakResolvent j B hB f,
      f - pressureHilbertWeakResolvent j B hB f) ∈
        pressureNeumannResolventGraph
          (pressureHilbertWeakResolvent j B hB)) ∧
    (∀ f : H, ‖pressureHilbertWeakResolvent j B hB f‖ ≤ ‖f‖) ∧
    (∀ z : H, (∀ x : H,
      ⟪z, pressureHilbertWeakResolvent j B hB x⟫_ℝ = 0) → z = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u f hu
    exact pressure_hilbert_neumann_graph_nonneg j B E hB hShift hE u f hu
  · intro f
    exact pressure_neumann_resolvent_graph_surjective_shift
      (pressureHilbertWeakResolvent j B hB) f
  · intro f
    exact pressure_hilbert_neumann_resolvent_contract j B E hB hShift hE f
  · intro z hz
    exact pressure_hilbert_neumann_resolvent_range_separating
      j B hB hSym hjinj hsep z hz

end ReservoirSeismicityControl
