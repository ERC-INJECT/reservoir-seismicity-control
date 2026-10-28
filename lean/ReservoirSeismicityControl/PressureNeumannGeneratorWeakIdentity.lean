import ReservoirSeismicityControl.PressureNeumannDenseSemigroup

/-!
# Block 70 — the generator is exactly the weak Neumann operator

The previous files construct a C₀ contraction semigroup from the canonical
Lax–Milgram resolvents. This module closes an important identification:
its generator L is the NEGATIVE of the operator A defined by the weak
Neumann energy identity E(x,v) = ⟪Au,jv⟫.

Both directions are proved, with no independent generator-identification or
Green-identity hypotheses. The form Hilbert space V and embedding j are
still abstract: realization as the physical H¹(Ω) to L²(Ω) embedding and
Davies–Gaffney bounds are separate tasks.

No assumptions on derivatives of well fluxes Q are used.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace
open MarkovProcess.Semigroup

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def oneShift : PositiveShift := ⟨1, by norm_num⟩

/-- For any generated contraction semigroup, the unit resolvent graph is
exactly the graph of the negative generator. This is a genuine equivalence,
not merely containment of one graph in the other. -/
theorem pressure_neumann_generator_graph_of_unit
    (C : ContractiveResolvent H) (R : H →L[ℝ] H)
    (hUnit : C.operator oneShift = R) (u f : H) :
    (u, f) ∈ pressureNeumannResolventGraph R ↔
      ∃ hu : u ∈ C.generatedSemigroup.generatorDomain,
        C.generatedSemigroup.generator ⟨u, hu⟩ = -f := by
  constructor
  · intro hgraph
    change R (u + f) = u at hgraph
    have hR : C.operator oneShift (u + f) = u := by
      rw [hUnit]
      exact hgraph
    have hu : u ∈ C.generatedSemigroup.generatorDomain := by
      rw [← hR]
      exact C.operator_mem_generatorDomain oneShift (u + f)
    refine ⟨hu, ?_⟩
    calc
      C.generatedSemigroup.generator ⟨u, hu⟩ =
          (oneShift : ℝ) • u - (u + f) :=
        C.generator_apply_of_operator_eq oneShift hu hR
      _ = -f := by simp [oneShift]
  · rintro ⟨hu, hgen⟩
    have hR := C.operator_smul_sub_generator oneShift ⟨u, hu⟩
    change C.operator oneShift
      ((oneShift : ℝ) • u - C.generatedSemigroup.generator ⟨u, hu⟩) = u at hR
    rw [hgen] at hR
    simp only [oneShift, one_smul, sub_neg_eq_add] at hR
    change R (u + f) = u
    rw [← hUnit]
    exact hR

/-- At shift 1, the canonical shifted weak form is the original unit
form, and its bounded resolvent is exactly the original Lax–Milgram
resolvent. The proofs of coercivity do not affect this equality. -/
theorem pressure_neumann_dense_unit_resolvent_eq
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    (pressureNeumannContractiveResolvent j B₁ E hB₁ hForm₁ hE
      (fun lam hLam => pressure_neumann_canonical_denseRange lam j B₁ E
        hB₁ hForm₁ hE hSym₁ hjinj hjDense hLam)).operator oneShift =
      pressureHilbertWeakResolvent j B₁ hB₁ := by
  change pressureNeumannCanonicalResolvent 1 j B₁ E hB₁ hForm₁ hE
    (by norm_num) = pressureHilbertWeakResolvent j B₁ hB₁
  -- Avoid rewriting the form under an argument whose coercivity certificate
  -- depends on that form.  Instead compare weak solutions by uniqueness.
  unfold pressureNeumannCanonicalResolvent
  apply ContinuousLinearMap.ext
  intro f
  let hShift : IsCoercive (pressureNeumannCanonicalShiftForm 1 B₁ E) :=
    pressure_neumann_canonical_shift_coercive 1 j B₁ E hB₁ hForm₁ hE (by norm_num)
  let x : V :=
    pressureHilbertWeakSolution j (pressureNeumannCanonicalShiftForm 1 B₁ E) hShift f
  have hUnitGreen : ∀ v : V, B₁ x v = ⟪f, j v⟫_ℝ := by
    intro v
    calc
      B₁ x v = ⟪j x, j v⟫_ℝ + E x v := hForm₁ x v
      _ = (pressureNeumannCanonicalShiftForm 1 B₁ E) x v := by
        simpa only [one_mul] using
          (pressure_neumann_canonical_shift_formula 1 j B₁ E hForm₁ x v).symm
      _ = ⟪f, j v⟫_ℝ :=
        pressure_hilbert_weak_solution_green j
          (pressureNeumannCanonicalShiftForm 1 B₁ E) hShift f v
  have hx : x = pressureHilbertWeakSolution j B₁ hB₁ f :=
    pressure_hilbert_weak_solution_unique j B₁ hB₁ f x hUnitGreen
  change j x = j (pressureHilbertWeakSolution j B₁ hB₁ f)
  exact congrArg j hx

/-- For the Neumann semigroup constructed from a dense form embedding,
its unbounded graph is exactly the negative generator graph. -/
theorem pressure_neumann_dense_generated_graph_iff
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (u f : H) :
    (u, f) ∈ pressureNeumannResolventGraph (pressureHilbertWeakResolvent j B₁ hB₁) ↔
      ∃ hu : u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain,
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator ⟨u, hu⟩ = -f := by
  let C : ContractiveResolvent H :=
    pressureNeumannContractiveResolvent j B₁ E hB₁ hForm₁ hE
      (fun lam hLam => pressure_neumann_canonical_denseRange lam j B₁ E
        hB₁ hForm₁ hE hSym₁ hjinj hjDense hLam)
  have hUnit : C.operator oneShift = pressureHilbertWeakResolvent j B₁ hB₁ :=
    pressure_neumann_dense_unit_resolvent_eq j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense
  change (u, f) ∈ pressureNeumannResolventGraph (pressureHilbertWeakResolvent j B₁ hB₁) ↔
    ∃ hu : u ∈ C.generatedSemigroup.generatorDomain,
      C.generatedSemigroup.generator ⟨u, hu⟩ = -f
  exact pressure_neumann_generator_graph_of_unit C _ hUnit u f

/-- The weak Neumann energy equation E(x,v)=⟪f,jv⟫, u=jx,
is equivalent to the original Lax–Milgram unbounded operator graph.
This direction of the weak operator identification does not require
positivity or symmetry: only the coercive shifted variational form. -/
theorem pressure_neumann_weak_energy_graph_iff
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (u f : H) :
    (∃ x : V, j x = u ∧ ∀ v : V, E x v = ⟪f, j v⟫_ℝ) ↔
      (u, f) ∈ pressureNeumannResolventGraph (pressureHilbertWeakResolvent j B₁ hB₁) := by
  constructor
  · rintro ⟨x, hx, hweak⟩
    have hb : ∀ v : V, B₁ x v = ⟪u + f, j v⟫_ℝ := by
      intro v
      calc
        B₁ x v = ⟪j x, j v⟫_ℝ + E x v := hForm₁ x v
        _ = ⟪u, j v⟫_ℝ + ⟪f, j v⟫_ℝ := by rw [hx, hweak v]
        _ = ⟪u + f, j v⟫_ℝ := (inner_add_left u f (j v)).symm
    have hsol : x = pressureHilbertWeakSolution j B₁ hB₁ (u + f) :=
      pressure_hilbert_weak_solution_unique j B₁ hB₁ (u + f) x hb
    change pressureHilbertWeakResolvent j B₁ hB₁ (u + f) = u
    rw [pressure_hilbert_resolvent_apply, ← hsol, hx]
  · intro hgraph
    let x := pressureHilbertWeakSolution j B₁ hB₁ (u + f)
    refine ⟨x, ?_, ?_⟩
    · change pressureHilbertWeakResolvent j B₁ hB₁ (u + f) = u at hgraph
      simpa only [x, pressure_hilbert_resolvent_apply] using hgraph
    · intro v
      exact pressure_hilbert_neumann_graph_green
        j B₁ E hB₁ hForm₁ u f hgraph v

/-- Main bridge: the constructed semigroup has exactly the weak Neumann
operator as its NEGATIVE generator, with no separately assumed operator
Green identity or generator comparison. -/
theorem pressure_neumann_dense_generator_weak_iff
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (u f : H) :
    (∃ x : V, j x = u ∧ ∀ v : V, E x v = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain,
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator ⟨u, hu⟩ = -f := by
  exact (pressure_neumann_weak_energy_graph_iff j B₁ E hB₁ hForm₁ u f).trans
    (pressure_neumann_dense_generated_graph_iff
      j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense u f)

end ReservoirSeismicityControl
