import ReservoirSeismicityControl.PressurePositiveSemigroupStepCFoundation
import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSelfAdjointGraph

/-!
# A5 bounded-input limit: the weak closed-graph step

The step Duhamel module bounds the generator images of finite step
approximations uniformly. This module supplies the missing *identification*
of a weak generator limit with the generator of the strong pressure limit.

The essential hypothesis here is convergence of the generator images tested
against every fixed vector. This is weaker than strong convergence and is
not inferred from a uniform bound alone.

Remaining tasks before full L∞ A5:
* construct uniformly bounded step approximations of measurable well rates;
* show convergence of their Duhamel integrals in H;
* extract a weakly convergent generator subsequence from uniform bounds;
* instantiate the physical generator graph for the exact semigroup used.

No `sorry`, `axiom`, compact resolvent, eigenbasis, or bounded Q' is used.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace

section AbstractWeakGraph

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- If a sequence of generator-domain vectors converges strongly, and its
 generator images converge weakly, the limit is in the domain.  This uses
 the self-adjoint *graph characterization*, not an assumed strong limit
 of the generator images. -/
theorem pressure_generator_of_weak_graph_limit
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (u : ℕ → S.generatorDomain) (p g : H)
    (hp : Tendsto (fun k => (u k : H)) atTop (𝓝 p))
    (hgWeak : ∀ v : H,
      Tendsto (fun k => ⟪S.generator (u k), v⟫_ℝ)
        atTop (𝓝 ⟪g, v⟫_ℝ)) :
    ∃ hpDomain : p ∈ S.generatorDomain,
      S.generator ⟨p, hpDomain⟩ = g := by
  apply (hGraph p g).mp
  intro v hv
  have hSym (k : ℕ) :
      ⟪(u k : H), S.generator ⟨v, hv⟩⟫_ℝ =
        ⟪S.generator (u k), v⟫_ℝ := by
    have hFormal := (hGraph (u k : H) (S.generator (u k))).mpr
      ⟨(u k).property, rfl⟩
    exact hFormal v hv
  have hEqFun :
      (fun k : ℕ => ⟪(u k : H), S.generator ⟨v, hv⟩⟫_ℝ) =
      (fun k : ℕ => ⟪S.generator (u k), v⟫_ℝ) := by
    funext k
    exact hSym k
  have hLeft :
      Tendsto (fun k : ℕ => ⟪(u k : H), S.generator ⟨v, hv⟩⟫_ℝ)
        atTop (𝓝 ⟪p, S.generator ⟨v, hv⟩⟫_ℝ) := by
    have hContinuous :
        Continuous (fun z : H => ⟪z, S.generator ⟨v, hv⟩⟫_ℝ) := by
      fun_prop
    exact (hContinuous.tendsto p).comp hp
  have hRight :
      Tendsto (fun k : ℕ => ⟪(u k : H), S.generator ⟨v, hv⟩⟫_ℝ)
        atTop (𝓝 ⟪g, v⟫_ℝ) := by
    rw [hEqFun]
    exact hgWeak v
  exact tendsto_nhds_unique hLeft hRight

/-- The Hilbert norm of a weak limit cannot exceed a uniform norm bound.
 The proof tests weak convergence against the limit vector itself. -/
theorem pressure_weak_limit_generator_norm_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (u : ℕ → S.generatorDomain) (g : H) (C : ℝ)
    (hgWeak : ∀ v : H,
      Tendsto (fun k => ⟪S.generator (u k), v⟫_ℝ)
        atTop (𝓝 ⟪g, v⟫_ℝ))
    (hBound : ∀ k, ‖S.generator (u k)‖ ≤ C) :
    ‖g‖ ≤ C := by
  have hC : 0 ≤ C :=
    (norm_nonneg (S.generator (u 0))).trans (hBound 0)
  have hPoint (k : ℕ) :
      ⟪S.generator (u k), g⟫_ℝ ≤ C * ‖g‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hBound k) (norm_nonneg g))
  have hLimit : ⟪g, g⟫_ℝ ≤ C * ‖g‖ :=
    le_of_tendsto (hgWeak g) (Filter.Eventually.of_forall hPoint)
  rw [real_inner_self_eq_norm_sq] at hLimit
  by_cases hzero : ‖g‖ = 0
  · simpa only [hzero] using hC
  · have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hzero)
    by_contra hNot
    have hgt : C < ‖g‖ := lt_of_not_ge hNot
    have hprod : 0 < (‖g‖ - C) * ‖g‖ :=
      mul_pos (sub_pos.mpr hgt) hpos
    nlinarith

/-- The desired abstract A5 weak-graph passage, conditional only on a
 genuinely weakly convergent subsequence of generator terms. -/
theorem pressure_generator_bound_of_weak_graph_limit
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (u : ℕ → S.generatorDomain) (p g : H) (C : ℝ)
    (hp : Tendsto (fun k => (u k : H)) atTop (𝓝 p))
    (hgWeak : ∀ v : H,
      Tendsto (fun k => ⟪S.generator (u k), v⟫_ℝ)
        atTop (𝓝 ⟪g, v⟫_ℝ))
    (hBound : ∀ k, ‖S.generator (u k)‖ ≤ C) :
    ∃ hpDomain : p ∈ S.generatorDomain,
      S.generator ⟨p, hpDomain⟩ = g ∧ ‖g‖ ≤ C := by
  obtain ⟨hpDomain, heq⟩ :=
    pressure_generator_of_weak_graph_limit S hGraph u p g hp hgWeak
  exact ⟨hpDomain, heq, pressure_weak_limit_generator_norm_bound S u g C hgWeak hBound⟩

end AbstractWeakGraph

end ReservoirSeismicityControl
