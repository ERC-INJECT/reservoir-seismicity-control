import ReservoirSeismicityControl.PressurePositiveSemigroupDualTest
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# A5: Hilbert-space duality closes the bounded-generator limit

This module closes the ABSTRACT strong-pressure-limit step without extracting
weakly convergent subsequences. The key ingredients are:

* the self-adjoint graph characterization of the generator;
* Hahn--Banach extension of a norm-bounded functional from generatorDomain;
* the real Hilbert-space Riesz representation theorem.

The first theorem assumes a bound on the dual generator functional. The second
derives that bound from the uniform generator estimates of a strongly
converging sequence, using the previously compiled dual-test result.

Still separate: construction of interval-step approximations for all bounded
measurable well rates, identification with the Bochner Duhamel integral,
and instantiation with the exact physical semigroup.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace

section BoundedDualLimit

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded dual generator functional belongs to the self-adjoint generator
 domain and has the same bound. This does not use weak sequential compactness. -/
theorem pressure_generator_bound_of_dual_estimate
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (p : H) (C : ℝ) (hC : 0 ≤ C)
    (hDual : ∀ v : S.generatorDomain,
      |⟪p, S.generator v⟫_ℝ| ≤ C * ‖(v : H)‖) :
    ∃ hp : p ∈ S.generatorDomain,
      ‖S.generator ⟨p, hp⟩‖ ≤ C := by
  let F : S.generatorDomain →ₗ[ℝ] ℝ := {
    toFun := fun v => ⟪p, S.generator v⟫_ℝ
    map_add' := by
      intro v w
      simp only [map_add, inner_add_right]
    map_smul' := by
      intro r v
      simp only [map_smul, real_inner_smul_right, smul_eq_mul]
      rfl
  }
  have hF (v : S.generatorDomain) : ‖F v‖ ≤ C * ‖v‖ := by
    change |⟪p, S.generator v⟫_ℝ| ≤ C * ‖(v : H)‖
    exact hDual v
  let Fc : StrongDual ℝ S.generatorDomain := F.mkContinuous C hF
  have hFcNorm : ‖Fc‖ ≤ C :=
    Fc.opNorm_le_bound hC (by
      intro v
      change ‖F v‖ ≤ C * ‖v‖
      exact hF v)
  obtain ⟨E, hExt, hExtNorm⟩ :=
    exists_extension_norm_eq S.generatorDomain Fc
  let g : H := (InnerProductSpace.toDual ℝ H).symm E
  have hFormal : ∀ v : H, ∀ hv : v ∈ S.generatorDomain,
      ⟪p, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ := by
    intro v hv
    calc
      ⟪p, S.generator ⟨v, hv⟩⟫_ℝ = Fc ⟨v, hv⟩ := rfl
      _ = E v := (hExt ⟨v, hv⟩).symm
      _ = ⟪g, v⟫_ℝ := by
        simpa only [g] using
          (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v) (y := E)).symm
  obtain ⟨hp, hAp⟩ := (hGraph p g).mp hFormal
  refine ⟨hp, ?_⟩
  have hGnorm : ‖g‖ = ‖E‖ := by
    have hIsom := (InnerProductSpace.toDual ℝ H).norm_map g
    have hEq : (InnerProductSpace.toDual ℝ H) g = E := by simp [g]
    rw [hEq] at hIsom
    exact hIsom.symm
  calc
    ‖S.generator ⟨p, hp⟩‖ = ‖g‖ := by rw [hAp]
    _ = ‖E‖ := hGnorm
    _ = ‖Fc‖ := hExtNorm
    _ ≤ C := hFcNorm

/-- Strong pressure convergence and a uniform bound on generator images
 imply generator-domain membership and the same bound at the limit. No
 weakly convergent subsequence or strong generator convergence is needed. -/
theorem pressure_generator_bound_of_strong_pressure_limit
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (u : ℕ → S.generatorDomain) (p : H) (C : ℝ)
    (hp : Tendsto (fun k => (u k : H)) atTop (𝓝 p))
    (hBound : ∀ k, ‖S.generator (u k)‖ ≤ C) :
    ∃ hDomain : p ∈ S.generatorDomain,
      ‖S.generator ⟨p, hDomain⟩‖ ≤ C := by
  have hC : 0 ≤ C :=
    (norm_nonneg (S.generator (u 0))).trans (hBound 0)
  apply pressure_generator_bound_of_dual_estimate S hGraph p C hC
  intro v
  have hUp : ⟪p, S.generator v⟫_ℝ ≤ C * ‖(v : H)‖ :=
    pressure_generator_dual_test_upper_bound S hGraph u p C hp hBound v
  have hNeg :=
    pressure_generator_dual_test_upper_bound S hGraph u p C hp hBound (-v)
  have hDown : -⟪p, S.generator v⟫_ℝ ≤ C * ‖(v : H)‖ := by
    simpa only [map_neg, inner_neg_right, Submodule.coe_neg, norm_neg] using hNeg
  exact abs_le.mpr ⟨by linarith, hUp⟩

end BoundedDualLimit

end ReservoirSeismicityControl
