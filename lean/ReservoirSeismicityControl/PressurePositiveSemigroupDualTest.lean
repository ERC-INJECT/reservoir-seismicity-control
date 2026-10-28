import ReservoirSeismicityControl.PressurePositiveSemigroupMultiwellL1
import ReservoirSeismicityControl.PressurePositiveSemigroupWeakGraph

/-!
# A5 bounded-input limit: a direct dual test inequality

For a symmetric generator, a sequence u_k in the generator domain whose
pressures converge strongly and whose generator images are uniformly bounded
implies a bound on the limiting pressure paired against A v, for any
v in the generator domain. This conclusion requires NO weak subsequence.

The subsequent step is to represent this bounded functional by a vector
in H and apply the self-adjoint generator graph characterization. That
Riesz/extension step is not claimed in this module.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace

section DualTest

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform generator bounds pass directly to dual generator tests under
strong convergence of the pressure. There is no weak-limit hypothesis. -/
theorem pressure_generator_dual_test_upper_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (u : ℕ → S.generatorDomain) (p : H) (C : ℝ)
    (hp : Tendsto (fun k => (u k : H)) atTop (𝓝 p))
    (hBound : ∀ k, ‖S.generator (u k)‖ ≤ C)
    (v : S.generatorDomain) :
    ⟪p, S.generator v⟫_ℝ ≤ C * ‖(v : H)‖ := by
  have hSym (k : ℕ) :
      ⟪(u k : H), S.generator v⟫_ℝ =
        ⟪S.generator (u k), (v : H)⟫_ℝ := by
    have hFormal := (hGraph (u k : H) (S.generator (u k))).mpr
      ⟨(u k).property, rfl⟩
    exact hFormal (v : H) v.property
  have hPoint (k : ℕ) :
      ⟪(u k : H), S.generator v⟫_ℝ ≤ C * ‖(v : H)‖ := by
    rw [hSym k]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hBound k) (norm_nonneg (v : H)))
  have hc : Continuous (fun z : H => ⟪z, S.generator v⟫_ℝ) := by
    fun_prop
  have ht : Tendsto (fun k : ℕ => ⟪(u k : H), S.generator v⟫_ℝ)
      atTop (𝓝 ⟪p, S.generator v⟫_ℝ) :=
    (hc.tendsto p).comp hp
  exact le_of_tendsto ht (Filter.Eventually.of_forall hPoint)

end DualTest

end ReservoirSeismicityControl
