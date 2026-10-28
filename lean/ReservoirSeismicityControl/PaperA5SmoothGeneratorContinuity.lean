import ReservoirSeismicityControl.PaperA5MultiwellGeneratorCommutation
import ReservoirSeismicityControl.PaperA5CausalLocalIntegrability
import ReservoirSeismicityControl.PaperA5FiniteHorizonConvolution
import Mathlib.Tactic

/-!
# Stage 72: continuous generator image for the smooth-profile multiwell pressure solution

Stages 66–69 identified an everywhere-continuous, finite-horizon
regularized convolution representation with the physical forward Duhamel
integral. Stages 70–71 proved that, when each fixed spatial well profile is
in the generator domain, the unbounded generator commutes with the integral.

This theorem combines the two results. It constructs a *globally continuous
real-time representative* of the generator of the actual multiwell mild
solution on a prescribed physical horizon. There is no Qdot assumption.

The remaining step for arbitrary L² well profiles is to use Stage 65's
uniform generator-image approximation estimate, Stage 64's uniform limit
criterion, and density of the physical Neumann generator domain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal Convolution BigOperators

section SmoothGeneratorContinuity

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The true generator image of the smooth-profile physical multiwell mild
solution has a continuous real-time representative throughout every finite
physical horizon. The domain-membership proof is constructed from Stage 71;
the continuous representative is constructed from Stages 66–69.

The theorem makes no assumption on the time derivative of any well rate. -/
theorem pressure_A5_smooth_multiwell_generator_continuous_representative
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (T : ℝ)))) :
    ∃ F : ℝ → H, Continuous F ∧
      ∀ t : NNReal, t ≤ T →
        ∃ hp : (S t (p₀ : H) +
          pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q)
            ∈ S.generatorDomain,
          S.generator ⟨S t (p₀ : H) +
            pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q, hp⟩ =
              F (t : ℝ) := by
  classical
  let R (j : Fin m) : ℝ → H := fun τ =>
    (∫ s in (0 : ℝ)..τ, pressureA5HorizonRate T (q j) s) •
      S.generator (f j) +
    ((pressureA5HorizonRate T (q j))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (pressureA5RegularizedKernel S (S.generator (f j)))) τ
  let F : ℝ → H := fun τ =>
    S (Real.toNNReal τ) (S.generator p₀) +
      ∑ j : Fin m, R j τ
  have hR (j : Fin m) : Continuous (R j) := by
    exact pressure_A5_horizon_regularized_volterra_continuous
      S T (q j) (hq j) (S.generator (f j))
  have hF : Continuous F := by
    change Continuous (fun τ : ℝ =>
      S (Real.toNNReal τ) (S.generator p₀) +
        ∑ j : Fin m, R j τ)
    exact (S.continuous_operator_toNNReal (S.generator p₀)).add
      (continuous_finsetSum Finset.univ (fun j _ => hR j))
  refine ⟨F, hF, ?_⟩
  intro t ht
  have htReal : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hLocal (j : Fin m) :
      Integrable (q j) (volume.restrict (Set.Ico 0 (t : ℝ))) := by
    exact IntegrableOn.mono_set (hq j) (by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 htReal⟩)
  obtain ⟨hp, hgen⟩ :=
    pressure_A5_full_generator_commutes_of_local_rates
      S t p₀ m f q hLocal
  refine ⟨hp, ?_⟩
  have hDuhamel :=
    pressure_A5_horizon_regularized_eq_forward_of_local_rates
      S T t ht m (fun j => S.generator (f j)) q hq
  have hRepresentative :
      F (t : ℝ) = S t (S.generator p₀) +
        pressureA5ForwardDuhamel S t m
          (fun j => S.generator (f j)) q := by
    calc
      F (t : ℝ) = S t (S.generator p₀) +
          ∑ j : Fin m, R j (t : ℝ) := by
        dsimp [F]
        rw [Real.toNNReal_coe]
      _ = S t (S.generator p₀) +
          pressureA5ForwardDuhamel S t m
            (fun j => S.generator (f j)) q := by
        congr 1
  exact hgen.trans hRepresentative.symm

end SmoothGeneratorContinuity
end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_smooth_multiwell_generator_continuous_representative
