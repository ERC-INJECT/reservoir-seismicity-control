import ReservoirSeismicityControl.Paper2026.PhysicalA9AutomaticKernelMeasurability
import ReservoirSeismicityControl.Paper2026.PhysicalA9CausalSemigroupFromDensity20261025
import Mathlib.Tactic

/-!
# Physical A9: no free homogeneous derivative or generator causal-value identity

Both results here are applications of existing ReservoirSeismicityControl/MarkovProcess theorems.
The first is an actual positive-time semigroup derivative, not a premise
asserting the homogeneous derivative. The second applies the existing
physical A5 generator/causal identity to the negative generator `A p`.

The generator used by MarkovProcess is `-A` in the ReservoirSeismicityControl pressure
convention. Therefore the *negative* generator is the positive elliptic
operator `A` in Appendix A. Neither theorem differentiates the well flux.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- The homogeneous A9 projected pressure-generator term is differentiable
    for physical time t>0. Here `u` is the generator-domain representative
    of the initial positive generator `A p(0)` (equivalently the initial
    `p_t` up to the well-source correction). `L` is the manuscript's positive
    generator orbit `A exp(-At)`, identified by `hLGenerator` with the
    negative of the strongly continuous semigroup generator orbit.

    This DERIVES the derivative from `S.hasDerivAt_operator_toNNReal`.
    In particular, no hypothesis about differentiability of the homogeneous
    orbit appears in this theorem. -/
theorem paper_A9_projected_homogeneous_rate_from_real_semigroup
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (u : S.generatorDomain)
    (L : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hLGenerator : ∀ t : ℝ, 0 < t →
      L t (u : Lp ℝ 2 μ) =
        -(S (Real.toNNReal t) (S.generator u))) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => P (S (Real.toNNReal τ) (u : Lp ℝ 2 μ)))
        (-(P (L t (u : Lp ℝ 2 μ)))) t := by
  have hPositive : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), 0 < t := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)), 0 < t
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  filter_upwards [hPositive] with t ht
  have hd := S.hasDerivAt_operator_toNNReal u ht
  have hp := P.hasFDerivAt.comp_hasDerivAt t hd
  have hp' : HasDerivAt
      (fun τ : ℝ => P (S (Real.toNNReal τ) (u : Lp ℝ 2 μ)))
      (P (S (Real.toNNReal t) (S.generator u))) t := by
    change HasDerivAt
      (fun τ : ℝ => P (S (Real.toNNReal τ) (u : Lp ℝ 2 μ)))
      (P (S (Real.toNNReal t) (S.generator u))) t at hp
    exact hp
  simpa only [hLGenerator t ht, map_neg, neg_neg] using hp'

/-- Physical A5 + the already verified off-diagonal causal identification
    yield the actual negative-generator pressure value, at an arbitrary
    nonnegative observation horizon. There is *no* free `hMildValue` input:
    the identity is obtained using the pre-existing A9 physical well theorem.

    The right-hand side is written as the negative of the generator's causal
    expression to preserve the sign `A=-generator` exactly. -/
theorem paper_A9_actual_negative_generator_causal_value_of_analytic_DG
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u v : Lp ℝ 2 μ,
      (∀ w : Lp ℝ 2 μ, ∀ hw : w ∈ S.generatorDomain,
        ⟪u, S.generator ⟨w, hw⟩⟫_ℝ = ⟪v, w⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = v)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q j s| ≤ M j)
    (g : ℕ → Fin m → S.generatorDomain)
    (hgLimit : ∀ j : Fin m, Tendsto
      (fun n : ℕ => (g n j : Lp ℝ 2 μ)) atTop (𝓝 (f j)))
    (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hAnalytic : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) (t : ℝ) →
      ∀ u : S.generatorDomain,
        ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
          T s (u : Lp ℝ 2 μ))
    (b : Fin m → ℝ → ℝ)
    (hbInt : ∀ j : Fin m,
      Integrable (b j) (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))))
    (hOffDiag : ∀ j : Fin m, ∀ n : ℕ,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        ‖(q j s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))‖ ≤ b j s) :
    ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
      let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
      P (-(S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩)) =
        -(P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (q j s) • T s (f j)) := by
  obtain ⟨hp, hg⟩ :=
    paper_A9_actual_L2_wells_causal_with_automatic_kernel_measurability
      μ far hfar S hSelf hGraph t p₀ m f q hq M hM hBound
      g hgLimit T hAnalytic b hbInt hOffDiag
  refine ⟨hp, ?_⟩
  dsimp only at hg ⊢
  simpa only [map_neg] using congrArg Neg.neg hg

#print axioms paper_A9_projected_homogeneous_rate_from_real_semigroup
#print axioms paper_A9_actual_negative_generator_causal_value_of_analytic_DG

end ReservoirSeismicityControl.Paper2026
