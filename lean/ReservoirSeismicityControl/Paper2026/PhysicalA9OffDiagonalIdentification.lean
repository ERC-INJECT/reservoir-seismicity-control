import ReservoirSeismicityControl.Paper2026.PhysicalA9ChosenLocalApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): physical far-field convolution identification

This theorem REUSES the already compiled physical A5 profile-stability and
smooth-well causal results. The only remaining positive-lag PDE input is the
published analytic/off-diagonal semigroup estimate used by (A8), expressed as
Bochner measurability, an integrable majorant, and the positive-lag limit of
the localized smooth generator orbits.

It does not assume the desired equality P A p = a causal convolution.
The theorem DERIVES that equality from the actual mild pressure generator.
It never differentiates the time-dependent well rate Q.

The input K(j,s) represents the far projection of the physical positive-lag
A exp(-A(t-s)) applied to the actual (centered) j-th well profile. The sign
convention in this module is for the semigroup generator L=-A; the final
A9 sign can be restored by multiplying the resulting equality by -1.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- The actual far-projected generator is equal to the physical causal
Bochner integral once the standard analytic-semigroup positive-lag
applicability conditions hold. Importantly, the smooth-to-physical generator
limit on the left is PROVED by A5 profile stability; the only external
inputs concern the far-projected kernel on positive lags. -/
theorem paper_A9_actual_L2_wells_projected_causal_of_offdiagonal
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
    (K : Fin m → ℝ → Lp ℝ 2 μ)
    (b : Fin m → ℝ → ℝ)
    (hbInt : ∀ j : Fin m,
      Integrable (b j) (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))))
    (hKernelMeas : ∀ j : Fin m, ∀ n : ℕ,
      AEStronglyMeasurable
        (fun s : ℝ => (q j s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
        (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))))
    (hOffDiag : ∀ j : Fin m, ∀ n : ℕ,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        ‖(q j s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))‖ ≤ b j s)
    (hPositiveLag : ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        Tendsto
          (fun n : ℕ => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
          atTop (𝓝 (K j s))) :
    ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
      let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
      P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩) =
        P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ), (q j s) • K j s := by
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))
  have hEach (j : Fin m) :
      Tendsto
        (fun n : ℕ => ∫ s in (0 : ℝ)..(t : ℝ),
          (q j s) • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (g n j))))
        atTop
        (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), (q j s) • K j s)) := by
    have hLag : ∀ᵐ s ∂ν,
        Tendsto
          (fun n : ℕ => (q j s) • P
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
          atTop (𝓝 ((q j s) • K j s)) := by
      filter_upwards [hPositiveLag j] with s hs
      exact (tendsto_const_nhds.smul hs)
    have hDCT := tendsto_integral_of_dominated_convergence
      (b j) (hKernelMeas j) (hbInt j) (hOffDiag j) hLag
    simpa only [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), P, ν]
      using hDCT
  have hAll : Tendsto
      (fun n : ℕ => P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (q j s) • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (g n j))))
      atTop
      (𝓝 (P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (q j s) • K j s)) := by
    have hSum : Tendsto
        (fun n : ℕ => ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (q j s) • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (g n j))))
        atTop
        (𝓝 (∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          (q j s) • K j s)) := by
      apply tendsto_finsetSum Finset.univ
      intro j _
      exact hEach j
    exact tendsto_const_nhds.add hSum
  obtain ⟨hp, hA5Limit⟩ :=
    paper_A9_chosen_local_approximants_smooth_causal_limit
      μ far hfar S hSelf hGraph t p₀ m f q hq M hM hBound g hgLimit
  refine ⟨hp, ?_⟩
  change P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
    ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩) =
      P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ), (q j s) • K j s
  exact tendsto_nhds_unique hA5Limit hAll

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_L2_wells_projected_causal_of_offdiagonal
