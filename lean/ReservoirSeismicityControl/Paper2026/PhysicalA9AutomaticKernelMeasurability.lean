import ReservoirSeismicityControl.Paper2026.PhysicalA9AnalyticPositiveLag
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): measurable far-field convolution without extra Q hypotheses

The already-compiled A5 formulation assumes q_j is integrable on [0,t).
The interval measures [0,t) and (0,t] coincide for Lebesgue-a.e. purposes.
Together with strong continuity of every Neumann-semigroup orbit and
continuity of the far projection, this proves the a.e. strong measurability
of the actual smooth-well projected integrands. No q-dot and no new
measurability assumption are needed. The off-diagonal integrable majorant
remains a separate, explicitly cited analytic-semigroup condition.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- Discharges the previously explicit strong-measurability premise for
all smooth well approximants, using only integrability of the actual rate
and strongly continuous semigroup orbits. -/
theorem paper_A9_kernel_measurable_from_integrable_Q
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (t : NNReal) (m : ℕ)
    (g : ℕ → Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ)))) :
    ∀ j : Fin m, ∀ n : ℕ,
      AEStronglyMeasurable
        (fun s : ℝ => (q j s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
        (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
  intro j n
  have hMeasures :
      (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t : ℝ)) =
        (volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) (t : ℝ)) :=
    ((volume : Measure ℝ).restrict_congr_set
      (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := (t : ℝ)))).symm
  have hQ : AEStronglyMeasurable (q j)
      (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
    rw [hMeasures]
    exact (hq j).aestronglyMeasurable
  have hOrbit : Continuous (fun s : ℝ =>
      ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))) :=
    (ReservoirSeismicityControl.paperFarLpProjection μ far hfar).continuous.comp
      ((S.continuous_operator_toNNReal (S.generator (g n j))).comp
        (continuous_const.sub continuous_id))
  exact hQ.smul hOrbit.aestronglyMeasurable

/-- The paper's actual L²-forced pressure generator has the causal far-field
integral representation. Unlike the previous theorem, there is NO free
positive-lag convergence hypothesis: it follows from the cited analytic
smoothing operator and the established L² profile approximation.

The remaining uniform integrable off-diagonal bound is the published
Davies--Gaffney/analytic semigroup applicability input; it is not
silently inferred from bare semigroup continuity. -/
theorem paper_A9_actual_L2_wells_causal_with_automatic_kernel_measurability
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
      P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩) =
        P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (q j s) • T s (f j) := by
  have hKernelMeas := paper_A9_kernel_measurable_from_integrable_Q
    μ far hfar S t m g q hq
  have hLag (j : Fin m) :=
    paper_A9_positive_lag_from_analytic_smoothing
      μ far hfar S t m f g hgLimit T hAnalytic j
  exact paper_A9_actual_L2_wells_projected_causal_of_offdiagonal
    μ far hfar S hSelf hGraph t p₀ m f q hq M hM hBound
    g hgLimit (fun j s => T s (f j)) b hbInt hKernelMeas hOffDiag hLag


end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_kernel_measurable_from_integrable_Q
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_L2_wells_causal_with_automatic_kernel_measurability
