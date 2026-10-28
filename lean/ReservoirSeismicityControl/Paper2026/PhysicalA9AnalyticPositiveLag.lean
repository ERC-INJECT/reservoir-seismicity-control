import ReservoirSeismicityControl.Paper2026.PhysicalA9OffDiagonalIdentification
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): positive-lag smoothing for the actual L² wells

For positive lag τ, analytic-semigroup theory supplies a *bounded* operator
Tτ extending the domain operator P L exp(τL), where L=-A and P is the physical
far-field projection. This theorem uses ONLY continuity of that bounded
operator and the previously constructed localized L² approximants to obtain
the missing positive-lag convergence in the A9 off-diagonal identification.

The existence of Tτ with the stated physical action is a standard analytic
semigroup applicability input (cited in the manuscript); it is NOT the
conclusion of A9. The remaining kernel measurability and uniform off-diagonal
integrable envelope are kept as explicit inputs. We do not assume a derivative
of Q, and do not repeat the density, stability, or convolution proofs.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- Analytic smoothing at every positive lag converts convergence of the
actual physical source profiles in L² into the missing positive-lag limit
of their *projected generator* orbits. -/
theorem paper_A9_positive_lag_from_analytic_smoothing
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (t : NNReal) (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
    (g : ℕ → Fin m → S.generatorDomain)
    (hgLimit : ∀ j : Fin m, Tendsto
      (fun n : ℕ => (g n j : Lp ℝ 2 μ)) atTop (𝓝 (f j)))
    (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hAnalytic : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) (t : ℝ) →
      ∀ u : S.generatorDomain,
        ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
          T s (u : Lp ℝ 2 μ))
    (j : Fin m) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
      Tendsto
        (fun n : ℕ => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
        atTop (𝓝 (T s (f j))) := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
  have hContinuous : Tendsto
      (fun n : ℕ => T s ((g n j : Lp ℝ 2 μ)))
      atTop (𝓝 (T s (f j))) :=
    ((T s).continuous.tendsto (f j)).comp (hgLimit j)
  have hOrbitEq :
      (fun n : ℕ => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))) =
      (fun n : ℕ => T s ((g n j : Lp ℝ 2 μ))) := by
    funext n
    exact hAnalytic s hs (g n j)
  rw [hOrbitEq]
  exact hContinuous

/-- The paper's actual L²-forced pressure generator has the causal far-field
integral representation. Unlike the previous theorem, there is NO free
positive-lag convergence hypothesis: it follows from the cited analytic
smoothing operator and the established L² profile approximation.

The measurability and uniform integrable off-diagonal bound are precisely
the remaining published Davies--Gaffney/analytic semigroup applicability
inputs; neither is silently inferred from bare semigroup continuity. -/
theorem paper_A9_actual_L2_wells_projected_causal_from_analytic_smoothing
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
    (hKernelMeas : ∀ j : Fin m, ∀ n : ℕ,
      AEStronglyMeasurable
        (fun s : ℝ => (q j s) • ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
        (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))))
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
  have hLag (j : Fin m) :=
    paper_A9_positive_lag_from_analytic_smoothing
      μ far hfar S t m f g hgLimit T hAnalytic j
  exact paper_A9_actual_L2_wells_projected_causal_of_offdiagonal
    μ far hfar S hSelf hGraph t p₀ m f q hq M hM hBound
    g hgLimit (fun j s => T s (f j)) b hbInt hKernelMeas hOffDiag hLag

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_positive_lag_from_analytic_smoothing
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_L2_wells_projected_causal_from_analytic_smoothing
