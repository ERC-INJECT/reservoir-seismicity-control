import ReservoirSeismicityControl.PaperA5MultiwellGeneratorCommutation
import ReservoirSeismicityControl.PaperA5CausalLocalIntegrability
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
Appendix A.3, (A9): the first *physical* generator-to-causal projection bridge.

For spatial well profiles in the generator domain D(A), the previously
proved A5 multiwell generator/Duhamel identity yields the actual far-projected
causal generator formula, with merely integrable signed well rates.

This is the D(A)-profile case of the desired equation. The manuscript's
indicator well profiles are generally in L² rather than D(A); extending
this identity to those profiles requires A5 profile stability and the
externally cited Davies--Gaffney far-projection envelope. We do NOT
assume the final physical A9 identity or the differentiability of Q.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped NNReal BigOperators InnerProductSpace

/-- The projected generator of the actual multiwell mild solution equals
its initial projected generator orbit plus the finite causal forcing integral.
The assumption `f : Fin m → S.generatorDomain` is *visible*: this theorem
is a verified stepping stone, not the final characteristic-well result. -/
theorem paper_A9_smooth_wells_projected_full_causal_generator
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ)))) :
    ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
        (fun j => (f j : Lp ℝ 2 μ)) q) ∈ S.generatorDomain,
      let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
      P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
            (fun j => (f j : Lp ℝ 2 μ)) q, hp⟩) =
        P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            q j s • P (S (Real.toNNReal ((t : ℝ) - s))
              (S.generator (f j))) := by
  obtain ⟨hp, hgen⟩ :=
    ReservoirSeismicityControl.pressure_A5_full_generator_commutes_of_local_rates
      S t p₀ m f q hq
  refine ⟨hp, ?_⟩
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  have hProjected (j : Fin m) :
      P (∫ s in (0 : ℝ)..(t : ℝ),
        q j s • S (Real.toNNReal ((t : ℝ) - s))
          (S.generator (f j))) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j))) := by
    have hqInterval : IntervalIntegrable (q j) volume 0 (t : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le
        (NNReal.coe_nonneg t)).2 (hq j)
    have hOrbit : IntervalIntegrable
        (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s))
          (S.generator (f j))) volume 0 (t : ℝ) :=
      ReservoirSeismicityControl.pressure_A5_forward_orbit_intervalIntegrable
        S t (q j) (S.generator (f j)) hqInterval
    calc
      P (∫ s in (0 : ℝ)..(t : ℝ),
        q j s • S (Real.toNNReal ((t : ℝ) - s))
          (S.generator (f j))) =
          ∫ s in (0 : ℝ)..(t : ℝ),
            P (q j s • S (Real.toNNReal ((t : ℝ) - s))
              (S.generator (f j))) :=
        (ContinuousLinearMap.intervalIntegral_comp_comm P hOrbit).symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j))) := by
        apply intervalIntegral.integral_congr
        intro s _
        change P (q j s • S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j))) =
          q j s • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j)))
        simp only [map_smul]
  change P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
        (fun j => (f j : Lp ℝ 2 μ)) q, hp⟩) =
    P (S t (S.generator p₀)) +
      ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
        q j s • P (S (Real.toNNReal ((t : ℝ) - s))
          (S.generator (f j)))
  calc
    P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
          (fun j => (f j : Lp ℝ 2 μ)) q, hp⟩) =
        P (S t (S.generator p₀) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
            (fun j => S.generator (f j)) q) := by
      exact congrArg P hgen
    _ = P (S t (S.generator p₀)) +
        ∑ j : Fin m, P (∫ s in (0 : ℝ)..(t : ℝ),
          q j s • S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j))) := by
      unfold ReservoirSeismicityControl.pressureA5ForwardDuhamel
      rw [map_add, map_sum]
    _ = P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j))) := by
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hProjected j)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_wells_projected_full_causal_generator
