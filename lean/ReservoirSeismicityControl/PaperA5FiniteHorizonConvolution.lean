import ReservoirSeismicityControl.PaperA5RegularizedConvolutionContinuity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Stage 67: finite-horizon localization of measurable well rates

The paper requires bounded measurable well rates on physical finite time
intervals, not global time integrability on `ℝ`. Stage 66 established
continuity for an `L¹(ℝ)` rate. This file supplies that global integrability
by truncating an actual physical rate to `[0,T)`.

There is no derivative assumption on q, and the truncation does not alter
its values for `0 ≤ s < T`. We then directly apply the proven Stage 66
continuity theorem to obtain a continuous regularized convolution.

Important remaining work:
* Identify the full-line truncated-rate convolution with the original
  forward-time `pressureA5ForwardDuhamel` on `[0,T]`.
* Prove generator commutation for smooth spatial profiles in `D(A)`.
* Use Stages 64/65 to transfer continuity to arbitrary fixed profiles.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal Convolution

section FiniteHorizon

variable {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

/-- A physical well rate, set to zero outside a fixed nonnegative horizon. -/
noncomputable def pressureA5HorizonRate (T : NNReal) (q : ℝ → ℝ) : ℝ → ℝ :=
  (Set.Ico (0 : ℝ) (T : ℝ)).indicator q

/-- Physical time-local integrability implies global integrability of the
truncated rate. No global assumption on the untruncated rate is needed. -/
theorem pressure_A5_horizon_rate_integrable
    (T : NNReal) (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico (0 : ℝ) (T : ℝ)))) :
    Integrable (pressureA5HorizonRate T q) (volume : Measure ℝ) := by
  change Integrable ((Set.Ico (0 : ℝ) (T : ℝ)).indicator q) (volume : Measure ℝ)
  exact (integrable_indicator_iff measurableSet_Ico).2 hq

/-- On the actual physical observation interval, truncation leaves the
well rate unchanged, including arbitrary measurable temporal fluctuations. -/
theorem pressure_A5_horizon_rate_agrees
    (T : NNReal) (q : ℝ → ℝ) (s : ℝ)
    (hs0 : 0 ≤ s) (hsT : s < (T : ℝ)) :
    pressureA5HorizonRate T q s = q s := by
  unfold pressureA5HorizonRate
  exact Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hs0, hsT⟩) q

/-- Outside `[0,T)` the truncated rate vanishes. In particular the input
is causal: it is zero at all negative times. -/
theorem pressure_A5_horizon_rate_zero_outside
    (T : NNReal) (q : ℝ → ℝ) (s : ℝ)
    (hs : s ∉ Set.Ico (0 : ℝ) (T : ℝ)) :
    pressureA5HorizonRate T q s = 0 := by
  unfold pressureA5HorizonRate
  exact Set.indicator_of_notMem hs q

/-- Uniform temporal continuity of the regularized Volterra representation
on every finite physical horizon, starting from the paper's LOCAL
integrability condition alone. This is the crucial input-localization
extension of the Stage 66 convolution theorem.

It is NOT YET the identification of this representation with the generator
of the physical Neumann Duhamel solution. -/
theorem pressure_A5_horizon_regularized_volterra_continuous
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T : NNReal) (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico (0 : ℝ) (T : ℝ))))
    (g : H) :
    Continuous (fun t : ℝ =>
      (∫ s in (0 : ℝ)..t, pressureA5HorizonRate T q s) • g +
        ((pressureA5HorizonRate T q) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (pressureA5RegularizedKernel S g)) t) := by
  exact pressure_A5_regularized_volterra_continuous S
    (pressureA5HorizonRate T q)
    (pressure_A5_horizon_rate_integrable T q hq) g

end FiniteHorizon

end ReservoirSeismicityControl
