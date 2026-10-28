import ReservoirSeismicityControl.PaperA5CausalConvolutionIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Stage 69: physical local well-rate integrability closes the causal Duhamel identity

Stage 68 identified the causal finite-horizon semigroup convolution with
`pressureA5ForwardDuhamel`, conditional on interval integrability of the
vector-valued orbit forcing. Here those hypotheses are DERIVED from the
single physical input condition `IntegrableOn q (Ico 0 T)`.

The key fact is `IntervalIntegrable.smul_continuousOn`: the semigroup orbit
`S (Real.toNNReal (t-s)) f` is continuous in s, so multiplying it by an
integrable scalar rate is Bochner-integrable. The same argument works for
its constant-vector part. Neither temporal derivatives of q nor global
integrability on the real line are required.

The result does not yet commute the unbounded generator with the integral.
That is the next analytical step. Nor does it assert physical continuity
of the generator image before that commutation is established.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal Convolution BigOperators

section LocalIntegrability

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The physical well forcing is Bochner interval-integrable as soon as its
scalar rate is integrable on the same interval. -/
theorem pressure_A5_forward_orbit_intervalIntegrable
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (q : ℝ → ℝ) (g : H)
    (hq : IntervalIntegrable q volume 0 (t : ℝ)) :
    IntervalIntegrable
      (fun s : ℝ => q s • S (Real.toNNReal ((t : ℝ) - s)) g)
      volume 0 (t : ℝ) := by
  have horbit : Continuous (fun s : ℝ =>
      S (Real.toNNReal ((t : ℝ) - s)) g) :=
    (S.continuous_operator_toNNReal g).comp (continuous_const.sub continuous_id)
  exact hq.smul_continuousOn horbit.continuousOn

/-- The constant-vector forcing is interval-integrable under exactly the
same scalar integrability assumption. -/
theorem pressure_A5_constant_orbit_intervalIntegrable
    (t : NNReal) (q : ℝ → ℝ) (g : H)
    (hq : IntervalIntegrable q volume 0 (t : ℝ)) :
    IntervalIntegrable (fun s : ℝ => q s • g)
      volume 0 (t : ℝ) :=
  hq.smul_continuousOn continuousOn_const

/-- Stage 68's exact identity holds using ONLY finite-horizon local
integrability of the actual physical rates. In particular it no longer
assumes separate vector-valued Bochner integrability certificates.

This is the physically relevant 29-well finite-sum formulation. -/
theorem pressure_A5_horizon_regularized_eq_forward_of_local_rates
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T t : NNReal) (ht : t ≤ T)
    (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (T : ℝ)))) :
    ((Finset.univ : Finset (Fin m)).sum (fun (j : Fin m) =>
      (∫ s in (0 : ℝ)..(t : ℝ), pressureA5HorizonRate T (q j) s) • f j +
        ((pressureA5HorizonRate T (q j)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (pressureA5RegularizedKernel S (f j))) (t : ℝ))) =
      pressureA5ForwardDuhamel S t m f q := by
  have htR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hscalar (j : Fin m) :
      IntervalIntegrable (q j) volume 0 (t : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le
      (NNReal.coe_nonneg t)).2
    exact IntegrableOn.mono_set
      (show IntegrableOn (q j) (Set.Ico 0 (T : ℝ)) volume from hq j)
      (by
        intro s hs
        exact ⟨hs.1, lt_of_lt_of_le hs.2 htR⟩)
  have hforward (j : Fin m) : IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j))
      volume 0 (t : ℝ) :=
    pressure_A5_forward_orbit_intervalIntegrable S t (q j) (f j) (hscalar j)
  have hbase (j : Fin m) : IntervalIntegrable
      (fun s : ℝ => q j s • f j) volume 0 (t : ℝ) :=
    pressure_A5_constant_orbit_intervalIntegrable t (q j) (f j) (hscalar j)
  exact pressure_A5_horizon_regularized_eq_forward_multiwell
    S T t ht m f q hforward hbase

end LocalIntegrability

end ReservoirSeismicityControl
