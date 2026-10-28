import ReservoirSeismicityControl.PaperA5FiniteHorizonConvolution
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Stage 68: exact causal convolution / physical Duhamel identity

Stage 66 proved continuity of the regularized Volterra expression.
Stage 67 localized the source rate to `[0,T)`.  This file identifies
that expression, for `0 <= t <= T`, with the *actual* forward-time Bochner
integral used in `pressureA5ForwardDuhamel`.

We first prove the identification of the regularized full-line
convolution with its causal interval integral. The jump at time zero is
then supplied by the scalar primitive. The final theorem extends the
identity to a finite family of fixed spatial profiles (the 29 wells in
our application).

No derivative of `q` is assumed. `IntervalIntegrable` hypotheses for the
vector integrals are still explicit, and must be discharged from the
bounded measurable rate and semigroup contraction in the next stage.
This file DOES NOT commute the unbounded generator with a Bochner integral.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal Convolution BigOperators

section CausalIdentity

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Causality converts the full-line regularized convolution of a
finite-horizon rate into the physical-time interval integral. This is an
identity of actual Bochner integrals, not an abstract representation
hypothesis. It also handles the endpoints `t=0` and `t=T`. -/
theorem pressure_A5_horizon_convolution_eq_interval
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T t : NNReal) (ht : t ≤ T)
    (q : ℝ → ℝ) (g : H) :
    ((pressureA5HorizonRate T q) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (pressureA5RegularizedKernel S g)) (t : ℝ) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        q s • (S (Real.toNNReal ((t : ℝ) - s)) g - g) := by
  have htR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hpoint (s : ℝ) :
      pressureA5HorizonRate T q s •
          pressureA5RegularizedKernel S g ((t : ℝ) - s) =
        (Set.Ico (0 : ℝ) (t : ℝ)).indicator
          (fun y : ℝ => q y •
            (S (Real.toNNReal ((t : ℝ) - y)) g - g)) s := by
    by_cases hs : s ∈ Set.Ico (0 : ℝ) (t : ℝ)
    · have hsT : s < (T : ℝ) := lt_of_lt_of_le hs.2 htR
      rw [pressure_A5_horizon_rate_agrees T q s hs.1 hsT,
        Set.indicator_of_mem hs]
      rfl
    · by_cases hsneg : s < 0
      · have houtside : s ∉ Set.Ico (0 : ℝ) (T : ℝ) := by
          intro hmem
          exact (not_lt_of_ge hmem.1) hsneg
        rw [pressure_A5_horizon_rate_zero_outside T q s houtside,
          zero_smul, Set.indicator_of_notMem hs]
      · have hts : (t : ℝ) ≤ s := by
          by_contra h
          exact hs ⟨le_of_not_gt hsneg, lt_of_not_ge h⟩
        have hkernel :
            pressureA5RegularizedKernel S g ((t : ℝ) - s) = 0 := by
          simp [pressureA5RegularizedKernel,
            Real.toNNReal_of_nonpos (sub_nonpos.mpr hts), S.zero_apply]
        rw [hkernel, smul_zero, Set.indicator_of_notMem hs]
  rw [MeasureTheory.convolution_lsmul]
  calc
    (∫ s : ℝ,
        pressureA5HorizonRate T q s •
          pressureA5RegularizedKernel S g ((t : ℝ) - s) ∂volume) =
        ∫ s : ℝ,
          (Set.Ico (0 : ℝ) (t : ℝ)).indicator
            (fun y : ℝ => q y •
              (S (Real.toNNReal ((t : ℝ) - y)) g - g)) s ∂volume := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ s : ℝ,
          q s • (S (Real.toNNReal ((t : ℝ) - s)) g - g)
            ∂(volume.restrict (Set.Ico (0 : ℝ) (t : ℝ))) := by
      rw [integral_indicator measurableSet_Ico]
    _ = ∫ s in (0 : ℝ)..(t : ℝ),
          q s • (S (Real.toNNReal ((t : ℝ) - s)) g - g) :=
      pressure_A5_integral_Ico_eq_interval t _

/-- A scalar primitive is unchanged when the physical input is truncated
at any later horizon. Endpoints do not matter for the interval integral. -/
theorem pressure_A5_horizon_primitive_eq_interval
    (T t : NNReal) (ht : t ≤ T) (q : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(t : ℝ), pressureA5HorizonRate T q s) =
      ∫ s in (0 : ℝ)..(t : ℝ), q s := by
  have htR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  apply intervalIntegral.integral_congr_Ioo_of_le (NNReal.coe_nonneg t)
  intro s hs
  exact pressure_A5_horizon_rate_agrees T q s hs.1.le
    (lt_of_lt_of_le hs.2 htR)

/-- The regularized continuous expression from Stages 66/67 equals the
actual forward Bochner integral for one fixed well profile. The temporal
rate need not be differentiable. The two explicitly stated integrability
hypotheses are needed solely for Bochner integral linearity. -/
theorem pressure_A5_horizon_regularized_eq_forward_onewell
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T t : NNReal) (ht : t ≤ T)
    (q : ℝ → ℝ) (g : H)
    (hforward : IntervalIntegrable
      (fun s : ℝ => q s • S (Real.toNNReal ((t : ℝ) - s)) g)
      volume 0 (t : ℝ))
    (hbase : IntervalIntegrable
      (fun s : ℝ => q s • g) volume 0 (t : ℝ)) :
    (∫ s in (0 : ℝ)..(t : ℝ), pressureA5HorizonRate T q s) • g +
      ((pressureA5HorizonRate T q) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (pressureA5RegularizedKernel S g)) (t : ℝ) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        q s • S (Real.toNNReal ((t : ℝ) - s)) g := by
  have hreg : IntervalIntegrable
      (fun s : ℝ => q s •
        (S (Real.toNNReal ((t : ℝ) - s)) g - g))
      volume 0 (t : ℝ) := by
    have heq : (fun s : ℝ => q s •
        (S (Real.toNNReal ((t : ℝ) - s)) g - g)) =
        (fun s : ℝ => q s • S (Real.toNNReal ((t : ℝ) - s)) g) -
          (fun s : ℝ => q s • g) := by
      funext s
      simp only [Pi.sub_apply, smul_sub]
    rw [heq]
    exact hforward.sub hbase
  calc
    (∫ s in (0 : ℝ)..(t : ℝ), pressureA5HorizonRate T q s) • g +
        ((pressureA5HorizonRate T q) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (pressureA5RegularizedKernel S g)) (t : ℝ) =
        (∫ s in (0 : ℝ)..(t : ℝ), q s • g) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            q s • (S (Real.toNNReal ((t : ℝ) - s)) g - g) := by
      rw [pressure_A5_horizon_convolution_eq_interval S T t ht q g,
        pressure_A5_horizon_primitive_eq_interval T t ht q,
        intervalIntegral.integral_smul_const]
    _ = ∫ s in (0 : ℝ)..(t : ℝ),
          (q s • g + q s •
            (S (Real.toNNReal ((t : ℝ) - s)) g - g)) := by
      exact (intervalIntegral.integral_add hbase hreg).symm
    _ = ∫ s in (0 : ℝ)..(t : ℝ),
          q s • S (Real.toNNReal ((t : ℝ) - s)) g := by
      apply intervalIntegral.integral_congr
      intro s hs
      change q s • g + q s • (S (Real.toNNReal ((t : ℝ) - s)) g - g) =
        q s • S (Real.toNNReal ((t : ℝ) - s)) g
      rw [smul_sub]
      abel

/-- Multiwell exact identification with the physical forward Duhamel term.
Here the source vector may represent all 29 well profiles. Finite summation
uses only the one-well Bochner identity above. No input derivative occurs. -/
theorem pressure_A5_horizon_regularized_eq_forward_multiwell
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (T t : NNReal) (ht : t ≤ T)
    (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
    (hforward : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j))
      volume 0 (t : ℝ))
    (hbase : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • f j) volume 0 (t : ℝ)) :
    ((Finset.univ : Finset (Fin m)).sum (fun (j : Fin m) =>
      (∫ s in (0 : ℝ)..(t : ℝ), pressureA5HorizonRate T (q j) s) • f j +
        ((pressureA5HorizonRate T (q j)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (pressureA5RegularizedKernel S (f j))) (t : ℝ))) =
      pressureA5ForwardDuhamel S t m f q := by
  unfold pressureA5ForwardDuhamel
  apply Finset.sum_congr rfl
  intro j hj
  exact pressure_A5_horizon_regularized_eq_forward_onewell
    S T t ht (q j) (f j) (hforward j) (hbase j)

end CausalIdentity

end ReservoirSeismicityControl
