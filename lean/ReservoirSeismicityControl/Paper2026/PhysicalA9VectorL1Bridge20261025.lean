import ReservoirSeismicityControl.Paper2026.PhysicalA9VectorForcing20261025
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): bounded-input L1 kernel approximation -> strong L2 rate

This is a vector-valued APPLICATION of the ALREADY VERIFIED compact convolution
and uniform-limit differentiability result. The new step is quantitative:
L1 errors of the projected vector kernels AND of their lag derivatives give
uniform errors of the convolutions, hence the required strong derivative.

The approximation of the ACTUAL separated Neumann kernel in W^{1,1} is an
external Sobolev/analytic-semigroup applicability fact cited in the manuscript;
it must be verified for the physical geometry. It is not silently assumed that
the physical forcing has the desired derivative, nor that scalar A8 bounds
imply vector L1 estimates. No derivative of well fluxes Q is requested.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology

set_option maxHeartbeats 2000000

/-- Uniformly bounded scalar inputs control Bochner convolution differences by
L1 differences of their L2-valued kernels. The integrability assumptions
make every Bochner integral well-defined rather than relying on defaults. -/
theorem paper_A9_vector_convolution_L1_error
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : ℝ → ℝ) (f g : ℝ → Lp ℝ 2 μ) (M : ℝ)
    (hQ : ∀ s : ℝ, |q s| ≤ M)
    (hfg : Integrable (fun s : ℝ => ‖f s - g s‖) volume)
    (hf : Integrable (fun s : ℝ => q s • f s) volume)
    (hg : Integrable (fun s : ℝ => q s • g s) volume) :
    ‖(∫ s : ℝ, q s • f s) - (∫ s : ℝ, q s • g s)‖ ≤
      M * ∫ s : ℝ, ‖f s - g s‖ := by
  have hdom : ∀ᵐ s : ℝ ∂volume,
      ‖q s • (f s - g s)‖ ≤ M * ‖f s - g s‖ :=
    Filter.Eventually.of_forall (fun s => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hQ s) (norm_nonneg _))
  have hbound :
      ‖∫ s : ℝ, q s • (f s - g s)‖ ≤
        M * ∫ s : ℝ, ‖f s - g s‖ := by
    simpa only [integral_const_mul] using
      (norm_integral_le_of_norm_le (hfg.const_mul M) hdom)
  have hlin :
      (∫ s : ℝ, q s • f s) - (∫ s : ℝ, q s • g s) =
        ∫ s : ℝ, q s • (f s - g s) := by
    rw [← integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [smul_sub]
  rw [hlin]
  exact hbound

/-- A uniform translated L1 error for projected vector kernels gives uniform
convergence of bounded-flux Bochner convolutions. This removes the `hValue`
and `hRateUniform` assumptions of the existing vector-convolution theorem. -/
theorem paper_A9_vector_L1_error_gives_uniform_convolution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : ℝ → ℝ) (kernel : ℝ → Lp ℝ 2 μ)
    (kn : ℕ → ℝ → Lp ℝ 2 μ)
    (M : ℝ) (hM : 0 ≤ M) (hQ : ∀ s : ℝ, |q s| ≤ M)
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 (0 : ℝ)))
    (hInt : ∀ t : ℝ,
      Integrable (fun s : ℝ => q s • kernel (t - s)) volume)
    (hIntKn : ∀ n : ℕ, ∀ t : ℝ,
      Integrable (fun s : ℝ => q s • kn n (t - s)) volume)
    (hDiffInt : ∀ n : ℕ, ∀ t : ℝ,
      Integrable (fun s : ℝ => ‖kn n (t - s) - kernel (t - s)‖) volume)
    (hDiffMass : ∀ n : ℕ, ∀ t : ℝ,
      (∫ s : ℝ, ‖kn n (t - s) - kernel (t - s)‖) ≤ err n) :
    TendstoUniformly
      (fun n t => ∫ s : ℝ, q s • kn n (t - s))
      (fun t => ∫ s : ℝ, q s • kernel (t - s)) atTop := by
  apply (Metric.tendstoUniformly_iff).2
  intro ε hε
  have herrM : Tendsto (fun n : ℕ => M * err n) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul herr)
  have hev : ∀ᶠ n : ℕ in atTop, M * err n < ε :=
    herrM.eventually_lt_const hε
  filter_upwards [hev] with n hn t
  have hbound := paper_A9_vector_convolution_L1_error μ q
    (fun s => kn n (t - s)) (fun s => kernel (t - s)) M hQ
    (hDiffInt n t) (hIntKn n t) (hInt t)
  have hmul : M * (∫ s : ℝ,
      ‖kn n (t - s) - kernel (t - s)‖) ≤ M * err n :=
    mul_le_mul_of_nonneg_left (hDiffMass n t) hM
  have hnorm :
      dist (∫ s : ℝ, q s • kn n (t - s))
        (∫ s : ℝ, q s • kernel (t - s)) ≤ M * err n := by
    simpa only [dist_eq_norm] using hbound.trans hmul
  rw [dist_comm] at hnorm
  exact lt_of_le_of_lt hnorm hn

/-- The physical A9 forcing derivative for finitely many wells, with
CONVOLUTION CONVERGENCE now PROVED from L1 kernel/rate approximation.
The remaining data are the separated projected-vector W11 approximants,
the ordinary bounded-flux integrability conditions, and zero-lag geometry.
No derivative of `q` is needed, and no `HasDerivAt` is assumed. -/
theorem paper_A9_vector_multiwell_rate_from_L1_kernel_approximation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (q : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ)
    (hq : ∀ j : Fin m, LocallyIntegrable (q j) volume)
    (hCompact : ∀ n j, HasCompactSupport (kn n j))
    (hSmooth : ∀ n j, ContDiff ℝ 1 (kn n j))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hQ : ∀ j s, |q j s| ≤ M j)
    (errValue errRate : Fin m → ℕ → ℝ)
    (herrValue : ∀ j, Tendsto (errValue j) atTop (𝓝 (0 : ℝ)))
    (herrRate : ∀ j, Tendsto (errRate j) atTop (𝓝 (0 : ℝ)))
    (hIntValue : ∀ j t,
      Integrable (fun s : ℝ => q j s • kernel j (t - s)) volume)
    (hIntKn : ∀ j n t,
      Integrable (fun s : ℝ => q j s • kn n j (t - s)) volume)
    (hIntRate : ∀ j t,
      Integrable (fun s : ℝ => q j s • rate j (t - s)) volume)
    (hIntKnRate : ∀ j n t,
      Integrable (fun s : ℝ => q j s • deriv (kn n j) (t - s)) volume)
    (hDiffValueInt : ∀ j n t,
      Integrable (fun s : ℝ =>
        ‖kn n j (t - s) - kernel j (t - s)‖) volume)
    (hDiffValueMass : ∀ j n t,
      (∫ s : ℝ, ‖kn n j (t - s) - kernel j (t - s)‖) ≤
        errValue j n)
    (hDiffRateInt : ∀ j n t,
      Integrable (fun s : ℝ =>
        ‖deriv (kn n j) (t - s) - rate j (t - s)‖) volume)
    (hDiffRateMass : ∀ j n t,
      (∫ s : ℝ, ‖deriv (kn n j) (t - s) - rate j (t - s)‖) ≤
        errRate j n)
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∑ j : Fin m,
        ∫ s : ℝ, q j s • kernel j (τ - s))
      (∑ j : Fin m, ∫ s : ℝ, q j s • rate j (t - s)) t := by
  have hValueUniform (j : Fin m) :=
    paper_A9_vector_L1_error_gives_uniform_convolution μ
      (q j) (kernel j) (fun n => kn n j) (M j) (hM j) (hQ j)
      (errValue j) (herrValue j) (hIntValue j)
      (hIntKn j) (hDiffValueInt j) (hDiffValueMass j)
  have hRateUniform (j : Fin m) :=
    paper_A9_vector_L1_error_gives_uniform_convolution μ
      (q j) (rate j) (fun n => deriv (kn n j)) (M j) (hM j) (hQ j)
      (errRate j) (herrRate j) (hIntRate j)
      (hIntKnRate j) (hDiffRateInt j) (hDiffRateMass j)
  exact paper_A9_vector_multiwell_rate_from_physical_approximants
    μ q kernel rate kn hq hCompact hSmooth
    (fun j τ => (hValueUniform j).tendsto_at τ)
    hRateUniform t


/-- Bind a proven full-line convolution derivative to the actual physical
forcing on positive time. The inputs `hForcingValue` and `hRateCausal` are
VALUE/CAUSAL identities (not differentiation hypotheses) supplied by the
physical mild-solution and positive-lag support arguments. In particular,
this lemma can consume the derivative from the preceding L1 theorem. -/
theorem paper_A9_positive_physical_forcing_rate_from_full_convolution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (forcing fullConv fullRate physicalRate : ℝ → Lp ℝ 2 μ)
    (hFullDerivative : ∀ t : ℝ,
      HasDerivAt fullConv (fullRate t) t)
    (hForcingValue : ∀ t : ℝ, 0 < t → forcing t = fullConv t)
    (hRateCausal : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      fullRate t = physicalRate t) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing (physicalRate t) t := by
  filter_upwards [hRateCausal,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with t hRate ht
  have hLocal : forcing =ᶠ[𝓝 t] fullConv := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
    exact hForcingValue τ hτ
  have hDeriv := (hFullDerivative t).congr_of_eventuallyEq hLocal
  rw [hRate] at hDeriv
  exact hDeriv

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_vector_convolution_L1_error
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_vector_L1_error_gives_uniform_convolution
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_vector_multiwell_rate_from_L1_kernel_approximation
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_positive_physical_forcing_rate_from_full_convolution
