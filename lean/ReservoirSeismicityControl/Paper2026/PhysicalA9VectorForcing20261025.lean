import ReservoirSeismicityControl.Paper2026.PhysicalA9PositiveTimeApplicability20261025
import ReservoirSeismicityControl.PaperFarNoncompactConvolutionLimit
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl A9: the missing strong projected-vector convolution route

This module does NOT rebuild the Neumann generator, well kernel, or scalar A8.
It applies Mathlib's COMPACT vector-valued convolution differentiation and
uniform-limit derivative theorem to noncompact, L²-valued physical kernels.

IMPORTANT STATUS:
* The theorem below DERIVES the strong forcing derivative, never assumes it.
* Its approximation hypotheses must be obtained from the physical projected
  kernel's vector W¹,¹ property via standard smooth approximation and the
  bounded-Q / L¹ convolution estimate. The already proved SCALAR K' bound
  is not enough. The present module does not discharge those hypotheses.
* No time derivative of Q is requested anywhere.
* All statements are conditional and contain no new axioms or sorry.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology

set_option maxHeartbeats 2000000

/-- Strong L² differentiation for the *noncompact* projected vector kernel.
The standard compact-kernel derivative is supplied directly by Mathlib; the
physical off-diagonal W¹,¹ convergence enters through VALUE convergence and
UNIFORM convergence of the derivative convolutions. Neither condition assumes
that the target convolution is differentiable. -/
theorem paper_A9_vector_convolution_rate_from_physical_approximants
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : ℝ → ℝ)
    (kernel rate : ℝ → Lp ℝ 2 μ)
    (kn : ℕ → ℝ → Lp ℝ 2 μ)
    (hq : LocallyIntegrable q volume)
    (hCompact : ∀ n : ℕ, HasCompactSupport (kn n))
    (hSmooth : ∀ n : ℕ, ContDiff ℝ 1 (kn n))
    (hValue : ∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ s : ℝ, q s • kn n (t - s))
        atTop (𝓝 (∫ s : ℝ, q s • kernel (t - s))))
    (hRateUniform : TendstoUniformly
      (fun n t => ∫ s : ℝ, q s • deriv (kn n) (t - s))
      (fun t => ∫ s : ℝ, q s • rate (t - s)) atTop)
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∫ s : ℝ, q s • kernel (τ - s))
      (∫ s : ℝ, q s • rate (t - s)) t := by
  have hCompactDerivative (n : ℕ) (τ : ℝ) :
      HasDerivAt
        (fun x : ℝ => ∫ s : ℝ, q s • kn n (x - s))
        (∫ s : ℝ, q s • deriv (kn n) (τ - s)) τ := by
    have h := HasCompactSupport.hasDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ)
      hq (hCompact n) (hSmooth n) τ
    have hEq :
        (fun x : ℝ => ∫ s : ℝ, q s • kn n (x - s)) =
          MeasureTheory.convolution q (kn n)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext x
      simp only [MeasureTheory.convolution_lsmul]
    rw [hEq]
    exact h
  exact hasDerivAt_of_tendstoUniformly hRateUniform
    (Filter.Eventually.of_forall (fun n τ => hCompactDerivative n τ))
    hValue t

/-- Finite physical wells: the vector derivative commutes with the finite
sum. This uses the actual number of well channels `Fin m`, not a new PDE.
No smoothness of any rate q_j is assumed. -/
theorem paper_A9_vector_multiwell_rate_from_physical_approximants
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (q : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ)
    (hq : ∀ j : Fin m, LocallyIntegrable (q j) volume)
    (hCompact : ∀ n j, HasCompactSupport (kn n j))
    (hSmooth : ∀ n j, ContDiff ℝ 1 (kn n j))
    (hValue : ∀ j t,
      Tendsto (fun n : ℕ => ∫ s : ℝ, q j s • kn n j (t - s))
        atTop (𝓝 (∫ s : ℝ, q j s • kernel j (t - s))))
    (hRateUniform : ∀ j, TendstoUniformly
      (fun n t => ∫ s : ℝ, q j s • deriv (kn n j) (t - s))
      (fun t => ∫ s : ℝ, q j s • rate j (t - s)) atTop)
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∑ j : Fin m,
        ∫ s : ℝ, q j s • kernel j (τ - s))
      (∑ j : Fin m, ∫ s : ℝ, q j s • rate j (t - s)) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact paper_A9_vector_convolution_rate_from_physical_approximants
    μ (q j) (kernel j) (rate j) (fun n => kn n j)
    (hq j) (fun n => hCompact n j) (fun n => hSmooth n j)
    (hValue j) (hRateUniform j) t

/-- Direct application to the strong forcing derivative premise of the
PASSED four-term physical A9 theorem. The kernel `kernel` is the causal
extension of `P A exp(-tA) f_j`, and `rate` the causal extension of
`-P A² exp(-tA) f_j`. The identities below only relate their VALUES and
causal-support integrals; they do not assume the target derivative.

`hRateCausal` is an equality between Bochner integrals, obtainable by the
already present causal-support/reflection machinery. The physical vector
W¹,¹ smooth-approximation obligation is explicitly retained above. -/
theorem paper_A9_physical_forcing_rate_from_vector_W11_approximation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (Q qext : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ)
    (hqext : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    (hCompact : ∀ n j, HasCompactSupport (kn n j))
    (hSmooth : ∀ n j, ContDiff ℝ 1 (kn n j))
    (hValue : ∀ j t,
      Tendsto (fun n : ℕ => ∫ s : ℝ, qext j s • kn n j (t - s))
        atTop (𝓝 (∫ s : ℝ, qext j s • kernel j (t - s))))
    (hRateUniform : ∀ j, TendstoUniformly
      (fun n t => ∫ s : ℝ, qext j s • deriv (kn n j) (t - s))
      (fun t => ∫ s : ℝ, qext j s • rate j (t - s)) atTop)
    (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hRateCausal : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      (∑ j : Fin m, ∫ s : ℝ,
        qext j s • rate j (t - s)) =
      (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
        (Q j s) • (-(P (second j (t - s)))))) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ∑ j : Fin m,
          ∫ s : ℝ, qext j s • kernel j (τ - s))
        (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          (Q j s) • (-(P (second j (t - s))))) t := by
  have hDerivative (t : ℝ) :=
    paper_A9_vector_multiwell_rate_from_physical_approximants
      μ qext kernel rate kn hqext hCompact hSmooth hValue hRateUniform t
  filter_upwards [hRateCausal] with t hCausal
  rw [← hCausal]
  exact hDerivative t

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_vector_convolution_rate_from_physical_approximants
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_vector_multiwell_rate_from_physical_approximants
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_forcing_rate_from_vector_W11_approximation
