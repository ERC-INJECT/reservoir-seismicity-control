import ReservoirSeismicityControl.PaperNearWeakNeumannMovingDerivative
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Stage 64: uniform A5 approximation implies continuity of the generator image

The Stage 63 moving-weight observation derivative requires `ContinuousAt (A ∘ p)`.
The sharp physical A5 estimate controls `A p` uniformly in time, but a
uniform norm bound alone does NOT imply continuity.

A fixed finite collection of spatial well profiles enables the following
separate approximation argument:

* Approximate each fixed profile `f_j ∈ H` by `f_j,n ∈ D(A)`.
* Establish continuity of each regularized generator image `A p_n` by
  the semigroup Duhamel formula (this is a STILL OPEN physical lemma).
* The sharp A5 estimate, together with linearity, bounds the difference
  `‖A p(t) - A p_n(t)‖` uniformly in time by the spatial approximation
  error (this is another STILL OPEN physical lemma).
* The result below proves rigorously that these two properties imply
  continuity of `A p`, with no condition on the derivative of well rates.

This module is the uniform-limit step, NOT the whole semigroup continuity
proof. It deliberately exposes the approximation estimates as hypotheses.
-/

namespace ReservoirSeismicityControl

open Filter Topology

/-- Uniform approximation in the *generator norm* transfers continuity of
regularized Neumann generator images to the limiting generator image.

The bound is global in time, as furnished by the sharp A5 estimate for the
fixed spatial well profiles. There is no `Qdot` hypothesis. -/
theorem paper_neumann_generator_continuous_of_uniform_A5_approximants
    {H : Type*} [NormedAddCommGroup H]
    (Ap : ℝ → H) (ApApprox : ℕ → ℝ → H)
    (M : ℝ) (profileError : ℕ → ℝ)
    (hApproxContinuous : ∀ n, Continuous (ApApprox n))
    (hA5Error : ∀ n t, ‖Ap t - ApApprox n t‖ ≤ M * profileError n)
    (hProfileConverges : Tendsto profileError atTop (𝓝 0)) :
    Continuous Ap := by
  apply continuous_of_uniform_approx_of_continuous
  rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
  intro ε hε
  have hErrorConverges :
      Tendsto (fun n : ℕ => M * profileError n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hProfileConverges :
        Tendsto (fun n : ℕ => M * profileError n) atTop (𝓝 (M * 0)))
  have hEventuallySmall :
      ∀ᶠ n in (atTop : Filter ℕ), M * profileError n < ε :=
    hErrorConverges.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := hEventuallySmall.exists
  refine ⟨ApApprox n, hApproxContinuous n, ?_⟩
  intro t
  simpa only [Set.mem_ofPred_eq, dist_eq_norm] using
    (hA5Error n t).trans hn.le

/-- The continuity conclusion in exactly the form needed by Stage 63. -/
theorem paper_neumann_generator_continuousAt_of_uniform_A5_approximants
    {H : Type*} [NormedAddCommGroup H]
    (Ap : ℝ → H) (ApApprox : ℕ → ℝ → H)
    (M : ℝ) (profileError : ℕ → ℝ)
    (hApproxContinuous : ∀ n, Continuous (ApApprox n))
    (hA5Error : ∀ n t, ‖Ap t - ApApprox n t‖ ≤ M * profileError n)
    (hProfileConverges : Tendsto profileError atTop (𝓝 0))
    (t : ℝ) : ContinuousAt Ap t :=
  (paper_neumann_generator_continuous_of_uniform_A5_approximants
    Ap ApApprox M profileError hApproxContinuous hA5Error
    hProfileConverges).continuousAt

end ReservoirSeismicityControl
