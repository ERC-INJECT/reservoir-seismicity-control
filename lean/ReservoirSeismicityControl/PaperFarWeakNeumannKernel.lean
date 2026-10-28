import ReservoirSeismicityControl.PaperFarCausalConvolutionBridge
import ReservoirSeismicityControl.PressureWeakNeumannRealization
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stage 65: frozen far-field kernel from the weak Neumann operator

The far-field kernel of Appendix A.3 has the form
  K_{j,t}(s) = < w_far(t), A exp(-s A) f_j >,
where t is the observation time and s > 0 is the semigroup lag.

Unlike an arbitrary scalar K, the kernel below is paired with the *actual
weak-form operator* constructed in `PressureWeakNeumannRealization`.
The domain-valued orbit represents `exp(-s A) f_j` only for positive s.
Its arbitrary extension to s ≤ 0 is not required to represent the heat flow,
since the well source f_j need not belong to D(A).

The main new result is the kernel's lag derivative under a strong
semigroup-orbit derivative in the ambient Hilbert space:
  d/ds K_{j,t}(s) = -< w_far(t), A² exp(-s A) f_j >.
The weight is frozen at observation time t during this differentiation.

This stage does not construct the Neumann heat semigroup nor prove
regularity of its orbits. It does not prove the off-diagonal estimates,
the physical observation derivative identity (A11), or the connection
between the weak form and the concrete ReservoirSeismicityControl tensor coefficient.
Those obligations remain explicit. No derivative of Q is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- The frozen-time far kernel based on the weak Neumann operator A.
`orbit j s` is intended to be `exp(-s A) f_j` only for s>0.
Outside positive lags it is an arbitrary domain-valued extension.
`weight t` is the far-field observation weight at fixed time t. -/
noncomputable def paperFarWeakNeumannKernel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (t : ℝ) (j : Fin n) (s : ℝ) : ℝ :=
  (innerSL ℝ (weight t))
    (pressureWeakNeumannOperator V E hsep (orbit j s))

/-- Candidate lag derivative of the physical kernel. The supplied
`second j s` represents `A² exp(-s A) f_j` in H, not a bounded A² on H. -/
noncomputable def paperFarWeakNeumannKernelRate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (weight : ℝ → H) (second : Fin n → ℝ → H)
    (t : ℝ) (j : Fin n) (s : ℝ) : ℝ :=
  -((innerSL ℝ (weight t)) (second j s))

/-- Differentiation of the frozen observation kernel in the semigroup lag.
The only analytic premise is the strong H-valued derivative of A applied
to the orbit, as supplied by an analytic Neumann semigroup. It does not
require a derivative of the well flux Q. -/
theorem paper_far_weak_neumann_kernel_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → H)
    (t : ℝ) (j : Fin n) (s : ℝ)
    (hOrbit : HasDerivAt
      (fun z => pressureWeakNeumannOperator V E hsep (orbit j z))
      (-(second j s)) s) :
    HasDerivAt (paperFarWeakNeumannKernel V E hsep weight orbit t j)
      (paperFarWeakNeumannKernelRate weight second t j s) s := by
  have h := ((innerSL ℝ (weight t)).hasFDerivAt.comp_hasDerivAt s hOrbit)
  change HasDerivAt
    (fun z => (innerSL ℝ (weight t))
      (pressureWeakNeumannOperator V E hsep (orbit j z)))
    (-((innerSL ℝ (weight t)) (second j s))) s
  simpa only [Function.comp_def, map_neg] using h

/-- The rate above differentiates only with respect to the lag.
This form is useful when applying the result simultaneously to all wells,
at any fixed observation time, and at positive semigroup lags. -/
theorem paper_far_weak_neumann_kernel_hasDerivAt_pos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → H)
    (hOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun z => pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j s)) s) :
    ∀ (t : ℝ) (j : Fin n) (s : ℝ), 0 < s →
      HasDerivAt (paperFarWeakNeumannKernel V E hsep weight orbit t j)
        (paperFarWeakNeumannKernelRate weight second t j s) s := by
  intro t j s hs
  exact paper_far_weak_neumann_kernel_hasDerivAt
    V E hsep weight orbit second t j s (hOrbit j s hs)

/-- Stage 64's causal kernel bound, specialized to the weak Neumann
operator kernel and its derived lag rate. The off-diagonal L¹ bound and
the PDE-to-far-observation derivative formula remain named premises.
The identities `K = <w,A T_s f>` and `K' = -<w,A² T_s f>` are no longer
independent scalar-kernel definitions. -/
theorem paper_far_weak_neumann_causal_derivative_bound_ae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → H)
    (far initial : ℝ → ℝ) (Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ) (Linit : ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hinit : ∀ᵐ t ∂paperPositiveTime, |initial t| ≤ Linit)
    (hKNow : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      |paperFarWeakNeumannKernel V E hsep weight orbit t j t| ≤ K₀ j)
    (hk : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      Integrable
        (fun s => paperFarWeakNeumannKernelRate weight second t j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hkMass : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      (∫ s in Set.Ioc (0 : ℝ) t,
        |paperFarWeakNeumannKernelRate weight second t j (t - s)|) ≤ K₁ j)
    (hfarDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt far
        (paperFarCausalKernelRate t (initial t)
          (paperFarWeakNeumannKernel V E hsep weight orbit t)
          (paperFarWeakNeumannKernelRate weight second t) Q) t) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤
        Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j) := by
  exact paper_far_actual_derivative_bound_from_causal_kernel_ae
    far initial
    (fun t => paperFarWeakNeumannKernel V E hsep weight orbit t)
    (fun t => paperFarWeakNeumannKernelRate weight second t)
    Q M K₀ K₁ Linit hM hK₀ hQ hinit hKNow hk hkMass hfarDeriv


/-- Combined Stage 65 certificate: a strong positive-lag derivative of the
Neumann orbit yields the *actual frozen-kernel derivative*, and the
Stage 64 causal estimate bounds the physical far observation when (A11)
and the off-diagonal kernel estimates are available. The second conjunct
is a conditional physical-observation estimate, not an independent proof
of (A11). In particular, there is no hypothesis on Q' or Q''. -/
theorem paper_far_weak_neumann_kernel_and_observation_certificates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → H)
    (far initial : ℝ → ℝ) (Q : Fin n → ℝ → ℝ)
    (M K₀ K₁ : Fin n → ℝ) (Linit : ℝ)
    (hOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun z => pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j s)) s)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hK₀ : ∀ j : Fin n, 0 ≤ K₀ j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hinit : ∀ᵐ t ∂paperPositiveTime, |initial t| ≤ Linit)
    (hKNow : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      |paperFarWeakNeumannKernel V E hsep weight orbit t j t| ≤ K₀ j)
    (hk : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      Integrable
        (fun s => paperFarWeakNeumannKernelRate weight second t j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hkMass : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n,
      (∫ s in Set.Ioc (0 : ℝ) t,
        |paperFarWeakNeumannKernelRate weight second t j (t - s)|) ≤ K₁ j)
    (hfarDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt far
        (paperFarCausalKernelRate t (initial t)
          (paperFarWeakNeumannKernel V E hsep weight orbit t)
          (paperFarWeakNeumannKernelRate weight second t) Q) t) :
    (∀ (t : ℝ) (j : Fin n) (s : ℝ), 0 < s →
      HasDerivAt (paperFarWeakNeumannKernel V E hsep weight orbit t j)
        (paperFarWeakNeumannKernelRate weight second t j s) s) ∧
    (∀ᵐ t ∂paperPositiveTime,
      ‖deriv far t‖ ≤ Linit + ∑ j : Fin n, M j * (K₀ j + K₁ j)) := by
  constructor
  · exact paper_far_weak_neumann_kernel_hasDerivAt_pos
      V E hsep weight orbit second hOrbit
  · exact paper_far_weak_neumann_causal_derivative_bound_ae
      V E hsep weight orbit second far initial Q M K₀ K₁ Linit
      hM hK₀ hQ hinit hKNow hk hkMass hfarDeriv

end ReservoirSeismicityControl
