import ReservoirSeismicityControl.PaperFarWeakNeumannKernel
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stage 66 — Far-region projection and weak Neumann kernel bounds

Appendix A.3 exploits separation of the observation region from the well
source. The decisive cancellation is that a far-supported observation weight
is unchanged by the far-region projection `P`, whereas the Neumann orbit
must first be projected before applying an off-diagonal estimate.

For a self-adjoint bounded linear projection `P` and `P w(t) = w(t)`, we prove

  ⟪w(t), v⟫ = ⟪w(t), P v⟫,
  |⟪w(t), v⟫| ≤ ‖w(t)‖ * ‖P v‖.

Applied to the weak Neumann kernel constructed in Stage 65, these estimates
reduce scalar kernel and kernel-derivative bounds to Hilbert-space
*projected-orbit* bounds. This is a genuine spatial-localization reduction.

No actual heat semigroup, cutoff multiplication operator, or
Davies--Gaffney estimate is constructed in this file. In particular,
`hProjectedOrbit` and `hProjectedSecond` are still substantive analytic
hypotheses to be proved for the physical Neumann semigroup. Stage 65's
positive-lag derivative assumption also remains explicit. The source
profiles need not lie in D(A) at zero lag. No derivative of Q is used.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

/-- A self-adjoint far-region operator can be moved between the two
slots of a real inner product. A weight fixed by it only sees the
far-region part of the other argument. -/
theorem paper_far_projected_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (w v : H) (hw : P w = w) :
    ⟪w, v⟫_ℝ = ⟪w, P v⟫_ℝ := by
  calc
    ⟪w, v⟫_ℝ = ⟪P w, v⟫_ℝ := by rw [hw]
    _ = ⟪w, P v⟫_ℝ := hPself w v

/-- Cauchy--Schwarz for a far-supported weight, with a localized
rather than global norm of the second factor. -/
theorem paper_far_projected_inner_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (w v : H) (hw : P w = w) :
    |⟪w, v⟫_ℝ| ≤ ‖w‖ * ‖P v‖ := by
  rw [paper_far_projected_inner P hPself w v hw]
  have hCS : ‖⟪w, P v⟫_ℝ‖ ≤ ‖w‖ * ‖P v‖ :=
    norm_inner_le_norm (𝕜 := ℝ) w (P v)
  simpa only [Real.norm_eq_abs] using hCS

/-- The Stage 65 weak-Neumann kernel is bounded by the *projected*
positive-lag semigroup orbit. No bound on the global `A T_s f_j`
is required. -/
theorem paper_far_weak_neumann_kernel_projected_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (hWeightFar : ∀ t : ℝ, P (weight t) = weight t)
    (t : ℝ) (j : Fin n) (s : ℝ) :
    |paperFarWeakNeumannKernel V E hsep weight orbit t j s| ≤
      ‖weight t‖ * ‖P (pressureWeakNeumannOperator V E hsep (orbit j s))‖ := by
  change
    |⟪weight t, pressureWeakNeumannOperator V E hsep (orbit j s)⟫_ℝ| ≤
      ‖weight t‖ * ‖P (pressureWeakNeumannOperator V E hsep (orbit j s))‖
  exact paper_far_projected_inner_bound P hPself _ _ (hWeightFar t)

/-- The corresponding bound for the lag derivative candidate
`-⟪w(t), A² T_s f_j⟫`. This does not require the source to lie in D(A²). -/
theorem paper_far_weak_neumann_kernel_rate_projected_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (weight : ℝ → H) (second : Fin n → ℝ → H)
    (hWeightFar : ∀ t : ℝ, P (weight t) = weight t)
    (t : ℝ) (j : Fin n) (s : ℝ) :
    |paperFarWeakNeumannKernelRate weight second t j s| ≤
      ‖weight t‖ * ‖P (second j s)‖ := by
  change |-(⟪weight t, second j s⟫_ℝ)| ≤
    ‖weight t‖ * ‖P (second j s)‖
  simpa only [abs_neg] using
    (paper_far_projected_inner_bound P hPself (weight t) (second j s)
      (hWeightFar t))

/-- A bounded family of far observation weights, combined with a
projected-orbit estimate, yields a uniform scalar kernel bound.
`B₀ j s` may carry the Davies--Gaffney factor
`s⁻¹ exp(-c d²/s)` on small positive lags. -/
theorem paper_far_weak_neumann_kernel_from_projected_orbit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (Lw : ℝ) (B₀ : Fin n → ℝ → ℝ)
    (hWeightFar : ∀ t : ℝ, P (weight t) = weight t)
    (hWeightNorm : ∀ t : ℝ, ‖weight t‖ ≤ Lw)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖P (pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤ B₀ j s)
    (t : ℝ) (j : Fin n) (s : ℝ) (hs : 0 < s) :
    |paperFarWeakNeumannKernel V E hsep weight orbit t j s| ≤ Lw * B₀ j s := by
  have hp := paper_far_weak_neumann_kernel_projected_bound
    V E hsep P hPself weight orbit hWeightFar t j s
  calc
    |paperFarWeakNeumannKernel V E hsep weight orbit t j s| ≤
      ‖weight t‖ * ‖P (pressureWeakNeumannOperator V E hsep (orbit j s))‖ := hp
    _ ≤ ‖weight t‖ * B₀ j s :=
      mul_le_mul_of_nonneg_left (hProjectedOrbit j s hs) (norm_nonneg _)
    _ ≤ Lw * B₀ j s :=
      mul_le_mul_of_nonneg_right (hWeightNorm t) (hB₀ j s hs)

/-- The same reduction applies to the rate kernel. The projected second
orbit, not a global operator norm of A², must be controlled. -/
theorem paper_far_weak_neumann_rate_from_projected_second
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (weight : ℝ → H) (second : Fin n → ℝ → H)
    (Lw : ℝ) (B₁ : Fin n → ℝ → ℝ)
    (hWeightFar : ∀ t : ℝ, P (weight t) = weight t)
    (hWeightNorm : ∀ t : ℝ, ‖weight t‖ ≤ Lw)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖P (second j s)‖ ≤ B₁ j s)
    (t : ℝ) (j : Fin n) (s : ℝ) (hs : 0 < s) :
    |paperFarWeakNeumannKernelRate weight second t j s| ≤ Lw * B₁ j s := by
  have hp := paper_far_weak_neumann_kernel_rate_projected_bound
    P hPself weight second hWeightFar t j s
  calc
    |paperFarWeakNeumannKernelRate weight second t j s| ≤
      ‖weight t‖ * ‖P (second j s)‖ := hp
    _ ≤ ‖weight t‖ * B₁ j s :=
      mul_le_mul_of_nonneg_left (hProjectedSecond j s hs) (norm_nonneg _)
    _ ≤ Lw * B₁ j s :=
      mul_le_mul_of_nonneg_right (hWeightNorm t) (hB₁ j s hs)

/-- Combine the Stage 65 positive-lag derivative with the spatial
projection bounds. This proves that a projected off-diagonal *H*-estimate
is sufficient for the desired scalar `K` and `K'` estimates. The analytic
semigroup properties and spatial projection still require construction. -/
theorem paper_far_weak_neumann_projected_kernel_certificates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (V : Submodule ℝ H)
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (P : H →L[ℝ] H)
    (hPself : ∀ u v : H, ⟪P u, v⟫_ℝ = ⟪u, P v⟫_ℝ)
    (weight : ℝ → H)
    (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → H)
    (Lw : ℝ) (B₀ B₁ : Fin n → ℝ → ℝ)
    (hWeightFar : ∀ t : ℝ, P (weight t) = weight t)
    (hWeightNorm : ∀ t : ℝ, ‖weight t‖ ≤ Lw)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖P (pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤ B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖P (second j s)‖ ≤ B₁ j s)
    (hOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun z => pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j s)) s) :
    ∀ (t : ℝ) (j : Fin n) (s : ℝ), 0 < s →
      HasDerivAt (paperFarWeakNeumannKernel V E hsep weight orbit t j)
        (paperFarWeakNeumannKernelRate weight second t j s) s ∧
      |paperFarWeakNeumannKernel V E hsep weight orbit t j s| ≤ Lw * B₀ j s ∧
      |paperFarWeakNeumannKernelRate weight second t j s| ≤ Lw * B₁ j s := by
  intro t j s hs
  refine ⟨?_, ?_, ?_⟩
  · exact paper_far_weak_neumann_kernel_hasDerivAt
      V E hsep weight orbit second t j s (hOrbit j s hs)
  · exact paper_far_weak_neumann_kernel_from_projected_orbit
      V E hsep P hPself weight orbit Lw B₀
      hWeightFar hWeightNorm hB₀ hProjectedOrbit t j s hs
  · exact paper_far_weak_neumann_rate_from_projected_second
      P hPself weight second Lw B₁
      hWeightFar hWeightNorm hB₁ hProjectedSecond t j s hs

end ReservoirSeismicityControl
