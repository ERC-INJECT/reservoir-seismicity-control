import ReservoirSeismicityControl.PaperPhysicalSRLocalizedObservationRate
import ReservoirSeismicityControl.PaperFarWeakNeumannKernel
import Mathlib.Tactic

/-!
# M2 — actual observation-time derivative of the physical far SR kernel

The frozen-lag far kernel is
  K(t,j,s) = < P(gamma_1 R(t)), A T_s f_j >.

The existing lag-derivative lemma differentiates the semigroup lag `s`.
Here we instead differentiate the *observation time* `t` with `s` fixed.
The result includes the essential moving-weight term
  <P(gamma_1 Rdot(t)), A T_s f_j>.

Its quantitative estimate only requires the actual L2 SR rate bound,
the bounded gamma_1 multiplier, and a projected positive-lag orbit bound.
No time derivative of the well rates is used. The latter projected orbit
bound (Davies--Gaffney / analyticity) is NOT proved in this file, nor is
the full derivative of the causal convolution.

Important: the indicator cutoff P is legitimate on L2. It is NOT claimed
to map into the Neumann generator domain (generally false for a sharp
interface); that issue belongs to the *near-field* proof.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- Observation-time differentiation of the actual localized signed-SR
far kernel, at a *fixed positive or negative lag* `s`. Unlike the
existing `paper_far_weak_neumann_kernel_hasDerivAt`, this differentiates
`R(t)` and not the heat-semigroup lag. -/
theorem paper_physical_sr_far_kernel_observation_hasDerivAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (R Rdot : ℝ → Lp ℝ (2 : ENNReal) μ)
    (V : Submodule ℝ (Lp ℝ (2 : ENNReal) μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ (2 : ENNReal) μ,
      (∀ v : V, ⟪f, (v : Lp ℝ (2 : ENNReal) μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (t : ℝ) (j : Fin n) (s : ℝ)
    (hR : HasDerivAt R (Rdot t) t) :
    HasDerivAt
      (fun τ => paperFarWeakNeumannKernel V E hsep
        (paperPhysicalSRLocalizedWeight μ far hfar Kγ R) orbit τ j s)
      (⟪paperPhysicalSRLocalizedWeightRate μ far hfar Kγ Rdot t,
        pressureWeakNeumannOperator V E hsep (orbit j s)⟫_ℝ) t := by
  let P := paperFarLpProjection μ far hfar
  let w := paperPhysicalSRLocalizedWeight μ far hfar Kγ R
  let wdot := paperPhysicalSRLocalizedWeightRate μ far hfar Kγ Rdot
  let v := pressureWeakNeumannOperator V E hsep (orbit j s)
  have hw : HasDerivAt w (wdot t) t := by
    change HasDerivAt (fun τ => (P.comp Kγ) (R τ))
      ((P.comp Kγ) (Rdot t)) t
    exact (P.comp Kγ).hasFDerivAt.comp_hasDerivAt t hR
  have hinner : HasDerivAt (fun τ => (innerSL ℝ v) (w τ))
      ((innerSL ℝ v) (wdot t)) t :=
    (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hw
  have hfun :
      (fun τ => paperFarWeakNeumannKernel V E hsep w orbit τ j s) =
      (fun τ => (innerSL ℝ v) (w τ)) := by
    funext τ
    change ⟪w τ, v⟫_ℝ = ⟪v, w τ⟫_ℝ
    exact (real_inner_comm (w τ) v).symm
  change HasDerivAt
    (fun τ => paperFarWeakNeumannKernel V E hsep w orbit τ j s)
    (⟪wdot t, v⟫_ℝ) t
  rw [hfun]
  convert hinner using 1
  simp only [innerSL_apply_apply]
  exact (real_inner_comm (wdot t) v).symm

/-- The moving-weight contribution is bounded by the *far-projected*
positive-lag orbit. This is a physical SR input to the far convolution
argument; it does not assume the kernel's time derivative formula. -/
theorem paper_physical_sr_far_kernel_observation_deriv_bound_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (R Rdot : ℝ → Lp ℝ (2 : ENNReal) μ)
    (V : Submodule ℝ (Lp ℝ (2 : ENNReal) μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ (2 : ENNReal) μ,
      (∀ v : V, ⟪f, (v : Lp ℝ (2 : ENNReal) μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → pressureWeakNeumannDomain V E)
    (Cγ CR : ℝ) (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR)
    (B₀ : Fin n → ℝ → ℝ)
    (hProjected : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖paperFarLpProjection μ far hfar
          (pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤ B₀ j s) :
    ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      |deriv (fun τ => paperFarWeakNeumannKernel V E hsep
        (paperPhysicalSRLocalizedWeight μ far hfar Kγ R) orbit τ j s) t| ≤
          (Cγ * CR) * B₀ j s := by
  let P := paperFarLpProjection μ far hfar
  let wdot := paperPhysicalSRLocalizedWeightRate μ far hfar Kγ Rdot
  filter_upwards [hderiv, hrate] with t ht hrt
  intro j s hs
  let v := pressureWeakNeumannOperator V E hsep (orbit j s)
  have hwdot : ‖wdot t‖ ≤ Cγ * CR := by
    change ‖P (Kγ (Rdot t))‖ ≤ Cγ * CR
    calc
      ‖P (Kγ (Rdot t))‖ ≤ ‖Kγ (Rdot t)‖ :=
        paper_far_lp_projection_norm_le μ far hfar _
      _ ≤ ‖Kγ‖ * ‖Rdot t‖ := Kγ.le_opNorm _
      _ ≤ Cγ * ‖Rdot t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ Cγ * CR := mul_le_mul_of_nonneg_left hrt hCγ
  have hnonneg : 0 ≤ Cγ * CR :=
    (norm_nonneg (wdot t)).trans hwdot
  have hfixed : P (wdot t) = wdot t := by
    change P (P (Kγ (Rdot t))) = P (Kγ (Rdot t))
    exact paper_far_lp_projection_idempotent μ far hfar _
  have hpair : |⟪wdot t, v⟫_ℝ| ≤ ‖wdot t‖ * ‖P v‖ :=
    paper_far_projected_inner_bound P
      (paper_far_lp_projection_selfAdjoint μ far hfar)
      (wdot t) v hfixed
  have hD := paper_physical_sr_far_kernel_observation_hasDerivAt
    μ far hfar Kγ R Rdot V E hsep orbit t j s ht
  calc
    |deriv (fun τ => paperFarWeakNeumannKernel V E hsep
        (paperPhysicalSRLocalizedWeight μ far hfar Kγ R) orbit τ j s) t| =
        |⟪wdot t, v⟫_ℝ| := by
          rw [hD.deriv]
    _ ≤ ‖wdot t‖ * ‖P v‖ := hpair
    _ ≤ (Cγ * CR) * ‖P v‖ :=
      mul_le_mul_of_nonneg_right hwdot (norm_nonneg _)
    _ ≤ (Cγ * CR) * B₀ j s :=
      mul_le_mul_of_nonneg_left (hProjected j s hs) hnonneg

#print axioms ReservoirSeismicityControl.paper_physical_sr_far_kernel_observation_hasDerivAt
#print axioms ReservoirSeismicityControl.paper_physical_sr_far_kernel_observation_deriv_bound_ae

end ReservoirSeismicityControl
