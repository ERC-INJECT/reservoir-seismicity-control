import ReservoirSeismicityControl.PressureWeakNeumannRealization
import ReservoirSeismicityControl.PaperRegionalPerturbationComponents

/-!
# Stage 62: near-field derivative for a fixed Neumann observation weight

For a time-independent regional pressure observation weight `w` belonging to
`D(A)`, the weak Neumann symmetry identity gives

    <w, A p(t)> = <A w, p(t)>.

Consequently, if the pressure trajectory is strongly differentiable in `L²`,
then the **physical near observation** is differentiable with

    d/dt <w,A p(t)> = <A w,p_t(t)>.

This does NOT differentiate `A p(t)` and does NOT assume `Qdot`. The proof
uses the weak Neumann operator constructed from its bilinear form, rather
than assuming a separate abstract operator symmetry axiom.

Scope: fixed weights, corresponding to the near-well contribution of
pressure observations in Appendix A.3. For SR observations the weight
contains `γ₁ R(t)` and varies with time. Its derivative additionally
contains `<w_t,A p>` and is NOT established by this module. Also still
needed: a physical construction of the cutoff weight in D(A), and the
identification of the strongly differentiable pressure path with the
Neumann semigroup mild solution for bounded measurable well rates.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- A near-field observation for the weak Neumann operator. The test weight
`w` is fixed in time and lies in the (unbounded) operator domain.
Unlike `⟪w,A p⟫` at a single time, its derivative can be evaluated from
only the `L²` pressure-rate derivative. -/
noncomputable def paperNearWeakNeumannFixedObservation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (w : pressureWeakNeumannDomain V E)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (t : ℝ) : ℝ :=
  ⟪((w : V) : H), pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ

/-- The fixed-weight near observation differentiates through `p` after
moving `A` to the fixed observation weight by weak Neumann symmetry.
`A p` is not required to have a time derivative. -/
theorem paper_near_weak_neumann_fixed_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (w : pressureWeakNeumannDomain V E)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (pdot : H) (t : ℝ)
    (hp : HasDerivAt (fun s : ℝ => (((p s : V) : H))) pdot t) :
    HasDerivAt (paperNearWeakNeumannFixedObservation V E hsep w p)
      (⟪pressureWeakNeumannOperator V E hsep w, pdot⟫_ℝ) t := by
  let A := pressureWeakNeumannOperator V E hsep
  have hEq :
      (fun s : ℝ => ⟪((w : V) : H), A (p s)⟫_ℝ) =
      (fun s : ℝ => ⟪A w, ((p s : V) : H)⟫_ℝ) := by
    funext s
    exact (pressure_weak_neumann_operator_symmetric
      V E hsep hEsym w (p s)).symm
  let L : H →L[ℝ] ℝ := innerSL ℝ (A w)
  have hComp :
      HasDerivAt (fun s : ℝ => L ((p s : V) : H)) (L pdot) t :=
    (L.hasFDerivAt.comp_hasDerivAt t hp)
  change HasDerivAt
    (fun s : ℝ => ⟪((w : V) : H), A (p s)⟫_ℝ)
    (⟪A w, pdot⟫_ℝ) t
  rw [hEq]
  simpa only [L, innerSL_apply_apply] using hComp

/-- The near observation has a uniform a.e. derivative bound when the
strong `L²` pressure rate is uniformly bounded. This is the fixed-weight
part of the paper's near-field estimate, with no hypothesis on `Qdot`. -/
theorem paper_near_weak_neumann_fixed_deriv_bound_ae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (w : pressureWeakNeumannDomain V E)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (pdot : ℝ → H)
    (Lweight Lpressure : ℝ) (hLweight : 0 ≤ Lweight)
    (hAw : ‖pressureWeakNeumannOperator V E hsep w‖ ≤ Lweight)
    (hp : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s : ℝ => (((p s : V) : H))) (pdot t) t)
    (hprate : ∀ᵐ t ∂paperPositiveTime, ‖pdot t‖ ≤ Lpressure) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (paperNearWeakNeumannFixedObservation V E hsep w p) t‖ ≤
        Lweight * Lpressure := by
  filter_upwards [hp, hprate] with t ht hbound
  rw [(paper_near_weak_neumann_fixed_hasDerivAt
    V E hsep hEsym w p (pdot t) t ht).deriv]
  calc
    ‖⟪pressureWeakNeumannOperator V E hsep w, pdot t⟫_ℝ‖ ≤
        ‖pressureWeakNeumannOperator V E hsep w‖ * ‖pdot t‖ :=
      norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ Lweight * ‖pdot t‖ :=
      mul_le_mul_of_nonneg_right hAw (norm_nonneg _)
    _ ≤ Lweight * Lpressure :=
      mul_le_mul_of_nonneg_left hbound hLweight

end ReservoirSeismicityControl
