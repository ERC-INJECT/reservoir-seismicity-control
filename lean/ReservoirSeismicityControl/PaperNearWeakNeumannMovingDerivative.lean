import ReservoirSeismicityControl.PaperNearWeakNeumannDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Stage 63: moving near-field Neumann observation without Qdot

For a time-dependent observation weight `w(t) ∈ D(A)` and pressure path
`p(t) ∈ D(A)`, the weak Neumann symmetry identity and a difference quotient
provide the genuine product rule

  d/dt ⟪w(t), A p(t)⟫
    = ⟪w_dot(t), A p(t)⟫ + ⟪A w(t), p_dot(t)⟫.

We DO NOT assume differentiability of `A w` or `A p`. Instead we require:
* both `w` and `p` are differentiable in ambient `H = L²` at the time;
* `A p` is continuous in `H` at that time;
* the bilinear weak Neumann form is symmetric.

Continuity of `A p` is a separate analytic premise and must eventually be
proved for the physical finite-profile Duhamel solution with measurable Q.
The domain membership and time derivative of the SR cutoff weight must also
be derived from the physical SR field and its local regularity. No Qdot
appears in these statements.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter
open scoped InnerProductSpace Topology

/-- The near-field Neumann observation with a time-dependent test weight. -/
noncomputable def paperNearWeakNeumannMovingObservation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (w p : ℝ → pressureWeakNeumannDomain V E)
    (t : ℝ) : ℝ :=
  ⟪(((w t : pressureWeakNeumannDomain V E) : V) : H),
    pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ

/-- A weak product rule for an unbounded symmetric operator. Crucially, the
operator need not be differentiable on either moving argument. -/
theorem paper_near_weak_neumann_moving_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (w p : ℝ → pressureWeakNeumannDomain V E)
    (wdot pdot : H) (t : ℝ)
    (hw : HasDerivAt (fun s : ℝ => (((w s : V) : H))) wdot t)
    (hp : HasDerivAt (fun s : ℝ => (((p s : V) : H))) pdot t)
    (hpGraph : ContinuousAt (fun s : ℝ =>
      pressureWeakNeumannOperator V E hsep (p s)) t) :
    HasDerivAt (paperNearWeakNeumannMovingObservation V E hsep w p)
      (⟪wdot, pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ +
       ⟪pressureWeakNeumannOperator V E hsep (w t), pdot⟫_ℝ) t := by
  let A := pressureWeakNeumannOperator V E hsep
  let ww : ℝ → H := fun s => (((w s : V) : H))
  let pp : ℝ → H := fun s => (((p s : V) : H))
  let obs : ℝ → ℝ := paperNearWeakNeumannMovingObservation V E hsep w p
  have hsym (a b : pressureWeakNeumannDomain V E) :
      ⟪(((a : V) : H)), A b⟫_ℝ = ⟪A a, (((b : V) : H))⟫_ℝ :=
    (pressure_weak_neumann_operator_symmetric V E hsep hEsym a b).symm
  have hdiff (s : ℝ) :
      obs s - obs t =
        ⟪ww s - ww t, A (p s)⟫_ℝ +
        ⟪A (w t), pp s - pp t⟫_ℝ := by
    change ⟪ww s, A (p s)⟫_ℝ - ⟪ww t, A (p t)⟫_ℝ =
      ⟪ww s - ww t, A (p s)⟫_ℝ + ⟪A (w t), pp s - pp t⟫_ℝ
    calc
      ⟪ww s, A (p s)⟫_ℝ - ⟪ww t, A (p t)⟫_ℝ =
          ⟪ww s - ww t, A (p s)⟫_ℝ +
            (⟪ww t, A (p s)⟫_ℝ - ⟪ww t, A (p t)⟫_ℝ) := by
              rw [inner_sub_left]
              ring
      _ = ⟪ww s - ww t, A (p s)⟫_ℝ +
          ⟪A (w t), pp s - pp t⟫_ℝ := by
            rw [hsym (w t) (p s), hsym (w t) (p t), inner_sub_right]
  have hslope (s : ℝ) :
      slope obs t s =
        ⟪slope ww t s, A (p s)⟫_ℝ +
        ⟪A (w t), slope pp t s⟫_ℝ := by
    rw [slope_def_module, slope_def_module, slope_def_module]
    rw [hdiff s, smul_add, real_inner_smul_left, real_inner_smul_right]
    simp only [smul_eq_mul]
  have hwSlope : Tendsto (slope ww t) (𝓝[≠] t) (𝓝 wdot) :=
    (by simpa only [ww] using hw.tendsto_slope)
  have hpSlope : Tendsto (slope pp t) (𝓝[≠] t) (𝓝 pdot) :=
    (by simpa only [pp] using hp.tendsto_slope)
  have hAp : Tendsto (fun s : ℝ => A (p s)) (𝓝[≠] t) (𝓝 (A (p t))) :=
    hpGraph.tendsto.mono_left nhdsWithin_le_nhds
  have hfirst :
      Tendsto (fun s => ⟪slope ww t s, A (p s)⟫_ℝ)
        (𝓝[≠] t) (𝓝 ⟪wdot, A (p t)⟫_ℝ) :=
    hwSlope.inner hAp
  have hsecond :
      Tendsto (fun s => ⟪A (w t), slope pp t s⟫_ℝ)
        (𝓝[≠] t) (𝓝 ⟪A (w t), pdot⟫_ℝ) :=
    tendsto_const_nhds.inner hpSlope
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hsum := hfirst.add hsecond
  have hfun :
      (fun s : ℝ =>
        ⟪slope ww t s, A (p s)⟫_ℝ +
          ⟪A (w t), slope pp t s⟫_ℝ) = slope obs t := by
    funext s
    exact (hslope s).symm
  rw [hfun] at hsum
  exact hsum

/-- Uniform a.e. derivative bound for the time-dependent near SR weight.
The terms correspond precisely to Appendix A.3's
`⟪w_t, Ap⟫ + ⟪Aw,p_t⟫`, without an assumption on Qdot. -/
theorem paper_near_weak_neumann_moving_deriv_bound_ae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (w p : ℝ → pressureWeakNeumannDomain V E)
    (wdot pdot : ℝ → H)
    (LwRate LAp LAw LpRate : ℝ)
    (hLwRate : 0 ≤ LwRate) (hLAw : 0 ≤ LAw)
    (hw : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s : ℝ => (((w s : V) : H))) (wdot t) t)
    (hp : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s : ℝ => (((p s : V) : H))) (pdot t) t)
    (hpGraph : ∀ᵐ t ∂paperPositiveTime,
      ContinuousAt (fun s : ℝ => pressureWeakNeumannOperator V E hsep (p s)) t)
    (hwrate : ∀ᵐ t ∂paperPositiveTime, ‖wdot t‖ ≤ LwRate)
    (hAp : ∀ᵐ t ∂paperPositiveTime,
      ‖pressureWeakNeumannOperator V E hsep (p t)‖ ≤ LAp)
    (hAw : ∀ᵐ t ∂paperPositiveTime,
      ‖pressureWeakNeumannOperator V E hsep (w t)‖ ≤ LAw)
    (hprate : ∀ᵐ t ∂paperPositiveTime, ‖pdot t‖ ≤ LpRate) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (paperNearWeakNeumannMovingObservation V E hsep w p) t‖ ≤
        LwRate * LAp + LAw * LpRate := by
  filter_upwards [hw, hp, hpGraph, hwrate, hAp, hAw, hprate] with
      t hwt hpt hgraph hwd hpAb hAwb hpdb
  rw [(paper_near_weak_neumann_moving_hasDerivAt V E hsep hEsym w p
    (wdot t) (pdot t) t hwt hpt hgraph).deriv]
  have h1 :
      ‖wdot t‖ * ‖pressureWeakNeumannOperator V E hsep (p t)‖ ≤
        LwRate * LAp := by
    calc
      _ ≤ LwRate * ‖pressureWeakNeumannOperator V E hsep (p t)‖ :=
        mul_le_mul_of_nonneg_right hwd (norm_nonneg _)
      _ ≤ LwRate * LAp :=
        mul_le_mul_of_nonneg_left hpAb hLwRate
  have h2 :
      ‖pressureWeakNeumannOperator V E hsep (w t)‖ * ‖pdot t‖ ≤
        LAw * LpRate := by
    calc
      _ ≤ LAw * ‖pdot t‖ :=
        mul_le_mul_of_nonneg_right hAwb (norm_nonneg _)
      _ ≤ LAw * LpRate :=
        mul_le_mul_of_nonneg_left hpdb hLAw
  calc
    ‖⟪wdot t, pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ +
      ⟪pressureWeakNeumannOperator V E hsep (w t), pdot t⟫_ℝ‖ ≤
        ‖⟪wdot t, pressureWeakNeumannOperator V E hsep (p t)⟫_ℝ‖ +
          ‖⟪pressureWeakNeumannOperator V E hsep (w t), pdot t⟫_ℝ‖ :=
      norm_add_le _ _
    _ ≤ ‖wdot t‖ * ‖pressureWeakNeumannOperator V E hsep (p t)‖ +
      ‖pressureWeakNeumannOperator V E hsep (w t)‖ * ‖pdot t‖ :=
      add_le_add (norm_inner_le_norm (𝕜 := ℝ) _ _)
        (norm_inner_le_norm (𝕜 := ℝ) _ _)
    _ ≤ LwRate * LAp + LAw * LpRate := add_le_add h1 h2

end ReservoirSeismicityControl
