import ReservoirSeismicityControl.Definitions

/-!
# Appendix A.3: regional perturbation derivatives

The key obligation is to prove an L∞ bound on the derivative of
J(t)=⟨w(t), A p(t)⟩ without assuming any L∞ bound on Q'.

Required structure:
* near wells: a smooth cutoff ζ, ζw ∈ D(A), and weak differentiation;
* far wells: positive support separation and Davies--Gaffney estimates
  for A exp(-sA), A² exp(-sA);
* convolution: integration by parts eliminates Q' and uses K(0)=0;
* density/continuity: extend from smooth Q to bounded continuous Q.

This file contains a concrete subgoal for the integrable small-time kernel.
The full semigroup implementation requires formalized Neumann operators,
which Mathlib does not automatically provide in the required form.
-/

namespace ReservoirSeismicityControl

/-- Elementary quadratic lower bound for the exponential. It is the only
    analytic growth estimate needed for the kernel-integrability subgoal. -/
private theorem exp_quadratic_lower (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / 4 ≤ Real.exp x := by
  have he : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2)
    linarith
  have he2 : (1 + x / 2) ^ 2 ≤ (Real.exp (x / 2)) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ Real.exp (x / 2) - (1 + x / 2))
      (by linarith : 0 ≤ Real.exp (x / 2) + (1 + x / 2))]
  have hexp : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at he2
  nlinarith

/-- The short-time Davies--Gaffney kernel model `s⁻² exp(-c d²/s)`
    is integrable whenever the separation `d` and constant `c` are positive.
    This does NOT formalize the off-diagonal operator estimate itself. -/
theorem far_kernel_small_time_integrable_pending
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (s ^ 2)⁻¹ * Real.exp (-(c * d ^ 2) / s))
      (Set.Ioc (0 : ℝ) 1) := by
  let a : ℝ := c * d ^ 2
  have ha : 0 < a := mul_pos hc (sq_pos_of_pos hd)
  let f : ℝ → ℝ := fun s => (s ^ 2)⁻¹ * Real.exp (-(a / s))
  have hf_meas : Measurable f := by
    dsimp [f]
    fun_prop
  have hf_bound (s : ℝ) (hs : 0 < s) : ‖f s‖ ≤ 4 / a ^ 2 := by
    let x : ℝ := a / s
    have hx : 0 < x := div_pos ha hs
    have hlow : x ^ 2 / 4 ≤ Real.exp x := exp_quadratic_lower x hx.le
    have hmul := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-x)).le
    have hexp : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hexp] at hmul
    have hnonneg : 0 ≤ f s := by
      dsimp [f]
      positivity
    have hcalc : f s ≤ 4 / a ^ 2 := by
      calc
        f s = (4 / a ^ 2) * ((x ^ 2 / 4) * Real.exp (-x)) := by
          dsimp [f, x]
          field_simp [ne_of_gt ha, ne_of_gt hs]
        _ ≤ (4 / a ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 4 / a ^ 2 := by ring
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hcalc
  have hfin : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by
    simp
  have hae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖f s‖ ≤ 4 / a ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioc)] with s hs
    exact hf_bound s hs.1
  have hf_int : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.IntegrableOn.of_bound hfin hf_meas.aestronglyMeasurable.restrict
      (4 / a ^ 2) hae
  simpa only [f, a, neg_div] using hf_int

end ReservoirSeismicityControl
