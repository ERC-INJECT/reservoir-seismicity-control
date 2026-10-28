import ReservoirSeismicityControl.Seismicity
import Mathlib.Tactic

/-!
# Appendix A.2: uniform two-sided seismicity bounds

The existing `logistic_comparison_pending` theorem establishes positivity and
an upper bound for a SINGLE positive solution. Here the constants are made
UNIFORM over spatial points, which is required by the SR well-sensitivity
bounds of Appendix A.4 and the demand-controller certificates of Appendix B.

The results assume an everywhere differentiable pointwise SR trajectory.
For bounded measurable well rates, the final PDE bridge must justify an
appropriate a.e./Caratheodory version; this file does not claim to do so.
No derivatives of the well rates occur.
-/

namespace ReservoirSeismicityControl

/-- Explicit two-sided bounds for a variable-coefficient logistic ODE.
The constants depend only on uniform coefficient and initial-value bounds. -/
theorem logistic_uniform_two_sided
    (S a b : ℝ → ℝ) (smin smax amin amax bmin bmax : ℝ)
    (hsmin : 0 < smin)
    (hinitialLo : smin ≤ S 0)
    (hinitialHi : S 0 ≤ smax)
    (hamin : 0 < amin) (hbmin : 0 < bmin)
    (ha : ∀ t : ℝ, 0 ≤ t → amin ≤ a t ∧ a t ≤ amax)
    (hb : ∀ t : ℝ, 0 ≤ t → bmin ≤ b t ∧ b t ≤ bmax)
    (hode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt S (a t * S t - b t * (S t) ^ 2) t) :
    ∀ t : ℝ, 0 ≤ t →
      (smin⁻¹ + bmax / amin)⁻¹ ≤ S t ∧
        S t ≤ (min smax⁻¹ (bmin / amax))⁻¹ := by
  have hs0 : 0 < S 0 := lt_of_lt_of_le hsmin hinitialLo
  have hsmax : 0 < smax := lt_of_lt_of_le hs0 hinitialHi
  have hamax : 0 < amax := by
    have h := ha 0 (le_refl (0 : ℝ))
    linarith
  have hbmax : 0 < bmax := by
    have h := hb 0 (le_refl (0 : ℝ))
    linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < S t := by
    obtain ⟨_, _, hcomparison⟩ :=
      logistic_comparison_pending S a b amin amax bmin bmax
        hs0 hamin ha hb hbmin hode
    exact fun t ht => (hcomparison t ht).1
  let Y : ℝ → ℝ := fun t => (S t)⁻¹
  have hYpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Y t :=
    (inv_pos.mpr (hpos t ht)).le
  have hYder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt Y (-a t * Y t + b t) t := by
    have hs : S t ≠ 0 := ne_of_gt (hpos t ht)
    have hd : HasDerivAt Y
        (-(a t * S t - b t * (S t) ^ 2) / (S t) ^ 2) t := by
      simpa only [Y] using (hode t ht).fun_inv hs
    have heq :
        -(a t * S t - b t * (S t) ^ 2) / (S t) ^ 2 =
          -a t * Y t + b t := by
      dsimp [Y]
      field_simp [hs] <;> ring
    rw [← heq]
    exact hd
  have hYupper := reciprocal_upper_comparison Y a b amin bmax
    hamin hbmax.le hYpos
    (fun t ht => (ha t ht).1)
    (fun t ht => (hb t ht).2) hYder
  have hYlower := reciprocal_lower_comparison Y a b amax bmin
    hamax hbmin hYpos
    (fun t ht => (ha t ht).2)
    (fun t ht => (hb t ht).1) hYder
  have hY0lo : smax⁻¹ ≤ Y 0 := by
    change smax⁻¹ ≤ (S 0)⁻¹
    exact (inv_le_inv₀ hsmax hs0).2 hinitialHi
  have hY0hi : Y 0 ≤ smin⁻¹ := by
    change (S 0)⁻¹ ≤ smin⁻¹
    exact (inv_le_inv₀ hs0 hsmin).2 hinitialLo
  have hLpos : 0 < smin⁻¹ + bmax / amin :=
    add_pos_of_pos_of_nonneg (inv_pos.mpr hsmin)
      (div_nonneg hbmax.le hamin.le)
  have hUpos : 0 < min smax⁻¹ (bmin / amax) :=
    lt_min (inv_pos.mpr hsmax) (div_pos hbmin hamax)
  intro t ht
  have hst : 0 < S t := hpos t ht
  have hYt : 0 < Y t := inv_pos.mpr hst
  have hylimit : Y t ≤ smin⁻¹ + bmax / amin := by
    linarith [hYupper t ht, hY0hi]
  have hylower : min smax⁻¹ (bmin / amax) ≤ Y t :=
    (le_min
      (le_trans (min_le_left _ _) hY0lo)
      (min_le_right _ _)).trans (hYlower t ht)
  constructor
  · have h := (inv_le_inv₀ hLpos hYt).2 hylimit
    simpa [Y] using h
  · have h := (inv_le_inv₀ hYt hUpos).2 hylower
    simpa [Y] using h

/-- Spatially uniform logistic bounds, derived from the pointwise ODE
without assuming the bounds separately at each spatial point. -/
theorem logistic_uniform_spatial_two_sided
    {X : Type*} (S a b : X → ℝ → ℝ)
    (smin smax amin amax bmin bmax : ℝ)
    (hsmin : 0 < smin)
    (hinit : ∀ x, smin ≤ S x 0 ∧ S x 0 ≤ smax)
    (hamin : 0 < amin) (hbmin : 0 < bmin)
    (ha : ∀ x t, 0 ≤ t → amin ≤ a x t ∧ a x t ≤ amax)
    (hb : ∀ x t, 0 ≤ t → bmin ≤ b x t ∧ b x t ≤ bmax)
    (hode : ∀ x t, 0 ≤ t →
      HasDerivAt (S x) (a x t * S x t - b x t * (S x t)^2) t) :
    ∀ x t, 0 ≤ t →
      (smin⁻¹ + bmax / amin)⁻¹ ≤ S x t ∧
        S x t ≤ (min smax⁻¹ (bmin / amax))⁻¹ := by
  intro x t ht
  exact logistic_uniform_two_sided (S x) (a x) (b x)
    smin smax amin amax bmin bmax hsmin
    (hinit x).1 (hinit x).2 hamin hbmin
    (ha x) (hb x) (hode x) t ht

/-- Pass from the transformed logistic variable `S = R * exp(γ₁u)`
back to the PHYSICAL seismicity density. Only a uniform bound on `γ₁u`
is used, not a pointwise estimate on `u_t`. -/
theorem logistic_uniform_physical_SR_bounds
    {X : Type*} (S a b R z : X → ℝ → ℝ)
    (smin smax amin amax bmin bmax C : ℝ)
    (hsmin : 0 < smin)
    (hinit : ∀ x, smin ≤ S x 0 ∧ S x 0 ≤ smax)
    (hamin : 0 < amin) (hbmin : 0 < bmin)
    (ha : ∀ x t, 0 ≤ t → amin ≤ a x t ∧ a x t ≤ amax)
    (hb : ∀ x t, 0 ≤ t → bmin ≤ b x t ∧ b x t ≤ bmax)
    (hode : ∀ x t, 0 ≤ t →
      HasDerivAt (S x) (a x t * S x t - b x t * (S x t)^2) t)
    (htrans : ∀ x t, 0 ≤ t → S x t = R x t * Real.exp (z x t))
    (hz : ∀ x t, 0 ≤ t → |z x t| ≤ C) :
    ∀ x t, 0 ≤ t →
      (smin⁻¹ + bmax / amin)⁻¹ / Real.exp C ≤ R x t ∧
        R x t ≤ (min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-C) := by
  have hS := logistic_uniform_spatial_two_sided S a b
    smin smax amin amax bmin bmax hsmin hinit hamin hbmin ha hb hode
  intro x t ht
  have hbmax : 0 < bmax := by
    have h := hb x 0 (le_refl (0 : ℝ))
    linarith
  have hL : 0 < (smin⁻¹ + bmax / amin)⁻¹ := by
    apply inv_pos.mpr
    exact add_pos_of_pos_of_nonneg (inv_pos.mpr hsmin)
      (div_nonneg hbmax.le hamin.le)
  have hst := hS x t ht
  have hspos : 0 < S x t := lt_of_lt_of_le hL hst.1
  have hexp : 0 < Real.exp (z x t) := Real.exp_pos _
  have hRpos : 0 < R x t := by
    by_contra hn
    have hrle : R x t ≤ 0 := le_of_not_gt hn
    have hsle := mul_nonpos_of_nonpos_of_nonneg hrle hexp.le
    rw [← htrans x t ht] at hsle
    linarith
  have hzbounds := (abs_le.mp (hz x t ht))
  have hzExpUpper : Real.exp (z x t) ≤ Real.exp C :=
    Real.exp_le_exp.mpr hzbounds.2
  have hzExpLower : Real.exp (-C) ≤ Real.exp (z x t) :=
    Real.exp_le_exp.mpr (by linarith [hzbounds.1])
  have hprod : R x t * Real.exp (z x t) = S x t :=
    (htrans x t ht).symm
  constructor
  · apply (div_le_iff₀ (Real.exp_pos C)).2
    calc
      (smin⁻¹ + bmax / amin)⁻¹ ≤ S x t := hst.1
      _ = R x t * Real.exp (z x t) := hprod.symm
      _ ≤ R x t * Real.exp C :=
        mul_le_mul_of_nonneg_left hzExpUpper hRpos.le
  · apply (le_div_iff₀ (Real.exp_pos (-C))).2
    calc
      R x t * Real.exp (-C) ≤ R x t * Real.exp (z x t) :=
        mul_le_mul_of_nonneg_left hzExpLower hRpos.le
      _ = S x t := hprod
      _ ≤ (min smax⁻¹ (bmin / amax))⁻¹ := hst.2


/-!
## The original physical SR equation implies the transformed logistic ODE

The next two theorems use the actual physical pressure and SR trajectories,
not a separately postulated transformed logistic state. The spatial variable
is abstract so these apply pointwise on a 3D reservoir domain.
-/

/-- Exact differentiation of `S = R * exp(γ₁ u)` from the physical SR
equation. Crucially `γ₁` is time-independent and there is no `Qdot` term. -/
theorem physical_sr_logistic_hasDerivAt
    {X : Type*}
    (u ut R Rt : X → ℝ → ℝ)
    (γ₁ Rstar : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (hu : ∀ x t, 0 ≤ t → HasDerivAt (u x) (ut x t) t)
    (hR : ∀ x t, 0 ≤ t → HasDerivAt (R x) (Rt x t) t)
    (hODE : ∀ x t, 0 ≤ t →
      Rt x t = -γ₁ x * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x)) :
    ∀ x t, 0 ≤ t →
      HasDerivAt
        (fun s => R x s * Real.exp (γ₁ x * u x s))
        (γ₂ x t * Rstar x * (R x t * Real.exp (γ₁ x * u x t)) -
          γ₂ x t * Real.exp (-(γ₁ x * u x t)) *
            (R x t * Real.exp (γ₁ x * u x t)) ^ 2) t := by
  intro x t ht
  let e : ℝ := Real.exp (γ₁ x * u x t)
  have he : 0 < e := Real.exp_pos _
  have hdexp : HasDerivAt
      (fun s : ℝ => Real.exp (γ₁ x * u x s))
      (e * (γ₁ x * ut x t)) t := by
    have hinner : HasDerivAt (fun s : ℝ => γ₁ x * u x s)
        (γ₁ x * ut x t) t := (hu x t ht).const_mul (γ₁ x)
    exact (Real.hasDerivAt_exp (γ₁ x * u x t)).comp t hinner
  have hproduct := (hR x t ht).mul hdexp
  have halg := logistic_transform_algebra
    (R x t) (ut x t) (γ₁ x) (γ₂ x t) (Rstar x) e he
  have hrate :
      Rt x t * e + R x t * (e * (γ₁ x * ut x t)) =
      γ₂ x t * Rstar x * (R x t * e) -
        γ₂ x t * Real.exp (-(γ₁ x * u x t)) * (R x t * e) ^ 2 := by
    calc
      Rt x t * e + R x t * (e * (γ₁ x * ut x t)) =
          e * (-γ₁ x * R x t * ut x t -
            γ₂ x t * R x t * (R x t - Rstar x)) +
          e * (γ₁ x * ut x t * R x t) := by
            rw [hODE x t ht]
            ring
      _ = γ₂ x t * Rstar x * (R x t * e) -
          γ₂ x t * e⁻¹ * (R x t * e)^2 := halg
      _ = γ₂ x t * Rstar x * (R x t * e) -
          γ₂ x t * Real.exp (-(γ₁ x * u x t)) * (R x t * e)^2 := by
            simp only [e, Real.exp_neg]
  have hd : HasDerivAt
      (fun s => R x s * Real.exp (γ₁ x * u x s))
      (Rt x t * e + R x t * (e * (γ₁ x * ut x t))) t := by
    change HasDerivAt
      (fun s : ℝ => R x s * Real.exp (γ₁ x * u x s))
      (Rt x t * e + R x t * (e * (γ₁ x * ut x t))) t at hproduct
    exact hproduct
  rw [hrate] at hd
  exact hd

/-- Uniform positivity and boundedness of the ORIGINAL physical SR field,
obtained by combining the chain rule above with logistic comparison. The
bounds on the transformed coefficients are the immediate scalar consequences
of the bounded pressure and positive physical parameters in Assumption 3.

An everywhere differentiable pointwise solution is assumed here. Establishing
these statements for a.e. spatial point and a.e. time under measurable well
rates is a separate analytical bridge and must not be silently inferred. -/
theorem physical_sr_uniform_bounds_from_original_ode
    {X : Type*}
    (u ut R Rt : X → ℝ → ℝ)
    (γ₁ Rstar : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (smin smax amin amax bmin bmax C : ℝ)
    (hsmin : 0 < smin)
    (hinit : ∀ x, smin ≤ R x 0 * Real.exp (γ₁ x * u x 0) ∧
      R x 0 * Real.exp (γ₁ x * u x 0) ≤ smax)
    (hamin : 0 < amin) (hbmin : 0 < bmin)
    (ha : ∀ x t, 0 ≤ t →
      amin ≤ γ₂ x t * Rstar x ∧ γ₂ x t * Rstar x ≤ amax)
    (hb : ∀ x t, 0 ≤ t →
      bmin ≤ γ₂ x t * Real.exp (-(γ₁ x * u x t)) ∧
        γ₂ x t * Real.exp (-(γ₁ x * u x t)) ≤ bmax)
    (hz : ∀ x t, 0 ≤ t → |γ₁ x * u x t| ≤ C)
    (hu : ∀ x t, 0 ≤ t → HasDerivAt (u x) (ut x t) t)
    (hR : ∀ x t, 0 ≤ t → HasDerivAt (R x) (Rt x t) t)
    (hODE : ∀ x t, 0 ≤ t →
      Rt x t = -γ₁ x * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x)) :
    ∀ x t, 0 ≤ t →
      (smin⁻¹ + bmax / amin)⁻¹ / Real.exp C ≤ R x t ∧
        R x t ≤ (min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-C) := by
  have hlogistic := physical_sr_logistic_hasDerivAt
    u ut R Rt γ₁ Rstar γ₂ hu hR hODE
  exact logistic_uniform_physical_SR_bounds
    (fun x t => R x t * Real.exp (γ₁ x * u x t))
    (fun x t => γ₂ x t * Rstar x)
    (fun x t => γ₂ x t * Real.exp (-(γ₁ x * u x t)))
    R (fun x t => γ₁ x * u x t)
    smin smax amin amax bmin bmax C
    hsmin hinit hamin hbmin ha hb hlogistic
    (fun _ _ _ => rfl) hz

end ReservoirSeismicityControl
