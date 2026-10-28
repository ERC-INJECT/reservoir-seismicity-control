import ReservoirSeismicityControl.Definitions

/-!
# Appendix A.2: logistic SR dynamics

The transform S = R exp(γ₁u) satisfies a time-dependent logistic equation
S' = a S - b S². The first goal below isolates the scalar comparison argument.

This does not yet formalize the spatially dependent L∞ and local H² estimates,
the reciprocal Y=1/S, or the spatial derivatives of Y.
-/

namespace ReservoirSeismicityControl

/-- Algebraic cancellation behind the transform `S = R * exp(γ₁ * u)`
    in (A7). `e` represents the positive exponential `exp(γ₁ * u)`.
    This verifies the algebra, not yet the product/chain differentiation. -/
theorem logistic_transform_algebra
    (R ut γ₁ γ₂ Rstar e : ℝ) (he : 0 < e) :
    e * (-γ₁ * R * ut - γ₂ * R * (R - Rstar)) +
      e * (γ₁ * ut * R) =
        γ₂ * Rstar * (R * e) - γ₂ * e⁻¹ * (R * e) ^ 2 := by
  field_simp [ne_of_gt he]
  ring

/-- Algebraic identity behind the reciprocal transform `Y = 1/S`
    in (A8). Differentiability and positivity are separate obligations. -/
theorem logistic_reciprocal_algebra
    (S a b St : ℝ) (hS : S ≠ 0) (hSt : St = a * S - b * S ^ 2) :
    -St / (S ^ 2) = -a * (1 / S) + b := by
  rw [hSt]
  field_simp [hS]
  ring

/-!
## Nonvanishing from a local linear-growth estimate

If a differentiable scalar trajectory obeys `‖f'‖ ≤ K‖f‖` on a
finite interval, a zero at its right endpoint forces its initial
value to vanish. This is Grönwall uniqueness applied to reversed time.
-/

private theorem nozero_of_linear_growth
    (f f' : ℝ → ℝ) (T K : ℝ) (hT : 0 ≤ T)
    (hf0 : f 0 ≠ 0)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivAt f (f' s) s)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f' s‖ ≤ K * ‖f s‖) :
    f T ≠ 0 := by
  intro hzero
  let g : ℝ → ℝ := fun s => f (T - s)
  let gp : ℝ → ℝ := fun s => -f' (T - s)
  have hgd (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
      HasDerivAt g (gp s) s := by
    have hs' : T - s ∈ Set.Icc (0 : ℝ) T := by
      rcases hs with ⟨hs0, hsT⟩
      constructor <;> linarith
    have hlin : HasDerivAt (fun z : ℝ => T - z) (-1) s := by
      convert (hasDerivAt_const s T).sub (hasDerivAt_id s) using 1 <;>
        (first | (funext z; rfl) | ring | rfl)
    have hd := (hder (T - s) hs').comp s hlin
    convert hd using 1 <;>
      (first | (funext z; rfl) | ring | rfl)
  have hgc : ContinuousOn g (Set.Icc (0 : ℝ) T) := by
    intro s hs
    exact (hgd s hs).continuousAt.continuousWithinAt
  have hgd' : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt g (gp s) (Set.Ici s) s := by
    intro s hs
    exact (hgd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
  have hgb : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ‖gp s‖ ≤ K * ‖g s‖ := by
    intro s hs
    have hmem : T - s ∈ Set.Icc (0 : ℝ) T := by
      rcases hs with ⟨hs0, hsT⟩
      constructor <;> linarith
    simpa [gp, g, norm_neg] using hbound (T - s) hmem
  have hgzero : g 0 = 0 := by simpa [g] using hzero
  have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hgc hgd' hgzero hgb T ⟨hT, le_refl T⟩
  exact hf0 (by simpa [g] using h)

/-- The logistic right-hand side is nonpositive at or above a
    positive upper barrier. This is a pointwise sign calculation,
    not yet the time-dependent forward-invariance theorem. -/
theorem logistic_rhs_nonpos_above
    (a b aMax bMin S : ℝ)
    (ha : a ≤ aMax) (hb : bMin ≤ b)
    (hS : 0 ≤ S) (hbarrier : aMax ≤ bMin * S) :
    a * S - b * S ^ 2 ≤ 0 := by
  have h₁ : a * S ≤ aMax * S :=
    mul_le_mul_of_nonneg_right ha hS
  have h₂ : bMin * S ^ 2 ≤ b * S ^ 2 :=
    mul_le_mul_of_nonneg_right hb (sq_nonneg S)
  have h₃ : aMax * S ≤ bMin * S ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbarrier hS
    nlinarith
  linarith

/-- The logistic right-hand side is nonnegative at or below a
    positive lower barrier. -/
theorem logistic_rhs_nonneg_below
    (a b aMin bMax S : ℝ)
    (ha : aMin ≤ a) (hb : b ≤ bMax)
    (hS : 0 ≤ S) (hbarrier : bMax * S ≤ aMin) :
    0 ≤ a * S - b * S ^ 2 := by
  have h₁ : aMin * S ≤ a * S :=
    mul_le_mul_of_nonneg_right ha hS
  have h₂ : b * S ^ 2 ≤ bMax * S ^ 2 :=
    mul_le_mul_of_nonneg_right hb (sq_nonneg S)
  have h₃ : bMax * S ^ 2 ≤ aMin * S := by
    have h := mul_le_mul_of_nonneg_right hbarrier hS
    nlinarith
  linarith

/-!
## Partial logistic comparison via the reciprocal equation (A8)

Both estimates below are independent analytic statements for the linear
reciprocal equation `Y' = -a Y + b`. They assume nonnegativity of `Y`,
which is needed for the sign of the integrating-factor derivative.

They do not prove that a solution `S` of the logistic ODE remains strictly
positive. That key implication, and hence `logistic_comparison_pending`,
is still an open Lean obligation.
-/

/-- Under a positive lower bound on `a` and an upper bound on `b`,
    a nonnegative solution of `Y' = -aY + b` has a uniform upper bound.
    This is one half of the reciprocal comparison in Appendix A.2. -/
theorem reciprocal_upper_comparison
    (Y a b : ℝ → ℝ) (aMin bMax : ℝ)
    (haMin : 0 < aMin) (hbMax : 0 ≤ bMax)
    (hY : ∀ t : ℝ, 0 ≤ t → 0 ≤ Y t)
    (ha : ∀ t : ℝ, 0 ≤ t → aMin ≤ a t)
    (hb : ∀ t : ℝ, 0 ≤ t → b t ≤ bMax)
    (hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt Y (-a t * Y t + b t) t) :
    ∀ t : ℝ, 0 ≤ t → Y t ≤ Y 0 + bMax / aMin := by
  let K : ℝ := bMax / aMin
  have hK : 0 ≤ K := div_nonneg hbMax haMin.le
  have haK : aMin * K = bMax := by
    dsimp [K]
    field_simp [ne_of_gt haMin]
  let F : ℝ → ℝ := fun s => Real.exp (aMin * s) * (Y s - K)
  have hFder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F
        (Real.exp (aMin * t) *
          ((aMin - a t) * Y t + (b t - bMax))) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (aMin * s))
        (aMin * Real.exp (aMin * t)) t := by
      convert (Real.hasDerivAt_exp (aMin * t)).comp t
        ((hasDerivAt_id t).const_mul aMin) using 1
      · rfl
      · ring
    have hd : HasDerivAt F
        ((aMin * Real.exp (aMin * t)) * (Y t - K) +
          Real.exp (aMin * t) * (-a t * Y t + b t)) t := by
      exact he.mul ((hderiv t ht).sub_const K)
    have heq :
        (aMin * Real.exp (aMin * t)) * (Y t - K) +
          Real.exp (aMin * t) * (-a t * Y t + b t) =
          Real.exp (aMin * t) *
            ((aMin - a t) * Y t + (b t - bMax)) := by
      calc
        _ = Real.exp (aMin * t) *
            ((aMin - a t) * Y t + (b t - aMin * K)) := by ring
        _ = _ := by rw [haK]
    rw [heq] at hd
    exact hd
  have hFcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hFder t ht).continuousAt.continuousWithinAt
  have hFdiff : DifferentiableOn ℝ F (interior (Set.Ici (0 : ℝ))) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    exact (hFder t ht0).differentiableAt.differentiableWithinAt
  have hFnonpos : ∀ t ∈ interior (Set.Ici (0 : ℝ)), deriv F t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    have hleft : aMin - a t ≤ 0 := by linarith [ha t ht0]
    have hterm : (aMin - a t) * Y t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hleft (hY t ht0)
    have hdiff : b t - bMax ≤ 0 := by linarith [hb t ht0]
    rw [(hFder t ht0).deriv]
    have hsum : (aMin - a t) * Y t + (b t - bMax) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsum
  have hFanti : AntitoneOn F (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hFcont hFdiff hFnonpos
  intro t ht
  change Y t ≤ Y 0 + K
  have hbound : F t ≤ F 0 :=
    hFanti (by simp) (by simpa using ht) ht
  have hFzero : F 0 = Y 0 - K := by simp [F]
  have hExp : 1 ≤ Real.exp (aMin * t) := by
    have hwt : 0 ≤ aMin * t := mul_nonneg haMin.le ht
    have he := Real.add_one_le_exp (aMin * t)
    linarith
  by_cases hcase : Y t ≤ K
  · have hY0 : 0 ≤ Y 0 := hY 0 (le_refl _)
    linarith
  · have hv : 0 ≤ Y t - K := by linarith
    have hmul : Y t - K ≤ Real.exp (aMin * t) * (Y t - K) := by
      nlinarith [mul_nonneg
        (by linarith : 0 ≤ Real.exp (aMin * t) - 1) hv]
    rw [hFzero] at hbound
    dsimp [F] at hbound
    linarith

/-- Under an upper bound on `a` and a positive lower bound on `b`,
    a nonnegative solution of `Y' = -aY + b` stays above the lesser
    of its initial value and the positive equilibrium `bMin/aMax`.
    This is the other half of Appendix A.2's reciprocal comparison. -/
theorem reciprocal_lower_comparison
    (Y a b : ℝ → ℝ) (aMax bMin : ℝ)
    (haMax : 0 < aMax) (hbMin : 0 < bMin)
    (hY : ∀ t : ℝ, 0 ≤ t → 0 ≤ Y t)
    (ha : ∀ t : ℝ, 0 ≤ t → a t ≤ aMax)
    (hb : ∀ t : ℝ, 0 ≤ t → bMin ≤ b t)
    (hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt Y (-a t * Y t + b t) t) :
    ∀ t : ℝ, 0 ≤ t → min (Y 0) (bMin / aMax) ≤ Y t := by
  let K : ℝ := bMin / aMax
  have haK : aMax * K = bMin := by
    dsimp [K]
    field_simp [ne_of_gt haMax]
  let F : ℝ → ℝ := fun s => Real.exp (aMax * s) * (Y s - K)
  have hFder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F
        (Real.exp (aMax * t) *
          ((aMax - a t) * Y t + (b t - bMin))) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (aMax * s))
        (aMax * Real.exp (aMax * t)) t := by
      convert (Real.hasDerivAt_exp (aMax * t)).comp t
        ((hasDerivAt_id t).const_mul aMax) using 1
      · rfl
      · ring
    have hd : HasDerivAt F
        ((aMax * Real.exp (aMax * t)) * (Y t - K) +
          Real.exp (aMax * t) * (-a t * Y t + b t)) t := by
      exact he.mul ((hderiv t ht).sub_const K)
    have heq :
        (aMax * Real.exp (aMax * t)) * (Y t - K) +
          Real.exp (aMax * t) * (-a t * Y t + b t) =
          Real.exp (aMax * t) *
            ((aMax - a t) * Y t + (b t - bMin)) := by
      calc
        _ = Real.exp (aMax * t) *
            ((aMax - a t) * Y t + (b t - aMax * K)) := by ring
        _ = _ := by rw [haK]
    rw [heq] at hd
    exact hd
  have hFcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hFder t ht).continuousAt.continuousWithinAt
  have hFdiff : DifferentiableOn ℝ F (interior (Set.Ici (0 : ℝ))) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    exact (hFder t ht0).differentiableAt.differentiableWithinAt
  have hFnonneg : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv F t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht : 0 < t)
    have hleft : 0 ≤ aMax - a t := by linarith [ha t ht0]
    have hterm : 0 ≤ (aMax - a t) * Y t :=
      mul_nonneg hleft (hY t ht0)
    have hdiff : 0 ≤ b t - bMin := by linarith [hb t ht0]
    rw [(hFder t ht0).deriv]
    have hsum : 0 ≤ (aMax - a t) * Y t + (b t - bMin) := by linarith
    exact mul_nonneg (Real.exp_pos _).le hsum
  have hFmono : MonotoneOn F (Set.Ici (0 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hFcont hFdiff hFnonneg
  intro t ht
  change min (Y 0) K ≤ Y t
  have hbound : F 0 ≤ F t :=
    hFmono (by simp) (by simpa using ht) ht
  have hFzero : F 0 = Y 0 - K := by simp [F]
  have hExp : 1 ≤ Real.exp (aMax * t) := by
    have hwt : 0 ≤ aMax * t := mul_nonneg haMax.le ht
    have he := Real.add_one_le_exp (aMax * t)
    linarith
  by_cases hcase : K ≤ Y t
  · exact (min_le_right _ _).trans hcase
  · have hv : Y t - K ≤ 0 := by linarith
    have hmul : Real.exp (aMax * t) * (Y t - K) ≤ Y t - K := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos
        (by linarith : 0 ≤ Real.exp (aMax * t) - 1) hv]
    rw [hFzero] at hbound
    dsimp [F] at hbound
    have hY0 : Y 0 ≤ Y t := by linarith
    exact (min_le_left _ _).trans hY0


/-!
## Global positivity and upper bound for the logistic equation

The coefficients are assumed bounded and positive, as in the paper.
We first derive a compact-interval growth bound for `S` using continuity,
then rule out zeros by Grönwall uniqueness. Since `S 0 > 0`, the
intermediate value theorem gives strict positivity. Finally we apply
`reciprocal_lower_comparison` to `1 / S` to obtain an upper bound.
-/

theorem logistic_comparison_pending
    (S a b : ℝ → ℝ) (aMin aMax bMin bMax : ℝ)
    (hS0 : 0 < S 0)
    (haMin : 0 < aMin)
    (ha : ∀ t : ℝ, 0 ≤ t → aMin ≤ a t ∧ a t ≤ aMax)
    (hb : ∀ t : ℝ, 0 ≤ t → bMin ≤ b t ∧ b t ≤ bMax)
    (hbMin : 0 < bMin)
    (hode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt S (a t * S t - b t * (S t) ^ 2) t) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t →
      0 < S t ∧ S t ≤ M := by
  let Sp : ℝ → ℝ := fun u => a u * S u - b u * (S u) ^ 2
  have haMax : 0 < aMax := by
    have h := ha 0 (le_refl (0 : ℝ))
    linarith
  have hbMax : 0 < bMax := by
    have h := hb 0 (le_refl (0 : ℝ))
    linarith
  have hnonzero (T : ℝ) (hT : 0 ≤ T) : S T ≠ 0 := by
    have hScont : ContinuousOn S (Set.Icc (0 : ℝ) T) := by
      intro u hu
      exact (hode u hu.1).continuousAt.continuousWithinAt
    have hbdimage : Bornology.IsBounded (S '' Set.Icc (0 : ℝ) T) :=
      (isCompact_Icc.image_of_continuousOn hScont).isBounded
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hbdimage
    have habsS (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) : |S u| ≤ R := by
      have himg : S u ∈ S '' Set.Icc (0 : ℝ) T := ⟨u, hu, rfl⟩
      have hball := hR himg
      simpa [Metric.mem_closedBall, Real.dist_eq] using hball
    let K : ℝ := aMax + bMax * R
    have hlocal (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) :
        ‖Sp u‖ ≤ K * ‖S u‖ := by
      have hau := ha u hu.1
      have hbu := hb u hu.1
      have haabs : |a u| ≤ aMax := by
        rw [abs_of_nonneg (le_trans haMin.le hau.1)]
        exact hau.2
      have hbabs : |b u| ≤ bMax := by
        rw [abs_of_nonneg (le_trans hbMin.le hbu.1)]
        exact hbu.2
      have hc : |a u - b u * S u| ≤ K := by
        calc
          |a u - b u * S u| ≤ |a u| + |b u * S u| := by
            simpa using (abs_sub_le (a u) 0 (b u * S u))
          _ = |a u| + |b u| * |S u| := by rw [abs_mul]
          _ ≤ aMax + bMax * R :=
            add_le_add haabs (mul_le_mul hbabs (habsS u hu) (abs_nonneg _) hbMax.le)
      have hf : Sp u = (a u - b u * S u) * S u := by dsimp [Sp]; ring
      rw [hf, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    exact nozero_of_linear_growth S Sp T K hT (ne_of_gt hS0)
      (by intro u hu; exact hode u hu.1) hlocal
  have hSpos (T : ℝ) (hT : 0 ≤ T) : 0 < S T := by
    by_contra hnot
    have hle : S T ≤ 0 := le_of_not_gt hnot
    have hScont : ContinuousOn S (Set.Icc (0 : ℝ) T) := by
      intro u hu
      exact (hode u hu.1).continuousAt.continuousWithinAt
    have h0 : (0 : ℝ) ∈ Set.Icc (S T) (S 0) := ⟨hle, hS0.le⟩
    obtain ⟨u, hu, hSu⟩ := (intermediate_value_Icc' hT hScont) h0
    exact (hnonzero u hu.1) hSu
  let Y : ℝ → ℝ := fun t => (S t)⁻¹
  have hYpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Y t := by
    exact (inv_pos.mpr (hSpos t ht)).le
  have hYder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt Y (-a t * Y t + b t) t := by
    have hs : S t ≠ 0 := ne_of_gt (hSpos t ht)
    have h₁ : HasDerivAt Y
        (-(a t * S t - b t * (S t) ^ 2) / (S t) ^ 2) t := by
      simpa only [Y] using (hode t ht).fun_inv hs
    have h₂ :
        -(a t * S t - b t * (S t) ^ 2) / (S t) ^ 2 =
          -a t * Y t + b t := by
      dsimp [Y]
      field_simp [hs] <;> ring
    rw [← h₂]
    exact h₁
  have hYlower := reciprocal_lower_comparison Y a b aMax bMin
    haMax hbMin hYpos
    (fun t ht => (ha t ht).2)
    (fun t ht => (hb t ht).1) hYder
  let m : ℝ := min (Y 0) (bMin / aMax)
  have hm : 0 < m := by
    exact lt_min (by simpa [Y] using inv_pos.mpr hS0) (div_pos hbMin haMax)
  refine ⟨m⁻¹, inv_pos.mpr hm, ?_⟩
  intro t ht
  constructor
  · exact hSpos t ht
  · have hy : m ≤ Y t := hYlower t ht
    have hmult : m * S t ≤ 1 := by
      apply (le_div_iff₀ (hSpos t ht)).mp
      simpa [m, Y, one_div] using hy
    have hlt : S t ≤ 1 / m := (le_div_iff₀ hm).mpr (by linarith)
    simpa [one_div] using hlt

end ReservoirSeismicityControl
