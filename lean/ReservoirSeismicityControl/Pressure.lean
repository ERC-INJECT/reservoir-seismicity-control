import ReservoirSeismicityControl.Definitions

/-!
# Appendix A.1: pressure

Proved: the scalar estimate for the mean pressure, assuming the time-integrated
net well flux bound (Assumption 5).

NOT YET FORMALIZED: the Neumann divergence-form operator, the zero-mean spectral
gap, the energy inequality, graph-norm estimates from bounded Q, Neumann heat
semigroup L² -> L∞ smoothing, and local elliptic H² regularity.

See PROOF_OBLIGATIONS.md for exact correspondences to the paper.
-/

namespace ReservoirSeismicityControl

/-- The global mean pressure is bounded by the accumulated flux estimate
    in Assumption 5. The input `net` denotes ∫₀ᵗ ∑ⱼ Qⱼ(s) ds. -/
theorem mean_pressure_bound
    (β volume Lnet u₀ : ℝ) (net : ℝ → ℝ)
    (hβ : 0 < β) (hvolume : 0 < volume)
    (hnet : ∀ t : ℝ, 0 ≤ t → |net t| ≤ Lnet) :
    ∀ t : ℝ, 0 ≤ t →
      |u₀ + net t / (β * volume)| ≤
        |u₀| + Lnet / (β * volume) := by
  have hden : 0 < β * volume := mul_pos hβ hvolume
  intro t ht
  calc
    |u₀ + net t / (β * volume)| ≤
        |u₀| + |net t / (β * volume)| := abs_add_le _ _
    _ = |u₀| + |net t| / (β * volume) := by
        rw [abs_div, abs_of_pos hden]
    _ ≤ |u₀| + Lnet / (β * volume) := by
        have hfrac :
            |net t| / (β * volume) ≤ Lnet / (β * volume) :=
          (div_le_div_iff_of_pos_right hden).2 (hnet t ht)
        linarith

/-- Scalar Grönwall comparison for the pressure energy.
    This is the equality version of the energy differential inequality in A.1.
    The PDE-specific coercivity and inequalities are not formalized here. -/
theorem pressure_energy_comparison_pending
    (E Q : ℝ → ℝ) (ω C : ℝ)
    (hω : 0 < ω) (hC : 0 ≤ C)
    (hE₀ : 0 ≤ E 0)
    (hE : ∀ t : ℝ, 0 ≤ t → 0 ≤ E t)
    (hQ : BoundedSignal Q)
    (hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt E (-ω * E t + C * (Q t) ^ 2) t) :
    BoundedSignal E := by
  obtain ⟨M, hM, hQM⟩ := hQ
  let K : ℝ := C * M ^ 2 / ω
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hωK : ω * K = C * M ^ 2 := by
    dsimp [K]
    field_simp [ne_of_gt hω]
  let F : ℝ → ℝ := fun s => Real.exp (ω * s) * (E s - K)
  have hFder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F (Real.exp (ω * t) * (C * ((Q t) ^ 2 - M ^ 2))) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (ω * s))
        (ω * Real.exp (ω * t)) t := by
      convert (Real.hasDerivAt_exp (ω * t)).comp t
        ((hasDerivAt_id t).const_mul ω) using 1
      · rfl
      · ring
    have hd : HasDerivAt F
        ((ω * Real.exp (ω * t)) * (E t - K) +
          Real.exp (ω * t) * (-ω * E t + C * (Q t) ^ 2)) t := by
      exact he.mul ((hderiv t ht).sub_const K)
    have heq :
        (ω * Real.exp (ω * t)) * (E t - K) +
          Real.exp (ω * t) * (-ω * E t + C * (Q t) ^ 2) =
            Real.exp (ω * t) * (C * ((Q t) ^ 2 - M ^ 2)) := by
      calc
        _ = Real.exp (ω * t) * (C * (Q t) ^ 2 - ω * K) := by ring
        _ = Real.exp (ω * t) * (C * ((Q t) ^ 2 - M ^ 2)) := by
          rw [hωK]
          ring
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
    have hleft : -M ≤ Q t := (abs_le.mp (hQM t ht0)).1
    have hright : Q t ≤ M := (abs_le.mp (hQM t ht0)).2
    have hsq : (Q t) ^ 2 ≤ M ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ M - Q t)
        (by linarith : 0 ≤ M + Q t)]
    rw [(hFder t ht0).deriv]
    have hneg : C * ((Q t) ^ 2 - M ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hC (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
  have hFanti : AntitoneOn F (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hFcont hFdiff hFnonpos
  have hnonneg_exp (t : ℝ) (ht : 0 ≤ t) : 1 ≤ Real.exp (ω * t) := by
    have hwt : 0 ≤ ω * t := mul_nonneg hω.le ht
    have he := Real.add_one_le_exp (ω * t)
    linarith
  refine ⟨E 0 + K, add_nonneg hE₀ hK, ?_⟩
  intro t ht
  have hbound : F t ≤ F 0 :=
    hFanti (by simp) (by simpa using ht) ht
  have hFzero : F 0 = E 0 - K := by simp [F]
  have hExp : 1 ≤ Real.exp (ω * t) := hnonneg_exp t ht
  have heval : E t ≤ E 0 + K := by
    by_cases hcase : E t ≤ K
    · linarith
    · have hv : 0 ≤ E t - K := by linarith
      have hmul : E t - K ≤ Real.exp (ω * t) * (E t - K) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp (ω * t) - 1) hv]
      rw [hFzero] at hbound
      dsimp [F] at hbound
      linarith
  rw [abs_of_nonneg (hE t ht)]
  exact heval

end ReservoirSeismicityControl
