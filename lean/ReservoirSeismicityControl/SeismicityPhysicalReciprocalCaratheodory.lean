import ReservoirSeismicityControl.SeismicityPhysicalIntegratedAEEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1 — constructive Carathéodory solution of the SR ODE

This module addresses the solution-existence/identification gate left after
`SeismicityPhysicalIntegratedAEEvolution`.

For each fixed spatial point, let
  a(t) = gamma₂(x,t) Rstar(x),
  b(t) = gamma₂(x,t) exp(-gamma₁(x) u(x,t)).
The reciprocal variable Y = exp(-gamma₁ u)/R obeys Y' = -a Y + b.

We CONSTRUCT Y by an integrating factor, establish its strong a.e. time
identity for merely interval-integrable coefficients, prove Y is positive
when b is nonnegative, and recover a positive Carathéodory solution of the
original physical nonlinear SR equation from a pressure path differentiable
a.e. in time. The proof uses no derivative of Q or of gamma₂.

This is a pointwise-in-space result. Spatial a.e.-representative and local
H²(Uj) estimates are still outstanding; they are NOT claimed here.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology

/-- Time primitive of the (possibly time-dependent) linear reciprocal coefficient. -/
noncomputable def srReciprocalPrimitive (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, a s

/-- Explicit variation-of-constants solution of `Y' = -a Y + b`.
    This is the reciprocal transformed SR density, pointwise in space. -/
noncomputable def srReciprocalExplicit
    (a b : ℝ → ℝ) (y₀ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-srReciprocalPrimitive a t) *
    (y₀ + ∫ s in (0 : ℝ)..t,
      Real.exp (srReciprocalPrimitive a s) * b s)

/-- The explicit reciprocal trajectory takes the correct initial value. -/
theorem sr_reciprocal_explicit_initial (a b : ℝ → ℝ) (y₀ : ℝ) :
    srReciprocalExplicit a b y₀ 0 = y₀ := by
  simp [srReciprocalExplicit, srReciprocalPrimitive]

/-- Positive initial data and nonnegative forcing imply strict positivity
of the explicit reciprocal solution, WITHOUT assuming any a priori
positivity or regularity of Y. -/
theorem sr_reciprocal_explicit_positive
    (a b : ℝ → ℝ) (y₀ T : ℝ)
    (hy₀ : 0 < y₀)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ b s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < srReciprocalExplicit a b y₀ t := by
  intro t ht
  have hNonneg :
      0 ≤ ∫ s in (0 : ℝ)..t,
        Real.exp (srReciprocalPrimitive a s) * b s := by
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      (hb s ⟨hs.1, le_trans hs.2 ht.2⟩)
  have hPositive :
      0 < y₀ + ∫ s in (0 : ℝ)..t,
        Real.exp (srReciprocalPrimitive a s) * b s := by
    linarith
  exact mul_pos (Real.exp_pos _) hPositive

/-- The integrating-factor construction solves the reciprocal ODE a.e.
on the interior of a finite horizon. This is a genuine scalar
Lebesgue-differentiation proof, NOT an everywhere-differentiable ODE axiom. -/
theorem sr_reciprocal_explicit_hasDerivAt_ae
    (a b : ℝ → ℝ) (y₀ T : ℝ) (hT : 0 ≤ T)
    (haInt : IntervalIntegrable a volume (0 : ℝ) T)
    (hbInt : IntervalIntegrable
      (fun s : ℝ => Real.exp (srReciprocalPrimitive a s) * b s)
      volume (0 : ℝ) T) :
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (srReciprocalExplicit a b y₀)
          (-a t * srReciprocalExplicit a b y₀ t + b t) t := by
  have haAE := haInt.ae_hasDerivAt_integral
  have hbAE := hbInt.ae_hasDerivAt_integral
  filter_upwards [haAE, hbAE] with t hat hbt
  intro ht
  have htClosed : t ∈ Set.uIcc (0 : ℝ) T := by
    rw [Set.uIcc_of_le hT]
    exact ⟨ht.1.le, ht.2.le⟩
  have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) T := by
    rw [Set.uIcc_of_le hT]
    exact ⟨le_refl _, hT⟩
  have hAprime : HasDerivAt (srReciprocalPrimitive a) (a t) t := by
    change HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..v, a s) (a t) t
    exact hat htClosed 0 hzero
  have hFprime :
      HasDerivAt
        (fun v : ℝ => ∫ s in (0 : ℝ)..v,
          Real.exp (srReciprocalPrimitive a s) * b s)
        (Real.exp (srReciprocalPrimitive a t) * b t) t :=
    hbt htClosed 0 hzero
  have hExp :
      HasDerivAt
        (fun v : ℝ => Real.exp (-srReciprocalPrimitive a v))
        (Real.exp (-srReciprocalPrimitive a t) * (-a t)) t :=
    (Real.hasDerivAt_exp _).comp t hAprime.neg
  have hSum :
      HasDerivAt
        (fun v : ℝ => y₀ + ∫ s in (0 : ℝ)..v,
          Real.exp (srReciprocalPrimitive a s) * b s)
        (Real.exp (srReciprocalPrimitive a t) * b t) t := by
    have hD := ((hasDerivAt_const t y₀).add hFprime)
    have hEq :
        ((fun _ : ℝ => y₀) +
          (fun v : ℝ => ∫ s in (0 : ℝ)..v,
            Real.exp (srReciprocalPrimitive a s) * b s)) =
        (fun v : ℝ => y₀ + ∫ s in (0 : ℝ)..v,
          Real.exp (srReciprocalPrimitive a s) * b s) := by
      funext v
      rfl
    rw [hEq] at hD
    simpa only [zero_add] using hD
  have hProd :
      HasDerivAt (srReciprocalExplicit a b y₀)
        (Real.exp (-srReciprocalPrimitive a t) * (-a t) *
           (y₀ + ∫ s in (0 : ℝ)..t,
             Real.exp (srReciprocalPrimitive a s) * b s) +
         Real.exp (-srReciprocalPrimitive a t) *
           (Real.exp (srReciprocalPrimitive a t) * b t)) t := by
    change HasDerivAt
      ((fun v : ℝ => Real.exp (-srReciprocalPrimitive a v)) *
        (fun v : ℝ => y₀ + ∫ s in (0 : ℝ)..v,
          Real.exp (srReciprocalPrimitive a s) * b s))
      (Real.exp (-srReciprocalPrimitive a t) * (-a t) *
        (y₀ + ∫ s in (0 : ℝ)..t,
          Real.exp (srReciprocalPrimitive a s) * b s) +
       Real.exp (-srReciprocalPrimitive a t) *
        (Real.exp (srReciprocalPrimitive a t) * b t)) t
    exact hExp.mul hSum
  have hExpCancel :
      Real.exp (-srReciprocalPrimitive a t) *
          Real.exp (srReciprocalPrimitive a t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hAlgebra :
      Real.exp (-srReciprocalPrimitive a t) * (-a t) *
          (y₀ + ∫ s in (0 : ℝ)..t,
            Real.exp (srReciprocalPrimitive a s) * b s) +
        Real.exp (-srReciprocalPrimitive a t) *
          (Real.exp (srReciprocalPrimitive a t) * b t) =
      -a t * srReciprocalExplicit a b y₀ t + b t := by
    dsimp only [srReciprocalExplicit]
    calc
      _ = -a t *
            (Real.exp (-srReciprocalPrimitive a t) *
              (y₀ + ∫ s in (0 : ℝ)..t,
                Real.exp (srReciprocalPrimitive a s) * b s)) +
          (Real.exp (-srReciprocalPrimitive a t) *
            Real.exp (srReciprocalPrimitive a t)) * b t := by ring
      _ = _ := by rw [hExpCancel]; ring
  rw [hAlgebra] at hProd
  exact hProd

/-- The original nonlinear SR right-hand side is recovered from a
reciprocal solution and a differentiable pressure trajectory. No
spatial smoothness or derivatives of gamma₂ are used in this identity. -/
theorem sr_physical_rate_from_reciprocal_at
    (u Y : ℝ → ℝ) (ut a b γ γ₂ Rstar t : ℝ)
    (hYnonzero : Y t ≠ 0)
    (hu : HasDerivAt u ut t)
    (hY : HasDerivAt Y (-a * Y t + b) t)
    (ha : a = γ₂ * Rstar)
    (hb : b = γ₂ * Real.exp (-γ * u t)) :
    HasDerivAt
      (fun s => Real.exp (-γ * u s) * (Y s)⁻¹)
      (-γ * (Real.exp (-γ * u t) * (Y t)⁻¹) * ut -
        γ₂ * (Real.exp (-γ * u t) * (Y t)⁻¹) *
          (Real.exp (-γ * u t) * (Y t)⁻¹ - Rstar)) t := by
  have hInner :
      HasDerivAt (fun s : ℝ => -γ * u s) (-γ * ut) t := by
    simpa only [neg_mul] using hu.const_mul (-γ)
  have hExp :
      HasDerivAt (fun s : ℝ => Real.exp (-γ * u s))
        (Real.exp (-γ * u t) * (-γ * ut)) t :=
    (Real.hasDerivAt_exp _).comp t hInner
  have hInv := hY.fun_inv hYnonzero
  have hProduct := hExp.mul hInv
  have hAlgebra :
      (Real.exp (-γ * u t) * (-γ * ut)) * (Y t)⁻¹ +
        Real.exp (-γ * u t) * (-(-a * Y t + b) / (Y t) ^ 2) =
      -γ * (Real.exp (-γ * u t) * (Y t)⁻¹) * ut -
        γ₂ * (Real.exp (-γ * u t) * (Y t)⁻¹) *
          (Real.exp (-γ * u t) * (Y t)⁻¹ - Rstar) := by
    rw [ha, hb]
    field_simp [hYnonzero]
    ring
  rw [hAlgebra] at hProduct
  exact hProduct

/-- Physical reconstructed SR trajectory from the reciprocal variable. -/
noncomputable def srPhysicalFromReciprocal
    (u : ℝ → ℝ) (γ Rstar : ℝ) (γ₂ : ℝ → ℝ) (y₀ t : ℝ) : ℝ :=
  let a : ℝ → ℝ := fun s => γ₂ s * Rstar
  let b : ℝ → ℝ := fun s => γ₂ s * Real.exp (-γ * u s)
  Real.exp (-γ * u t) * (srReciprocalExplicit a b y₀ t)⁻¹

/-- The reciprocal construction reproduces the prescribed initial
physical SR value exactly, rather than merely finding an arbitrary positive
solution. The natural initial parameter is `exp(-gamma*u(0))/R0`. -/
theorem sr_physical_reciprocal_initial_matches
    (u : ℝ → ℝ) (γ Rstar : ℝ) (γ₂ : ℝ → ℝ) (R₀ : ℝ)
    (hR₀ : R₀ ≠ 0) :
    srPhysicalFromReciprocal u γ Rstar γ₂
      (Real.exp (-γ * u 0) / R₀) 0 = R₀ := by
  change Real.exp (-γ * u 0) *
    (srReciprocalExplicit (fun s => γ₂ s * Rstar)
      (fun s => γ₂ s * Real.exp (-γ * u s))
      (Real.exp (-γ * u 0) / R₀) 0)⁻¹ = R₀
  rw [sr_reciprocal_explicit_initial]
  field_simp [hR₀, Real.exp_ne_zero]

/-- The constructive, strictly positive SR solution obeys the physical
nonlinear ODE almost everywhere in time. This theorem needs only an
a.e.-differentiable scalar pressure path and locally integrable
coefficients. It does *not* assume `HasDerivAt R` or the nonlinear
SR ODE as hypotheses. -/
theorem sr_physical_reciprocal_caratheodory_ae
    (u ut : ℝ → ℝ) (γ Rstar : ℝ) (γ₂ : ℝ → ℝ)
    (y₀ T : ℝ) (hT : 0 ≤ T) (hy₀ : 0 < y₀)
    (hγ₂ : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ γ₂ s)
    (hAInt : IntervalIntegrable
      (fun s : ℝ => γ₂ s * Rstar) volume (0 : ℝ) T)
    (hBInt : IntervalIntegrable
      (fun s : ℝ =>
        Real.exp (srReciprocalPrimitive (fun v => γ₂ v * Rstar) s) *
          (γ₂ s * Real.exp (-γ * u s))) volume (0 : ℝ) T)
    (hu : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) T → HasDerivAt u (ut t) t) :
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < srPhysicalFromReciprocal u γ Rstar γ₂ y₀ t) ∧
    (∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (srPhysicalFromReciprocal u γ Rstar γ₂ y₀)
          (-γ * srPhysicalFromReciprocal u γ Rstar γ₂ y₀ t * ut t -
            γ₂ t * srPhysicalFromReciprocal u γ Rstar γ₂ y₀ t *
              (srPhysicalFromReciprocal u γ Rstar γ₂ y₀ t - Rstar)) t) := by
  let a : ℝ → ℝ := fun s => γ₂ s * Rstar
  let b : ℝ → ℝ := fun s => γ₂ s * Real.exp (-γ * u s)
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ b s := by
    intro s hs
    exact mul_nonneg (hγ₂ s hs) (Real.exp_pos _).le
  have hYpos := sr_reciprocal_explicit_positive a b y₀ T hy₀ hb
  have hYder := sr_reciprocal_explicit_hasDerivAt_ae
    a b y₀ T hT hAInt hBInt
  constructor
  · intro t ht
    change 0 < Real.exp (-γ * u t) * (srReciprocalExplicit a b y₀ t)⁻¹
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (hYpos t ht))
  · filter_upwards [hYder, hu] with t htY htU
    intro ht
    have hYt : srReciprocalExplicit a b y₀ t ≠ 0 :=
      ne_of_gt (hYpos t ⟨ht.1.le, ht.2.le⟩)
    have hPhysical := sr_physical_rate_from_reciprocal_at
      u (srReciprocalExplicit a b y₀) (ut t) (a t) (b t)
      γ (γ₂ t) Rstar t hYt (htU ht) (htY ht) rfl rfl
    -- Expose the explicit physical reconstruction in the goal. The hypotheses
    -- `a` and `b` above are precisely the coefficients used in the definition.
    change HasDerivAt
      (fun s : ℝ => Real.exp (-γ * u s) *
        (srReciprocalExplicit a b y₀ s)⁻¹)
      (-γ * (Real.exp (-γ * u t) *
          (srReciprocalExplicit a b y₀ t)⁻¹) * ut t -
        γ₂ t * (Real.exp (-γ * u t) *
          (srReciprocalExplicit a b y₀ t)⁻¹) *
          (Real.exp (-γ * u t) *
            (srReciprocalExplicit a b y₀ t)⁻¹ - Rstar)) t
    exact hPhysical

#print axioms ReservoirSeismicityControl.sr_reciprocal_explicit_initial
#print axioms ReservoirSeismicityControl.sr_reciprocal_explicit_positive
#print axioms ReservoirSeismicityControl.sr_reciprocal_explicit_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.sr_physical_rate_from_reciprocal_at
#print axioms ReservoirSeismicityControl.sr_physical_reciprocal_initial_matches
#print axioms ReservoirSeismicityControl.sr_physical_reciprocal_caratheodory_ae

end ReservoirSeismicityControl
