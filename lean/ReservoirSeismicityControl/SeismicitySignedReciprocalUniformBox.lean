import ReservoirSeismicityControl.SeismicitySignedModel
import ReservoirSeismicityControl.Seismicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# M1: Time-uniform reciprocal bounds for the constructed signed SR solution

This module closes a missing comparison interface in Appendix A.2:
the explicit Carathéodory reciprocal solution previously had positivity and
an a.e. evolution equation, but no time-independent two-sided bounds.

For coefficients continuous in time at a fixed spatial point, we prove that
*the explicit solution itself* is differentiable at every time. We then
apply the already-verified scalar comparison theorems to this constructed
solution to deduce a uniform positive box. This is the pointwise prerequisite
for the subsequent local H²(U_j) spatial derivative estimates.

IMPORTANT: time continuity here is an explicit premise. Its a.e.-spatial
instantiation from the physical L² pressure solution and gamma₂ regularity
is NOT established in this module. No assumption on Qdot is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology

/-- Continuity of the time coefficient upgrades the *constructed* reciprocal
solution from a.e. differentiable to differentiable at every time. -/
theorem sr_reciprocal_explicit_hasDerivAt_continuous
    (a b : ℝ → ℝ) (y₀ t : ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    HasDerivAt (srReciprocalExplicit a b y₀)
      (-a t * srReciprocalExplicit a b y₀ t + b t) t := by
  have hAprime : HasDerivAt (srReciprocalPrimitive a) (a t) t := by
    change HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..v, a s) (a t) t
    exact intervalIntegral.integral_hasDerivAt_right
      (ha.intervalIntegrable 0 t) (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
  have hAc : Continuous (srReciprocalPrimitive a) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hv : HasDerivAt (srReciprocalPrimitive a) (a v) v := by
      change HasDerivAt (fun w : ℝ => ∫ s in (0 : ℝ)..w, a s) (a v) v
      exact intervalIntegral.integral_hasDerivAt_right
        (ha.intervalIntegrable 0 v) (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
    exact hv.continuousAt
  have hBc : Continuous (fun s : ℝ =>
      Real.exp (srReciprocalPrimitive a s) * b s) :=
    (Real.continuous_exp.comp hAc).mul hb
  have hFprime :
      HasDerivAt
        (fun v : ℝ => ∫ s in (0 : ℝ)..v,
          Real.exp (srReciprocalPrimitive a s) * b s)
        (Real.exp (srReciprocalPrimitive a t) * b t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hBc.intervalIntegrable 0 t) (hBc.stronglyMeasurableAtFilter _ _)
      hBc.continuousAt
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

/-- Uniform positive lower and upper bounds on the *constructed*
reciprocal solution, independent of the time horizon. These are
sufficient to control the coefficients of the local spatial H² proof.
The bound is derived, not assumed. -/
theorem sr_reciprocal_explicit_uniform_box
    (a b : ℝ → ℝ) (y₀ aMin aMax bMin bMax : ℝ)
    (hy₀ : 0 < y₀) (haMin : 0 < aMin) (hbMin : 0 < bMin)
    (ha : Continuous a) (hb : Continuous b)
    (haBounds : ∀ t : ℝ, 0 ≤ t → aMin ≤ a t ∧ a t ≤ aMax)
    (hbBounds : ∀ t : ℝ, 0 ≤ t → bMin ≤ b t ∧ b t ≤ bMax) :
    ∀ t : ℝ, 0 ≤ t →
      min y₀ (bMin / aMax) ≤ srReciprocalExplicit a b y₀ t ∧
      srReciprocalExplicit a b y₀ t ≤ y₀ + bMax / aMin := by
  have haMax : 0 < aMax := by
    have h := haBounds 0 (le_refl (0 : ℝ))
    linarith
  have hbMax : 0 ≤ bMax := by
    have h := hbBounds 0 (le_refl (0 : ℝ))
    linarith
  have hYpos : ∀ t : ℝ, 0 ≤ t →
      0 ≤ srReciprocalExplicit a b y₀ t := by
    intro t ht
    have hY := sr_reciprocal_explicit_positive a b y₀ t hy₀
      (fun v hv => le_trans hbMin.le (hbBounds v hv.1).1)
      t ⟨ht, le_refl t⟩
    exact hY.le
  have hYderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (srReciprocalExplicit a b y₀)
        (-a t * srReciprocalExplicit a b y₀ t + b t) t := by
    intro t _
    exact sr_reciprocal_explicit_hasDerivAt_continuous a b y₀ t ha hb
  have hLower := reciprocal_lower_comparison
    (srReciprocalExplicit a b y₀) a b aMax bMin haMax hbMin
    hYpos (fun t ht => (haBounds t ht).2)
    (fun t ht => (hbBounds t ht).1) hYderiv
  have hUpper := reciprocal_upper_comparison
    (srReciprocalExplicit a b y₀) a b aMin bMax haMin hbMax
    hYpos (fun t ht => (haBounds t ht).1)
    (fun t ht => (hbBounds t ht).2) hYderiv
  intro t ht
  constructor
  · simpa only [sr_reciprocal_explicit_initial] using hLower t ht
  · simpa only [sr_reciprocal_explicit_initial] using hUpper t ht

/-- The uniform reciprocal lower barrier is *strictly positive*.
This is the separation from zero needed for the H² reciprocal calculus. -/
theorem sr_reciprocal_uniform_lower_positive
    (y₀ aMax bMin : ℝ)
    (hy₀ : 0 < y₀) (haMax : 0 < aMax) (hbMin : 0 < bMin) :
    0 < min y₀ (bMin / aMax) := by
  exact lt_min hy₀ (div_pos hbMin haMax)


/-- Spatially indexed physical coefficients, with one common time-uniform box.
In the reservoir application `X` is the spatial domain (or an a.e. subset).
The hypotheses are the physical bounds of Assumption 3 plus continuity in
time at each selected spatial point; no uniform-in-x derivative is assumed.
The result is the *same box at every spatial point* and every `t ≥ 0`. -/
theorem sr_signed_physical_reciprocal_uniform_spatial_box
    {X : Type*}
    (u : X → ℝ → ℝ) (gamma1 Rstar : X → ℝ)
    (gamma2 : X → ℝ → ℝ) (s : ℝ) (y₀ : X → ℝ)
    (yMin yMax aMin aMax bMin bMax : ℝ)
    (hyMin : 0 < yMin) (haMin : 0 < aMin) (hbMin : 0 < bMin)
    (hyBounds : ∀ x, yMin ≤ y₀ x ∧ y₀ x ≤ yMax)
    (haCont : ∀ x, Continuous (fun t => gamma2 x t * Rstar x))
    (hbCont : ∀ x, Continuous
      (fun t => gamma2 x t * Real.exp (s * gamma1 x * u x t)))
    (haBounds : ∀ x t, 0 ≤ t →
      aMin ≤ gamma2 x t * Rstar x ∧
        gamma2 x t * Rstar x ≤ aMax)
    (hbBounds : ∀ x t, 0 ≤ t →
      bMin ≤ gamma2 x t * Real.exp (s * gamma1 x * u x t) ∧
        gamma2 x t * Real.exp (s * gamma1 x * u x t) ≤ bMax) :
    ∀ x t, 0 ≤ t →
      min yMin (bMin / aMax) ≤
        srReciprocalExplicit (fun v => gamma2 x v * Rstar x)
          (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
          (y₀ x) t ∧
      srReciprocalExplicit (fun v => gamma2 x v * Rstar x)
          (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
          (y₀ x) t ≤ yMax + bMax / aMin := by
  intro x t ht
  have hyPos : 0 < y₀ x := lt_of_lt_of_le hyMin (hyBounds x).1
  have hbox := sr_reciprocal_explicit_uniform_box
    (fun v => gamma2 x v * Rstar x)
    (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
    (y₀ x) aMin aMax bMin bMax
    hyPos haMin hbMin (haCont x) (hbCont x)
    (haBounds x) (hbBounds x) t ht
  constructor
  · exact (le_min
      ((min_le_left yMin (bMin / aMax)).trans (hyBounds x).1)
      (min_le_right yMin (bMin / aMax))).trans hbox.1
  · exact hbox.2.trans (by linarith [(hyBounds x).2])

#print axioms ReservoirSeismicityControl.sr_reciprocal_explicit_hasDerivAt_continuous
#print axioms ReservoirSeismicityControl.sr_reciprocal_explicit_uniform_box
#print axioms ReservoirSeismicityControl.sr_reciprocal_uniform_lower_positive
#print axioms ReservoirSeismicityControl.sr_signed_physical_reciprocal_uniform_spatial_box

end ReservoirSeismicityControl
