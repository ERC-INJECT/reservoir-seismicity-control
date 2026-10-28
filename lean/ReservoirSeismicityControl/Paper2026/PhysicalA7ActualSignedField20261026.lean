import ReservoirSeismicityControl.SeismicitySignedReciprocalUniformBox
import ReservoirSeismicityControl.SeismicityPhysicalReciprocalCaratheodory
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# The ACTUAL signed reciprocal and seismicity field, not abstract L² data

The spatially indexed physical scalar Carathéodory solution is defined here
rather than introduced as an arbitrary `Yphysical` accompanied by `hScalar`.
Its L² class and the corresponding SR class are constructed by `MemLp.toLp`.
The only external analytic hypothesis is ordinary measurability/L² integrability
of these explicit scalar fields on the bounded local region. This integrability
is a consequence of the spatial box and finite volume, but is not claimed to
be established in this file. No H² regularity of Y or R is assumed or proved.

This is a *physical field identification prerequisite*, not the completion of
A7 H². It will replace `hScalar` and the arbitrary local L² fields when the
actual weak Sobolev kernel and Fubini identifications are completed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- A7's actual signed reciprocal, pointwise in space and time. -/
noncomputable def physicalSignedYScalar
    {X : Type*} (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (x : X) (t : ℝ) : ℝ :=
  ReservoirSeismicityControl.srReciprocalExplicit
    (fun v => gamma2 x v * Rstar x)
    (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
    (Real.exp (s * gamma1 x * u x 0) / R0 x) t

/-- The *same* physical seismicity-rate field recovered from the signed
reciprocal: Y = exp(s γ₁ u)/R. This fixes the manuscript sign convention. -/
noncomputable def physicalSignedRScalar
    {X : Type*} (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (x : X) (t : ℝ) : ℝ :=
  Real.exp (s * gamma1 x * u x t) *
    (physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)⁻¹

/-- At t=0, the constructed signed reciprocal matches the manuscript's
physical initial reciprocal exactly. -/
theorem physical_signed_Y_initial
    {X : Type*} (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ) (x : X) :
    physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x 0 =
      Real.exp (s * gamma1 x * u x 0) / R0 x := by
  simp only [physicalSignedYScalar, ReservoirSeismicityControl.sr_reciprocal_explicit_initial]

/-- Actual signed SR has the exact initial value; this is NOT an abstract
`Rphysical` paired with an assumed representative identity. -/
theorem physical_signed_R_initial
    {X : Type*} (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ) (x : X)
    (hR0 : R0 x ≠ 0) :
    physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x 0 = R0 x := by
  rw [physicalSignedRScalar, physical_signed_Y_initial]
  field_simp [hR0, Real.exp_ne_zero] <;> ring

/-- Once a positive reciprocal box is supplied by the already verified
scalar comparison theorem, positivity of the physical SR is automatic. -/
theorem physical_signed_R_positive
    {X : Type*} (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ) (x : X) (t : ℝ)
    (hY : 0 < physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t) :
    0 < physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t := by
  exact mul_pos (Real.exp_pos _) (inv_pos.mpr hY)

/-- L² field of the **actual scalar** reciprocal on a local region.
The `MemLp` input expresses spatial measurability/integrability; it does not
postulate any spatial weak derivatives or any H² regularity. -/
noncomputable def physicalSignedYL2
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma1 Rstar R0 : X → ℝ) (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ) : ℝ → Lp ℝ 2 μ :=
  fun t => if ht : 0 ≤ t then (hLp t ht).toLp else 0

/-- L² field of the **actual reconstructed SR**. Both time paths depend on
the same physical pressure u and the same signed reciprocal equation. -/
noncomputable def physicalSignedRL2
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma1 Rstar R0 : X → ℝ) (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ) : ℝ → Lp ℝ 2 μ :=
  fun t => if ht : 0 ≤ t then (hLp t ht).toLp else 0

/-- `hScalar` of the previous A7 interface is a THEOREM for the explicit
physical field, not an extra physical assumption. -/
theorem physical_signed_YL2_represents_actual_solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma1 Rstar R0 : X → ℝ) (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, ((physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hLp t) x : ℝ) =
      ReservoirSeismicityControl.srReciprocalExplicit
        (fun v => gamma2 x v * Rstar x)
        (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
        (Real.exp (s * gamma1 x * u x 0) / R0 x) t := by
  filter_upwards [MemLp.coeFn_toLp (hLp t ht)] with x hx
  simpa only [physicalSignedYL2, dif_pos ht, physicalSignedYScalar] using hx

/-- The reconstructed physical SR L² representative is exactly the signed
pointwise quotient of the very same scalar reciprocal. -/
theorem physical_signed_RL2_represents_actual_solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma1 Rstar R0 : X → ℝ) (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, ((physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hLp t) x : ℝ) =
      Real.exp (s * gamma1 x * u x t) *
        (physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)⁻¹ := by
  filter_upwards [MemLp.coeFn_toLp (hLp t ht)] with x hx
  simpa only [physicalSignedRL2, dif_pos ht, physicalSignedRScalar] using hx

#print axioms physical_signed_Y_initial
#print axioms physical_signed_R_initial
#print axioms physical_signed_R_positive
#print axioms physical_signed_YL2_represents_actual_solution
#print axioms physical_signed_RL2_represents_actual_solution

end ReservoirSeismicityControl.Paper2026
