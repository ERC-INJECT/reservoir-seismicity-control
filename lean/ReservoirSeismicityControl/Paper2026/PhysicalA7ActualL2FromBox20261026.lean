import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualSignedField20261026
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# Physical A7: actual signed Y and R are L² on every finite-volume near-well region

The previous concrete signed-field module required two independently supplied
`MemLp` certificates. Here those are PROVED from the actual physical positive
reciprocal bounds and the finite reservoir volume, not assumed.

`hYbox` is the output of the previously proved physical scalar comparison;
`hExpBound` is the physical bounded-pressure / bounded-γ₁ exponential bound.
Only the ordinary a.e. measurability of the two explicit scalar maps remains.
No H² assumption on Y, R, or the propagator; no Qdot assumption.

A uniform H² estimate is NOT asserted by this theorem. This removes the
measurability/integrability applicability obstruction before the spatial
weak-derivative identification is attempted.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The explicit physical reciprocal and reconstructed signed SR have
finite-volume L² representatives once the scalar reciprocal comparison and
pressure exponential box are available. The bounds hold a.e. in space,
so this does not strengthen the manuscript to pointwise spatial bounds. -/
theorem physical_signed_actual_Y_R_memLp_from_uniform_box
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (yMin yMax Emax : ℝ)
    (hyMin : 0 < yMin) (hEmax : 0 ≤ Emax)
    (hYmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    (hRmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    (hYbox : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂μ,
      yMin ≤ physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ∧
      physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ≤ yMax)
    (hExpBound : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂μ,
      Real.exp (s * gamma1 x * u x t) ≤ Emax) :
    (∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ) ∧
    (∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ) := by
  constructor
  · intro t ht
    have hTop : MemLp
        (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (⊤ : ENNReal) μ := by
      apply memLp_top_of_bound (hYmeas t ht) yMax
      filter_upwards [hYbox t ht] with x hx
      have hpos : 0 < physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t :=
        lt_of_lt_of_le hyMin hx.1
      simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hx.2
    exact hTop.mono_exponent (by norm_num : (2 : ENNReal) ≤ ⊤)
  · intro t ht
    have hTop : MemLp
        (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (⊤ : ENNReal) μ := by
      apply memLp_top_of_bound (hRmeas t ht) (Emax / yMin)
      filter_upwards [hYbox t ht, hExpBound t ht] with x hx he
      let y := physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t
      have hy : 0 < y := lt_of_lt_of_le hyMin hx.1
      have hRpos : 0 < physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t :=
        physical_signed_R_positive gamma1 Rstar R0 gamma2 u s x t hy
      have hq : Real.exp (s * gamma1 x * u x t) / y ≤ Emax / yMin := by
        apply (div_le_div_iff₀ hy hyMin).2
        exact (mul_le_mul_of_nonneg_right he hyMin.le).trans
          (mul_le_mul_of_nonneg_left hx.1 hEmax)
      have hR : physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t ≤
          Emax / yMin := by
        simpa only [physicalSignedRScalar, div_eq_mul_inv] using hq
      simpa only [Real.norm_eq_abs, abs_of_pos hRpos] using hR
    exact hTop.mono_exponent (by norm_num : (2 : ENNReal) ≤ ⊤)

/-- Construct the actual L² time paths from the scalar physical bounds.
In particular, the `hLp` assumptions of the earlier signed-field theorem
are eliminated, and both L² paths represent exactly the same signed
Carathéodory solution and reconstructed SR. -/
theorem physical_signed_actual_Y_R_L2_paths_from_box
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (yMin yMax Emax : ℝ)
    (hyMin : 0 < yMin) (hEmax : 0 ≤ Emax)
    (hYmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    (hRmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    (hYbox : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂μ,
      yMin ≤ physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ∧
      physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ≤ yMax)
    (hExpBound : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂μ,
      Real.exp (s * gamma1 x * u x t) ≤ Emax) :
    ∃ Yphys Rphys : ℝ → Lp ℝ 2 μ,
      (∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
        (Yphys t x : ℝ) =
          physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t) ∧
      (∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
        (Rphys t x : ℝ) =
          physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t) := by
  obtain ⟨hLpY, hLpR⟩ := physical_signed_actual_Y_R_memLp_from_uniform_box
    μ gamma1 Rstar R0 gamma2 u s yMin yMax Emax
    hyMin hEmax hYmeas hRmeas hYbox hExpBound
  refine ⟨physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hLpY,
    physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hLpR, ?_, ?_⟩
  · intro t ht
    have h := physical_signed_YL2_represents_actual_solution
      μ gamma1 Rstar R0 gamma2 u s hLpY t ht
    simpa only [physicalSignedYScalar] using h
  · intro t ht
    have h := physical_signed_RL2_represents_actual_solution
      μ gamma1 Rstar R0 gamma2 u s hLpR t ht
    simpa only [physicalSignedRScalar] using h

#print axioms physical_signed_actual_Y_R_memLp_from_uniform_box
#print axioms physical_signed_actual_Y_R_L2_paths_from_box

end ReservoirSeismicityControl.Paper2026
