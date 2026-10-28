import ReservoirSeismicityControl.SeismicitySignedSpatialDifferenceQuotients
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# M1 — physical spatial L² integrability of the signed reciprocal Hessian forcing

For the signed model Y = exp(s γ₁ u) / R, the mixed second spatial
quotient/derivative equation contains

  D²b - (Da)(DY) - (Da)(DY) - (D²a)Y.

The finite-volume 3D Sobolev embedding H² ⊂ W¹,⁶ provides
Da, DY ∈ L⁶; the second derivatives D²a,D²b belong to L²,
and positivity of Y gives Y ∈ L∞. The previously verified discrete
identities produce exactly these terms. This file proves, in actual
MeasureTheory.MemLp spaces (not just pointwise algebra), that all of
these terms belong to L² of a finite-measure neighborhood.

The two first-derivative products use Holder L⁶×L⁶ → L³ and the
finite-measure inclusion L³ → L². The last product uses L²×L∞→L².

The uniform L² norm bound and identification of physical weak spatial
derivatives from quotient compactness are separate M1 goals.
No assumption on Qdot is made. Both s=±1 are included via a,b.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The physical Holder exponents 6,6,3 (1/3=1/6+1/6). -/
private instance srSpatialHolder663 :
    (6 : ENNReal).HolderTriple 6 3 := by
  constructor
  -- Arithmetic in ENNReal is not normalized directly by `norm_num`.
  -- Rewrite reciprocals as coercions from NNReal before evaluating them.
  change ((6 : NNReal) : ENNReal)⁻¹ + ((6 : NNReal) : ENNReal)⁻¹ =
    ((3 : NNReal) : ENNReal)⁻¹
  rw [← ENNReal.coe_inv (show (6 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_inv (show (3 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_add]
  -- The resulting identity is an ordinary equality of nonnegative reals.
  apply congrArg (fun z : NNReal => (z : ENNReal))
    (show (6 : NNReal)⁻¹ + (6 : NNReal)⁻¹ = (3 : NNReal)⁻¹ by
      apply Subtype.ext
      norm_num)

/-- A product of spatial L⁶ coefficient/reciprocal gradients lies in L³.
This is a *genuine* Holder integrability result on the Lebesgue quotient. -/
theorem sr_signed_spatial_L6_times_L6_memLp3
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f g : Lp ℝ (6 : ENNReal) μ) :
    MemLp (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (3 : ENNReal) μ := by
  exact (Lp.memLp f).fun_mul (Lp.memLp g)

/-- The same physical L⁶×L⁶ product has its sharp L³ Holder norm bound. -/
theorem sr_signed_spatial_L6_cross_L3_norm_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f g : Lp ℝ (6 : ENNReal) μ) :
    ‖(f • g : Lp ℝ (3 : ENNReal) μ)‖ ≤ ‖f‖ * ‖g‖ := by
  exact Lp.norm_smul_le f g

/-- Finite volume upgrades the cross term from L³ to L².
This is the exponent change needed to bound the Hessian forcing. -/
theorem sr_signed_spatial_L6_times_L6_memLp2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Lp ℝ (6 : ENNReal) μ) :
    MemLp (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (2 : ENNReal) μ := by
  have h3 := sr_signed_spatial_L6_times_L6_memLp3 μ f g
  exact h3.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)

/-- The zero-order reciprocal term belongs to L² when D²a∈L²,
Y∈L∞. No extra pointwise bound on D²a is required. -/
theorem sr_signed_spatial_L2_times_Linfty_memLp2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (d2a : Lp ℝ (2 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp (fun x : Ω => (d2a x : ℝ) * (y x : ℝ))
      (2 : ENNReal) μ := by
  exact (Lp.memLp d2a).fun_mul (Lp.memLp y)

/-- All four terms in the physical Hessian equation are L² on the
well neighborhood. This closes the integrability side of the signed
SR Hessian forcing, with no independent L²-forcing hypothesis. -/
theorem sr_signed_reciprocal_hessian_forcing_memLp2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (d2b d2a : Lp ℝ (2 : ENNReal) μ)
    (da₁ da₂ dy₁ dy₂ : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp
      (fun x : Ω =>
        (d2b x : ℝ) - (da₁ x : ℝ) * (dy₂ x : ℝ) -
          (da₂ x : ℝ) * (dy₁ x : ℝ) -
          (d2a x : ℝ) * (y x : ℝ))
      (2 : ENNReal) μ := by
  have hc1 := sr_signed_spatial_L6_times_L6_memLp2 μ da₁ dy₂
  have hc2 := sr_signed_spatial_L6_times_L6_memLp2 μ da₂ dy₁
  have hc3 := sr_signed_spatial_L2_times_Linfty_memLp2 μ d2a y
  exact (((Lp.memLp d2b).sub hc1).sub hc2).sub hc3

#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_times_L6_memLp3
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_cross_L3_norm_le
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_times_L6_memLp2
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L2_times_Linfty_memLp2
#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_hessian_forcing_memLp2

end ReservoirSeismicityControl
