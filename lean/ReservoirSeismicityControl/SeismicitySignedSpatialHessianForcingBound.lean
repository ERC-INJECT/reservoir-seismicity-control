import ReservoirSeismicityControl.SeismicitySignedSpatialHessianLpCrossTerms
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# M1 — quantitative spatial L² estimate for the signed reciprocal Hessian forcing

The last stage proved actual L² membership of the four Hessian forcing
terms.  This stage proves the *numerical norm estimate* needed to feed the
verified damped-convolution H² bootstrap.

If the well neighborhood has finite volume, Holder L⁶×L⁶→L³ and the
finite-measure embedding L³→L² yield the sharp volume factor |U_j|^(1/6).
In particular, for
  F = D²b - (Da₁)(DY₂) - (Da₂)(DY₁) - (D²a)Y,
we bound the actual L² seminorm of F in terms of the L²/L⁶/L∞ seminorms
of its physical components, WITHOUT postulating a bound on F.

The signed SR model enters via the coefficients
  a = γ₂ R*, b = γ₂ exp(s γ₁ u), s∈{-1,1}.
There is no time derivative of Q here.

This is not a proof that Y has spatial weak derivatives; the latter must
still be identified from the finite-difference equations and the H² data.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The exact L⁶×L⁶→L² Hölder bound on a finite-volume well neighborhood.
The exponent `(1/2 - 1/3)` equals `1/6`, as in Appendix A.2. -/
theorem sr_signed_spatial_L6_cross_L2_volume_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Lp ℝ (6 : ENNReal) μ) :
    eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (2 : ENNReal) μ ≤
      (eLpNorm (f : Ω → ℝ) (6 : ENNReal) μ *
        eLpNorm (g : Ω → ℝ) (6 : ENNReal) μ) *
        μ Set.univ ^ ((1 : ℝ) / 6) := by
  letI : (6 : ENNReal).HolderTriple 6 3 := by
    constructor
    change ((6 : NNReal) : ENNReal)⁻¹ + ((6 : NNReal) : ENNReal)⁻¹ =
      ((3 : NNReal) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (show (6 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_inv (show (3 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_add]
    apply congrArg (fun z : NNReal => (z : ENNReal))
      (show (6 : NNReal)⁻¹ + (6 : NNReal)⁻¹ = (3 : NNReal)⁻¹ by
        apply Subtype.ext
        norm_num)
  have hf : AEStronglyMeasurable (f : Ω → ℝ) μ := Lp.aestronglyMeasurable f
  have hg : AEStronglyMeasurable (g : Ω → ℝ) μ := Lp.aestronglyMeasurable g
  have hfg : AEStronglyMeasurable
      (fun x : Ω => (f x : ℝ) * (g x : ℝ)) μ := hf.mul hg
  have hHolder :
      eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (3 : ENNReal) μ ≤
        eLpNorm (f : Ω → ℝ) (6 : ENNReal) μ *
          eLpNorm (g : Ω → ℝ) (6 : ENNReal) μ := by
    have h := eLpNorm_smul_le_mul_eLpNorm
      (p := (6 : ENNReal)) (q := (6 : ENNReal)) (r := (3 : ENNReal))
      hf hg
    -- Hölder returns the product as pointwise scalar multiplication `•`,
    -- not as function multiplication `*`.  Prove the exact function identity.
    have hPointwise :
        ((f : Ω → ℝ) • (g : Ω → ℝ)) =
          (fun x : Ω => (f x : ℝ) * (g x : ℝ)) := by
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
    rw [hPointwise] at h
    exact h
  have hEmbed :
      eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (2 : ENNReal) μ ≤
        eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (3 : ENNReal) μ *
          μ Set.univ ^ ((1 : ℝ) / 6) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (2 : ENNReal)) (q := (3 : ENNReal))
      (by norm_num) hfg
    convert h using 1 <;> norm_num
  have hnonneg : (0 : ENNReal) ≤ μ Set.univ ^ ((1 : ℝ) / 6) := bot_le
  exact hEmbed.trans (mul_le_mul_of_nonneg_right hHolder hnonneg)

/-- The actual L² estimate for multiplication of a second-derivative
coefficient by the uniformly bounded reciprocal solution. -/
theorem sr_signed_spatial_L2_Linfty_cross_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f : Lp ℝ (2 : ENNReal) μ)
    (g : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) (2 : ENNReal) μ ≤
      eLpNorm (f : Ω → ℝ) (2 : ENNReal) μ *
        eLpNorm (g : Ω → ℝ) (⊤ : ENNReal) μ := by
  have hg : AEStronglyMeasurable (g : Ω → ℝ) μ := Lp.aestronglyMeasurable g
  have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
    (p := (2 : ENNReal)) (φ := (g : Ω → ℝ))
    (f := (f : Ω → ℝ)) hg
  have h' :
      eLpNorm (fun x : Ω => (g x : ℝ) * (f x : ℝ)) (2 : ENNReal) μ ≤
        eLpNorm (g : Ω → ℝ) (⊤ : ENNReal) μ *
          eLpNorm (f : Ω → ℝ) (2 : ENNReal) μ := by
    have hPointwise :
        ((g : Ω → ℝ) • (f : Ω → ℝ)) =
          (fun x : Ω => (g x : ℝ) * (f x : ℝ)) := by
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
    rw [hPointwise] at h
    exact h
  calc
    eLpNorm (fun x : Ω => (f x : ℝ) * (g x : ℝ)) 2 μ =
        eLpNorm (fun x : Ω => (g x : ℝ) * (f x : ℝ)) 2 μ := by
          congr 1
          funext x
          ring
    _ ≤ eLpNorm (g : Ω → ℝ) ⊤ μ *
        eLpNorm (f : Ω → ℝ) 2 μ := h'
    _ = _ := mul_comm _ _

/-- Complete *quantitative* spatial L² bound for the signed reciprocal
Hessian forcing, ready for the damped H² bootstrap.  The finite-volume
factor is explicit and works for ordinary (non-normalized) volume measure. -/
theorem sr_signed_reciprocal_hessian_forcing_eLpNorm_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (d2b d2a : Lp ℝ (2 : ENNReal) μ)
    (da₁ da₂ dy₁ dy₂ : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm
      (fun x : Ω =>
        (d2b x : ℝ) - (da₁ x : ℝ) * (dy₂ x : ℝ) -
          (da₂ x : ℝ) * (dy₁ x : ℝ) -
          (d2a x : ℝ) * (y x : ℝ))
      (2 : ENNReal) μ ≤
        ((eLpNorm (d2b : Ω → ℝ) (2 : ENNReal) μ +
          (eLpNorm (da₁ : Ω → ℝ) (6 : ENNReal) μ *
            eLpNorm (dy₂ : Ω → ℝ) (6 : ENNReal) μ) *
            μ Set.univ ^ ((1 : ℝ) / 6)) +
          (eLpNorm (da₂ : Ω → ℝ) (6 : ENNReal) μ *
            eLpNorm (dy₁ : Ω → ℝ) (6 : ENNReal) μ) *
            μ Set.univ ^ ((1 : ℝ) / 6)) +
          eLpNorm (d2a : Ω → ℝ) (2 : ENNReal) μ *
            eLpNorm (y : Ω → ℝ) (⊤ : ENNReal) μ := by
  let c₁ : Ω → ℝ := fun x => (da₁ x : ℝ) * (dy₂ x : ℝ)
  let c₂ : Ω → ℝ := fun x => (da₂ x : ℝ) * (dy₁ x : ℝ)
  let c₃ : Ω → ℝ := fun x => (d2a x : ℝ) * (y x : ℝ)
  let f : Ω → ℝ := fun x => (d2b x : ℝ)
  have h₁ := sr_signed_spatial_L6_cross_L2_volume_bound μ da₁ dy₂
  have h₂ := sr_signed_spatial_L6_cross_L2_volume_bound μ da₂ dy₁
  have h₃ := sr_signed_spatial_L2_Linfty_cross_bound μ d2a y
  have h1 : eLpNorm c₁ (2 : ENNReal) μ ≤
      (eLpNorm (da₁ : Ω → ℝ) 6 μ * eLpNorm (dy₂ : Ω → ℝ) 6 μ) *
      μ Set.univ ^ ((1 : ℝ) / 6) := h₁
  have h2 : eLpNorm c₂ (2 : ENNReal) μ ≤
      (eLpNorm (da₂ : Ω → ℝ) 6 μ * eLpNorm (dy₁ : Ω → ℝ) 6 μ) *
      μ Set.univ ^ ((1 : ℝ) / 6) := h₂
  have h3 : eLpNorm c₃ (2 : ENNReal) μ ≤
      eLpNorm (d2a : Ω → ℝ) 2 μ * eLpNorm (y : Ω → ℝ) ⊤ μ := h₃
  have htotal :
      eLpNorm ((f - c₁ - c₂) - c₃) (2 : ENNReal) μ ≤
      ((eLpNorm f 2 μ + eLpNorm c₁ 2 μ) + eLpNorm c₂ 2 μ) +
        eLpNorm c₃ 2 μ := by
    calc
      eLpNorm ((f - c₁ - c₂) - c₃) 2 μ ≤
          eLpNorm (f - c₁ - c₂) 2 μ + eLpNorm c₃ 2 μ :=
        eLpNorm_sub_le (by norm_num)
      _ ≤ (eLpNorm (f - c₁) 2 μ + eLpNorm c₂ 2 μ) +
           eLpNorm c₃ 2 μ := by
        gcongr
        exact eLpNorm_sub_le (by norm_num)
      _ ≤ ((eLpNorm f 2 μ + eLpNorm c₁ 2 μ) + eLpNorm c₂ 2 μ) +
           eLpNorm c₃ 2 μ := by
        gcongr
        exact eLpNorm_sub_le (by norm_num)
  change eLpNorm ((f - c₁ - c₂) - c₃) 2 μ ≤ _
  apply htotal.trans
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact le_rfl
      · exact h1
    · exact h2
  · exact h3

#print axioms ReservoirSeismicityControl.sr_signed_spatial_L6_cross_L2_volume_bound
#print axioms ReservoirSeismicityControl.sr_signed_spatial_L2_Linfty_cross_bound
#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_hessian_forcing_eLpNorm_bound

end ReservoirSeismicityControl
