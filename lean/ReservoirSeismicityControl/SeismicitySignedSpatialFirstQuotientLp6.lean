import ReservoirSeismicityControl.SeismicitySignedSpatialDiscreteWeakLimit
import ReservoirSeismicityControl.SeismicitySignedSpatialHessianForcingBound
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# M1 — The actual first spatial difference-quotient forcing is in L⁶

For the signed seismicity reciprocal Y = exp(s γ₁ u) / R, the already
verified first-quotient equation is

  (D_h Y)_t = -a(x+h,t) D_h Y + [D_h b - (D_h a) Y],

with a=γ₂ R*, b=γ₂ exp(s γ₁ u) and s=±1.

The physical spatial Sobolev assumptions give D_h a,D_h b in L⁶
(on suitable interior translated subdomains), while the verified
reciprocal box controls Y in L∞. This module proves the exact L⁶
integrability and *quantitative* forcing norm bound, in Mathlib's Lp
spaces, without assuming the forcing's L⁶ bound separately.

This is not the uniform-in-time quotient estimate. To conclude H²(U_j)
we still need spatially localized difference quotient estimates for
the original H² coefficient data, the a.e.-time damped evolution
in L⁶ and L², and the weak compactness/weak derivative passage.
No Qdot estimate and no choice of sign is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Multiplication of a first derivative in L⁶ by a bounded
reciprocal solution preserves L⁶ integrability. -/
theorem sr_signed_first_quotient_L6_Linfty_product_memLp6
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (da : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp (fun x : Ω => (da x : ℝ) * (y x : ℝ))
      (6 : ENNReal) μ := by
  exact (Lp.memLp da).fun_mul (Lp.memLp y)

/-- The *actual* quotient forcing is in spatial L⁶. -/
theorem sr_signed_first_quotient_forcing_memLp6
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (db da : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp
      (fun x : Ω => (db x : ℝ) - (da x : ℝ) * (y x : ℝ))
      (6 : ENNReal) μ := by
  exact (Lp.memLp db).sub
    (sr_signed_first_quotient_L6_Linfty_product_memLp6 μ da y)

/-- Quantitative L⁶ × L∞ → L⁶ bound for the first-quotient product. -/
theorem sr_signed_first_quotient_L6_Linfty_product_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (da : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm (fun x : Ω => (da x : ℝ) * (y x : ℝ))
      (6 : ENNReal) μ ≤
      eLpNorm (da : Ω → ℝ) (6 : ENNReal) μ *
        eLpNorm (y : Ω → ℝ) (⊤ : ENNReal) μ := by
  have hy : AEStronglyMeasurable (y : Ω → ℝ) μ :=
    Lp.aestronglyMeasurable y
  have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
    (p := (6 : ENNReal)) (φ := (y : Ω → ℝ))
    (f := (da : Ω → ℝ)) hy
  have hPointwise :
      ((y : Ω → ℝ) • (da : Ω → ℝ)) =
        (fun x : Ω => (y x : ℝ) * (da x : ℝ)) := by
    funext x
    simp only [smul_eq_mul, Pi.mul_apply]
  rw [hPointwise] at h
  calc
    eLpNorm (fun x : Ω => (da x : ℝ) * (y x : ℝ)) 6 μ =
        eLpNorm (fun x : Ω => (y x : ℝ) * (da x : ℝ)) 6 μ := by
          congr 1
          funext x
          ring
    _ ≤ eLpNorm (y : Ω → ℝ) ⊤ μ *
          eLpNorm (da : Ω → ℝ) 6 μ := h
    _ = _ := mul_comm _ _

/-- The first derivative forcing estimate from Appendix A.2,
expressed with *actual* spatial L⁶ seminorms. -/
theorem sr_signed_first_quotient_forcing_eLpNorm_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (db da : Lp ℝ (6 : ENNReal) μ)
    (y : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm (fun x : Ω => (db x : ℝ) - (da x : ℝ) * (y x : ℝ))
        (6 : ENNReal) μ ≤
      eLpNorm (db : Ω → ℝ) (6 : ENNReal) μ +
        eLpNorm (da : Ω → ℝ) (6 : ENNReal) μ *
          eLpNorm (y : Ω → ℝ) (⊤ : ENNReal) μ := by
  let f : Ω → ℝ := fun x => (db x : ℝ)
  let g : Ω → ℝ := fun x => (da x : ℝ) * (y x : ℝ)
  have hSub : eLpNorm (f - g) (6 : ENNReal) μ ≤
      eLpNorm f 6 μ + eLpNorm g 6 μ :=
    eLpNorm_sub_le (by norm_num)
  have hProd := sr_signed_first_quotient_L6_Linfty_product_bound μ da y
  change eLpNorm (f - g) 6 μ ≤
    eLpNorm f 6 μ +
      eLpNorm (da : Ω → ℝ) 6 μ * eLpNorm (y : Ω → ℝ) ⊤ μ
  have hProd' : eLpNorm g (6 : ENNReal) μ ≤
      eLpNorm (da : Ω → ℝ) 6 μ *
        eLpNorm (y : Ω → ℝ) ⊤ μ := hProd
  exact hSub.trans (add_le_add_right hProd' (eLpNorm f (6 : ENNReal) μ))

/-- Applied at each time to the real, signed physical reciprocal Y,
the spatial first quotient's L⁶ forcing is uniformly controlled by
uniform coefficient difference-quotient norms and the reciprocal box.
The premises are bound statements on the physical Lp representatives,
not an independent bound on the forcing term. -/
theorem sr_signed_first_quotient_forcing_uniform_L6
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (db da : ℝ → Lp ℝ (6 : ENNReal) μ)
    (y : ℝ → Lp ℝ (⊤ : ENNReal) μ)
    (A1 B1 YM : ENNReal)
    (hA : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (da t : Ω → ℝ) (6 : ENNReal) μ ≤ A1)
    (hB : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (db t : Ω → ℝ) (6 : ENNReal) μ ≤ B1)
    (hY : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (y t : Ω → ℝ) (⊤ : ENNReal) μ ≤ YM) :
    ∀ t : ℝ, 0 ≤ t →
      eLpNorm (fun x : Ω =>
        (db t x : ℝ) - (da t x : ℝ) * (y t x : ℝ))
        (6 : ENNReal) μ ≤ B1 + A1 * YM := by
  intro t ht
  have hBase := sr_signed_first_quotient_forcing_eLpNorm_bound
    μ (db t) (da t) (y t)
  apply hBase.trans
  apply add_le_add (hB t ht)
  exact mul_le_mul' (hA t ht) (hY t ht)

#print axioms ReservoirSeismicityControl.sr_signed_first_quotient_L6_Linfty_product_memLp6
#print axioms ReservoirSeismicityControl.sr_signed_first_quotient_forcing_memLp6
#print axioms ReservoirSeismicityControl.sr_signed_first_quotient_L6_Linfty_product_bound
#print axioms ReservoirSeismicityControl.sr_signed_first_quotient_forcing_eLpNorm_bound
#print axioms ReservoirSeismicityControl.sr_signed_first_quotient_forcing_uniform_L6

end ReservoirSeismicityControl
