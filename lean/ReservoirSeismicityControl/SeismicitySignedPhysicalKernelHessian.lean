import ReservoirSeismicityControl.SeismicitySignedPhysicalH2HalfDamping
import ReservoirSeismicityControl.SeismicitySignedSpatialHessianForcingBound
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# M1 — physical H² kernel: the complete spatial Hessian cross terms

For A(x)=∫_v^t a(x,q)dq and K(x)=exp(-A(x)) b(x,v), the second
spatial derivative of K is

  exp(-A) [Dij b - Di A Dj b - Dj A Di b - Dij A b + Di A Dj A b].

The preceding M1 modules proved the scalar classical kernel identity,
the two-gradient L⁶×L⁶→L² bound, and the exponentially weighted time
moment estimates. The new results below estimate the ENTIRE expression in
actual L²(U_j), including the previously untreated quadratic-gradient
term Di A Dj A b. The latter only needs Di A,Dj A∈L⁶ and b∈L∞,
not an unjustified L∞ bound on first derivatives.

This is the sharp spatial product estimate necessary to derive polynomial
kernel bounds from physical coefficient norms on a finite-volume 3D
neighborhood. The remaining separate physical interface is weak
identification of the kernel derivatives under the time integral, along
with the weak Sobolev composition of the exponential multiplier. No
unproved H² claim is introduced by these norm estimates.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The product of two L⁶ gradients times one bounded coefficient lies
in L². This is the quadratic part of the *physical exponential kernel*
Hessian and uses the finite-volume embedding L³⊂L². -/
theorem sr_signed_kernel_quadratic_gradient_memLp2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp (fun x : Ω =>
      ((p x : ℝ) * (q x : ℝ)) * (b x : ℝ))
      (2 : ENNReal) μ := by
  exact (sr_signed_spatial_L6_times_L6_memLp2 μ p q).fun_mul
    (Lp.memLp b)

/-- Quantitative volume-aware Hölder bound for the complete quadratic
term. The first two factors belong only to L⁶; the third to L∞. -/
theorem sr_signed_kernel_quadratic_gradient_L2_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm (fun x : Ω =>
      ((p x : ℝ) * (q x : ℝ)) * (b x : ℝ))
      (2 : ENNReal) μ ≤
      ((eLpNorm (p : Ω → ℝ) (6 : ENNReal) μ *
        eLpNorm (q : Ω → ℝ) (6 : ENNReal) μ) *
        μ Set.univ ^ ((1 : ℝ) / 6)) *
        eLpNorm (b : Ω → ℝ) (⊤ : ENNReal) μ := by
  let hProd : MemLp (fun x : Ω => (p x : ℝ) * (q x : ℝ))
      (2 : ENNReal) μ :=
    sr_signed_spatial_L6_times_L6_memLp2 μ p q
  let pq : Lp ℝ (2 : ENNReal) μ :=
    MemLp.toLp (fun x : Ω => (p x : ℝ) * (q x : ℝ)) hProd
  have hRep : (pq : Ω → ℝ) =ᵐ[μ]
      (fun x : Ω => (p x : ℝ) * (q x : ℝ)) :=
    MemLp.coeFn_toLp hProd
  have hNormRep :
      eLpNorm (pq : Ω → ℝ) (2 : ENNReal) μ =
      eLpNorm (fun x : Ω => (p x : ℝ) * (q x : ℝ))
        (2 : ENNReal) μ := eLpNorm_congr_ae hRep
  have hTripleRep :
      (fun x : Ω => (pq x : ℝ) * (b x : ℝ)) =ᵐ[μ]
      (fun x : Ω => ((p x : ℝ) * (q x : ℝ)) * (b x : ℝ)) := by
    filter_upwards [hRep] with x hx
    rw [hx]
  have hNormTriple :
      eLpNorm (fun x : Ω =>
          ((p x : ℝ) * (q x : ℝ)) * (b x : ℝ))
          (2 : ENNReal) μ =
      eLpNorm (fun x : Ω => (pq x : ℝ) * (b x : ℝ))
          (2 : ENNReal) μ :=
    eLpNorm_congr_ae hTripleRep.symm
  have hPair := sr_signed_spatial_L6_cross_L2_volume_bound μ p q
  have hMul := sr_signed_spatial_L2_Linfty_cross_bound μ pq b
  calc
    eLpNorm (fun x : Ω =>
        ((p x : ℝ) * (q x : ℝ)) * (b x : ℝ)) 2 μ =
        eLpNorm (fun x : Ω => (pq x : ℝ) * (b x : ℝ)) 2 μ := hNormTriple
    _ ≤ eLpNorm (pq : Ω → ℝ) 2 μ *
          eLpNorm (b : Ω → ℝ) ⊤ μ := hMul
    _ = eLpNorm (fun x : Ω => (p x : ℝ) * (q x : ℝ)) 2 μ *
          eLpNorm (b : Ω → ℝ) ⊤ μ := by rw [hNormRep]
    _ ≤ ((eLpNorm (p : Ω → ℝ) 6 μ *
          eLpNorm (q : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) *
          eLpNorm (b : Ω → ℝ) ⊤ μ :=
        mul_le_mul_of_nonneg_right hPair bot_le

/-- The *complete* weak Hessian integrand from the direct kernel formula.
The first four terms are handled by the already verified Hessian
cross-term bound; the fifth, quadratic term is now controlled above. -/
theorem sr_signed_physical_kernel_hessian_memLp2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (b_ij A_ij : Lp ℝ (2 : ENNReal) μ)
    (A_i A_j b_i b_j : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ) :
    MemLp (fun x : Ω =>
        (b_ij x : ℝ) - (A_i x : ℝ) * (b_j x : ℝ) -
          (A_j x : ℝ) * (b_i x : ℝ) -
          (A_ij x : ℝ) * (b x : ℝ) +
          ((A_i x : ℝ) * (A_j x : ℝ)) * (b x : ℝ))
      (2 : ENNReal) μ := by
  have hBase := sr_signed_reciprocal_hessian_forcing_memLp2
    μ b_ij A_ij A_i A_j b_i b_j b
  have hQuadratic := sr_signed_kernel_quadratic_gradient_memLp2
    μ A_i A_j b
  exact hBase.add hQuadratic

/-- Exact volume-aware L² bound of the FULL physical spatial Hessian
of the undamped Duhamel kernel, including its quadratic gradient term.
This produces a quantitative hypothesis for the half-damping theorem
from L²/L⁶/L∞ data, not from a postulated Hessian norm bound. -/
theorem sr_signed_physical_kernel_hessian_L2_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (b_ij A_ij : Lp ℝ (2 : ENNReal) μ)
    (A_i A_j b_i b_j : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ) :
    eLpNorm (fun x : Ω =>
        (b_ij x : ℝ) - (A_i x : ℝ) * (b_j x : ℝ) -
          (A_j x : ℝ) * (b_i x : ℝ) -
          (A_ij x : ℝ) * (b x : ℝ) +
          ((A_i x : ℝ) * (A_j x : ℝ)) * (b x : ℝ))
        (2 : ENNReal) μ ≤
      (((eLpNorm (b_ij : Ω → ℝ) 2 μ +
        (eLpNorm (A_i : Ω → ℝ) 6 μ *
          eLpNorm (b_j : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        (eLpNorm (A_j : Ω → ℝ) 6 μ *
          eLpNorm (b_i : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        eLpNorm (A_ij : Ω → ℝ) 2 μ *
          eLpNorm (b : Ω → ℝ) ⊤ μ) +
      (((eLpNorm (A_i : Ω → ℝ) 6 μ *
          eLpNorm (A_j : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) *
          eLpNorm (b : Ω → ℝ) ⊤ μ) := by
  let base : Ω → ℝ := fun x =>
    (b_ij x : ℝ) - (A_i x : ℝ) * (b_j x : ℝ) -
      (A_j x : ℝ) * (b_i x : ℝ) - (A_ij x : ℝ) * (b x : ℝ)
  let quad : Ω → ℝ := fun x =>
    ((A_i x : ℝ) * (A_j x : ℝ)) * (b x : ℝ)
  have hBase := sr_signed_reciprocal_hessian_forcing_eLpNorm_bound
    μ b_ij A_ij A_i A_j b_i b_j b
  have hQuad := sr_signed_kernel_quadratic_gradient_L2_bound
    μ A_i A_j b
  have hSum : eLpNorm (base + quad) (2 : ENNReal) μ ≤
      eLpNorm base (2 : ENNReal) μ +
        eLpNorm quad (2 : ENNReal) μ := eLpNorm_add_le (by norm_num)
  change eLpNorm (base + quad) 2 μ ≤ _
  exact hSum.trans (add_le_add hBase hQuad)

#print axioms ReservoirSeismicityControl.sr_signed_kernel_quadratic_gradient_memLp2
#print axioms ReservoirSeismicityControl.sr_signed_kernel_quadratic_gradient_L2_bound
#print axioms ReservoirSeismicityControl.sr_signed_physical_kernel_hessian_memLp2
#print axioms ReservoirSeismicityControl.sr_signed_physical_kernel_hessian_L2_bound

end ReservoirSeismicityControl
