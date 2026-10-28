import ReservoirSeismicityControl.SeismicitySignedPhysicalKernelHessian
import ReservoirSeismicityControl.SeismicitySignedPhysicalThreeDimensionalKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
# M1: physical exponential damping preserves the *full* 3D kernel Hessian bound

For the reciprocal Duhamel kernel K(x,t,v) = exp(-A(x,t,v)) b(x,v),
A = integral_v^t gamma₂(x,q) R*(x) dq ≥ 0. The original Hessian theorem
bounds the five-term *bracket* in L². Here the actual exponential factor
is included, with **no separately postulated L-infinity bound on exp(-A)**.

The damping contraction works for every Lp exponent and any measure; the
five-term Hessian corollary works on the physical finite-volume region.
The only measurability premise of exp(-A) is separate from its boundedness;
it follows from ordinary measurability of A but is NOT proven here.

Not an assertion that the Hessian expression is already the weak derivative
of nonsmooth K: compatible smooth H² approximations on U_j and kernel weak
identification still need to be discharged. No sorry, admit, or axiom.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalDampedKernelHessian

open MeasureTheory

/-- If the integrated seismicity damping A is nonnegative a.e., then
multiplication by its physical exponential is an Lp contraction, for any
exponent including p=2 and p=6. No L-infinity premise on exp(-A). -/
theorem physical_exponential_damping_contracts_Lp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A F : Ω → ℝ) (p : ENNReal)
    (hA : ∀ᵐ x ∂μ, 0 ≤ A x)
    (hExpMeas : AEStronglyMeasurable (fun x => Real.exp (-A x)) μ)
    (hF : MemLp F p μ) :
    MemLp (fun x => Real.exp (-A x) * F x) p μ ∧
    eLpNorm (fun x => Real.exp (-A x) * F x) p μ ≤ eLpNorm F p μ := by
  have hProductMeas :
      AEStronglyMeasurable (fun x => Real.exp (-A x) * F x) μ :=
    hExpMeas.mul hF.aestronglyMeasurable
  have hPoint : ∀ᵐ x ∂μ,
      ‖Real.exp (-A x) * F x‖ ≤ ‖F x‖ := by
    filter_upwards [hA] with x hx
    have hNeg : -A x ≤ (0 : ℝ) := neg_nonpos.mpr hx
    have hExp : Real.exp (-A x) ≤ 1 := by
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hNeg)
    change |Real.exp (-A x) * F x| ≤ |F x|
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-A x) * |F x| ≤ 1 * |F x| :=
        mul_le_mul_of_nonneg_right hExp (abs_nonneg _)
      _ = |F x| := one_mul _
  exact ⟨hF.of_le hProductMeas hPoint,
    eLpNorm_mono_ae hProductMeas hPoint⟩

/-- The full *damped* Hessian formula is L² and inherits the previous
quantitative five-term estimate. In particular, the quadratic gradient
term needs only L⁶ gradients, not an artificial L∞ gradient bound.
The coefficient A in the exponential is nonnegative because gamma₂ R*>0
and the causal interval is forward in time (a fact to connect separately
when the pointwise time primitive is identified).
-/
theorem physical_damped_kernel_hessian_L2_and_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → ℝ)
    (bij Aij : Lp ℝ (2 : ENNReal) μ)
    (Ai Aj bi bj : Lp ℝ (6 : ENNReal) μ)
    (b : Lp ℝ (⊤ : ENNReal) μ)
    (hA : ∀ᵐ x ∂μ, 0 ≤ A x)
    (hExpMeas : AEStronglyMeasurable (fun x => Real.exp (-A x)) μ) :
    MemLp (fun x : Ω => Real.exp (-A x) *
      ((bij x : ℝ) - (Ai x : ℝ) * (bj x : ℝ) -
        (Aj x : ℝ) * (bi x : ℝ) -
        (Aij x : ℝ) * (b x : ℝ) +
        ((Ai x : ℝ) * (Aj x : ℝ)) * (b x : ℝ))) 2 μ ∧
    eLpNorm (fun x : Ω => Real.exp (-A x) *
      ((bij x : ℝ) - (Ai x : ℝ) * (bj x : ℝ) -
        (Aj x : ℝ) * (bi x : ℝ) -
        (Aij x : ℝ) * (b x : ℝ) +
        ((Ai x : ℝ) * (Aj x : ℝ)) * (b x : ℝ))) 2 μ ≤
      (((eLpNorm (bij : Ω → ℝ) 2 μ +
        (eLpNorm (Ai : Ω → ℝ) 6 μ *
          eLpNorm (bj : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        (eLpNorm (Aj : Ω → ℝ) 6 μ *
          eLpNorm (bi : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) +
        eLpNorm (Aij : Ω → ℝ) 2 μ *
          eLpNorm (b : Ω → ℝ) ⊤ μ) +
      (((eLpNorm (Ai : Ω → ℝ) 6 μ *
          eLpNorm (Aj : Ω → ℝ) 6 μ) *
          μ Set.univ ^ ((1 : ℝ) / 6)) *
          eLpNorm (b : Ω → ℝ) ⊤ μ) := by
  let F : Ω → ℝ := fun x =>
    (bij x : ℝ) - (Ai x : ℝ) * (bj x : ℝ) -
      (Aj x : ℝ) * (bi x : ℝ) -
      (Aij x : ℝ) * (b x : ℝ) +
      ((Ai x : ℝ) * (Aj x : ℝ)) * (b x : ℝ)
  have hF : MemLp F (2 : ENNReal) μ :=
    sr_signed_physical_kernel_hessian_memLp2 μ bij Aij Ai Aj bi bj b
  have hEstimate :=
    sr_signed_physical_kernel_hessian_L2_bound μ bij Aij Ai Aj bi bj b
  obtain ⟨hActual, hContraction⟩ :=
    physical_exponential_damping_contracts_Lp μ A F 2 hA hExpMeas hF
  exact ⟨hActual, hContraction.trans hEstimate⟩

#print axioms physical_exponential_damping_contracts_Lp
#print axioms physical_damped_kernel_hessian_L2_and_bound

end SeismicitySignedPhysicalDampedKernelHessian
end ReservoirSeismicityControl
