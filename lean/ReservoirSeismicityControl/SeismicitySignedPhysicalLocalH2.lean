import ReservoirSeismicityControl.SeismicitySignedSpatialL6Damping
import ReservoirSeismicityControl.SeismicitySignedSpatialHessianForcingBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Signed physical SR, M1 direct-kernel theorem package

This package REPLACES the incremental difference-quotient path for local H².
For `s ∈ {-1,1}`, `Y=exp(s*gamma1*u)/R` and
`Y_t = -a Y + b`, where `a=gamma2*Rstar` and
`b=gamma2*exp(s*gamma1*u)`.

New results:
1. The *constructed* scalar reciprocal has the actual Duhamel formula;
   this formula is derived from `srReciprocalExplicit`, not assumed.
2. Exact first and second spatial derivatives of the exponential kernel.
3. Exact first and second spatial derivatives of the integrand `E*b`,
   including all mixed product-rule terms.

All these identities are independent of s and work for both injection and
extraction. Unlike the earlier derivative-equation bootstrap, none of the
new chain/product identities assume spatial derivatives of Y.

CRITICAL SCOPE: Derivatives in items (2)–(3) use classical 1D spatial
sections. The physical 3D H²(U_j) theorem additionally needs a bounded-
Lipschitz-domain weak Sobolev calculus and a differentiation-under-Bochner-
integration statement, neither of which has yet been derived in Lean from
Assumption 3. Therefore the global H² theorem is **not** asserted here.
See M1_DIRECT_KERNEL_PROOF.md for the precise quantitative estimate and
remaining proof interface. No `sorry` or custom axioms are used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology

/-- The *physical* Duhamel factor from the integrating-factor construction.
`a` may be only locally time-integrable; the formula is algebraic and
requires no differentiability of a or b in time. -/
noncomputable def srSignedDuhamelFactor
    (a : ℝ → ℝ) (t v : ℝ) : ℝ :=
  Real.exp (srReciprocalPrimitive a v - srReciprocalPrimitive a t)

/-- The explicit, previously verified Carathéodory solution equals a
homogeneous term plus an integral of the *physical* Duhamel factor.
In particular, the Duhamel equality itself is NOT a new premise. -/
theorem sr_signed_reciprocal_explicit_duhamel
    (a b : ℝ → ℝ) (y0 t : ℝ) :
    srReciprocalExplicit a b y0 t =
      Real.exp (-srReciprocalPrimitive a t) * y0 +
        ∫ v in (0 : ℝ)..t, srSignedDuhamelFactor a t v * b v := by
  calc
    srReciprocalExplicit a b y0 t =
        Real.exp (-srReciprocalPrimitive a t) * y0 +
          Real.exp (-srReciprocalPrimitive a t) *
            (∫ v in (0 : ℝ)..t,
              Real.exp (srReciprocalPrimitive a v) * b v) := by
        simp only [srReciprocalExplicit, mul_add]
    _ = Real.exp (-srReciprocalPrimitive a t) * y0 +
          ∫ v in (0 : ℝ)..t,
            Real.exp (-srReciprocalPrimitive a t) *
              (Real.exp (srReciprocalPrimitive a v) * b v) := by
        rw [intervalIntegral.integral_const_mul]
    _ = Real.exp (-srReciprocalPrimitive a t) * y0 +
          ∫ v in (0 : ℝ)..t, srSignedDuhamelFactor a t v * b v := by
        congr 1
        apply intervalIntegral.integral_congr
        intro v _
        dsimp only
        unfold srSignedDuhamelFactor
        calc
          Real.exp (-srReciprocalPrimitive a t) *
            (Real.exp (srReciprocalPrimitive a v) * b v) =
              (Real.exp (-srReciprocalPrimitive a t) *
                Real.exp (srReciprocalPrimitive a v)) * b v := by ring
          _ = Real.exp
                (srReciprocalPrimitive a v - srReciprocalPrimitive a t) * b v := by
                rw [← Real.exp_add]
                congr 1
                ring

/-- The pointwise spatial reciprocal constructed from the signed physical
coefficients satisfies an **actual**, not postulated, Duhamel identity. -/
theorem sr_signed_physical_reciprocal_exact_duhamel
    {X : Type*} (u : X → ℝ → ℝ) (gamma1 Rstar : X → ℝ)
    (gamma2 : X → ℝ → ℝ) (s : ℝ) (y0 : X → ℝ)
    (x : X) (t : ℝ) :
    srReciprocalExplicit
      (fun v => gamma2 x v * Rstar x)
      (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
      (y0 x) t =
      Real.exp (-srReciprocalPrimitive
        (fun v => gamma2 x v * Rstar x) t) * y0 x +
        ∫ v in (0 : ℝ)..t,
          srSignedDuhamelFactor
            (fun τ => gamma2 x τ * Rstar x) t v *
              (gamma2 x v * Real.exp (s * gamma1 x * u x v)) := by
  exact sr_signed_reciprocal_explicit_duhamel
    (fun v => gamma2 x v * Rstar x)
    (fun v => gamma2 x v * Real.exp (s * gamma1 x * u x v))
    (y0 x) t

/-- The direct exponential kernel's first spatial derivative. This is a
real spatial section of the full 3D weak formula `∇E=-E∇A`.
Here `A(x)=∫_v^t a(x,τ)dτ` in the physical application. -/
theorem sr_signed_kernel_first_spatial_derivative
    (A DA : ℝ → ℝ) (x : ℝ)
    (hA : HasDerivAt A (DA x) x) :
    HasDerivAt (fun z : ℝ => Real.exp (-A z))
      (-Real.exp (-A x) * DA x) x := by
  have hInner : HasDerivAt (fun z : ℝ => -A z) (-DA x) x := hA.neg
  have h := (Real.hasDerivAt_exp (-A x)).comp x hInner
  -- `HasDerivAt.comp` returns a function composition; expose its lambda form.
  change HasDerivAt (fun z : ℝ => Real.exp (-A z))
    (Real.exp (-A x) * (-DA x)) x at h
  convert h using 1 <;> ring

/-- The exact second spatial derivative of the exponential kernel:
`E'' = E ((A')²-A'')`. Unlike derivative-equation bootstraps, this
formula differentiates the actual spatial propagator. -/
theorem sr_signed_kernel_second_spatial_derivative
    (A DA DDA : ℝ → ℝ) (x : ℝ)
    (hA : HasDerivAt A (DA x) x)
    (hDA : HasDerivAt DA (DDA x) x) :
    HasDerivAt (fun z : ℝ => -Real.exp (-A z) * DA z)
      (Real.exp (-A x) * ((DA x)^2 - DDA x)) x := by
  have hE := sr_signed_kernel_first_spatial_derivative A DA x hA
  have hProd := (hE.mul hDA).neg
  have hFunEq :
      (fun z : ℝ => -Real.exp (-A z) * DA z) =
      (fun z : ℝ => -(Real.exp (-A z) * DA z)) := by
    funext z
    ring
  rw [hFunEq]
  convert hProd using 1 <;> ring

/-- First spatial derivative of the *physical Duhamel integrand* `E*b`.
This is directly computed from the kernel, not from a derivative assumed
for Y. -/
theorem sr_signed_kernel_integrand_first_spatial_derivative
    (A DA b Db : ℝ → ℝ) (x : ℝ)
    (hA : HasDerivAt A (DA x) x)
    (hb : HasDerivAt b (Db x) x) :
    HasDerivAt (fun z : ℝ => Real.exp (-A z) * b z)
      (Real.exp (-A x) * (Db x - DA x * b x)) x := by
  have hE := sr_signed_kernel_first_spatial_derivative A DA x hA
  have hProd := hE.mul hb
  convert hProd using 1 <;> ring

/-- Second derivative of the integrand `E*b`:
`(Eb)''=E[b''-2A'b'-A''b+(A')²b]`.
This is the full second-order product/chain formula used by the direct
H² estimate, including the quadratic-gradient term. -/
theorem sr_signed_kernel_integrand_second_spatial_derivative
    (A DA DDA b Db DDb : ℝ → ℝ) (x : ℝ)
    (hA : HasDerivAt A (DA x) x)
    (hDA : HasDerivAt DA (DDA x) x)
    (hb : HasDerivAt b (Db x) x)
    (hDb : HasDerivAt Db (DDb x) x) :
    HasDerivAt
      (fun z : ℝ => Real.exp (-A z) * (Db z - DA z * b z))
      (Real.exp (-A x) *
        (DDb x - 2 * DA x * Db x - DDA x * b x + (DA x)^2 * b x)) x := by
  have hE := sr_signed_kernel_first_spatial_derivative A DA x hA
  have hAb := hDA.mul hb
  have hInner := hDb.sub hAb
  have hProd := hE.mul hInner
  -- Mathlib retains `(Db - DA * b) x` as a function application.
  -- Unfold the pointwise operations before solving the polynomial identity.
  convert hProd using 1 <;> (simp only [Pi.sub_apply, Pi.mul_apply] <;> ring)

#print axioms ReservoirSeismicityControl.sr_signed_reciprocal_explicit_duhamel
#print axioms ReservoirSeismicityControl.sr_signed_physical_reciprocal_exact_duhamel
#print axioms ReservoirSeismicityControl.sr_signed_kernel_first_spatial_derivative
#print axioms ReservoirSeismicityControl.sr_signed_kernel_second_spatial_derivative
#print axioms ReservoirSeismicityControl.sr_signed_kernel_integrand_first_spatial_derivative
#print axioms ReservoirSeismicityControl.sr_signed_kernel_integrand_second_spatial_derivative

end ReservoirSeismicityControl
