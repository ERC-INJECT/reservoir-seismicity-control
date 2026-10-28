import ReservoirSeismicityControl.SeismicitySignedPhysicalTimeIntegratedCoefficient
import ReservoirSeismicityControl.SeismicitySignedPhysicalLocalH2
import ReservoirSeismicityControl.SeismicitySignedPhysicalKernelHessian
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1 — full mixed 3D classical kernel differentiation

For a fixed lag (t-v), the actual spatial kernel is K = exp(-A) b.
The old `SeismicitySignedPhysicalLocalH2` proved its one-dimensional
section derivatives; this file supplies ALL 3 first derivatives and
ALL 9 ordered mixed second derivatives on `Fin 3 → ℝ`.

The hypotheses are the ordinary *classical coordinate derivatives* of A,
b, and their first-derivative fields. No bounded first derivatives are
assumed. The resulting five-term formula is the one whose L² integrability
and quantitative bound were already proved in
`SeismicitySignedPhysicalKernelHessian` under L⁶/L²/L∞ physical data.

This theorem is useful for a smooth approximation of the physical
coefficients, but it DOES NOT yet identify the formula as a weak H²
derivative for nonsmooth coefficients. In particular it does not assume,
construct, or prove the H² smooth approximation, compactly supported test
functions, and strong/weak limiting step. Hence M1 remains open.
No sorry, admit, or extra axiom.
-/

namespace ReservoirSeismicityControl
namespace SeismicitySignedPhysicalThreeDimensionalKernel

/-- A true coordinate section through a 3D point. -/
def section3 (f : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (x : Fin 3 → ℝ) : ℝ → ℝ :=
  fun z => f (Function.update x i z)

private theorem update_at_coordinate (x : Fin 3 → ℝ) (i : Fin 3) :
    Function.update x i (x i) = x := by
  funext j
  by_cases hij : j = i
  · subst j
    simp
  · simp [hij]

/-- The actual scalar spatial kernel (not an assumed Hessian field). -/
noncomputable def spatialKernel3 (A b : (Fin 3 → ℝ) → ℝ) :
    (Fin 3 → ℝ) → ℝ :=
  fun x => Real.exp (-A x) * b x

/-- The first-order expression dictated by differentiation of `spatialKernel3`. -/
noncomputable def spatialKernelFirst3
    (A b : (Fin 3 → ℝ) → ℝ)
    (DA Db : Fin 3 → (Fin 3 → ℝ) → ℝ) :
    Fin 3 → (Fin 3 → ℝ) → ℝ :=
  fun i x => Real.exp (-A x) * (Db i x - DA i x * b x)

/-- The full five-term mixed 3D kernel Hessian candidate. -/
noncomputable def spatialKernelSecond3
    (A b : (Fin 3 → ℝ) → ℝ)
    (DA Db : Fin 3 → (Fin 3 → ℝ) → ℝ)
    (DDA DDb : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) :
    Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ :=
  fun i j x => Real.exp (-A x) *
    (DDb i j x - DA i x * Db j x - DA j x * Db i x -
      DDA i j x * b x + (DA i x * DA j x) * b x)

/-- On every coordinate section, the derivative of the *actual* 3D
kernel equals its physical first-order expression. All three coordinates
are handled in a single theorem, rather than reducing to one fixed axis. -/
theorem spatialKernel3_first_all
    (A b : (Fin 3 → ℝ) → ℝ)
    (DA Db : Fin 3 → (Fin 3 → ℝ) → ℝ)
    (hA : ∀ i x, HasDerivAt (section3 A i x) (DA i x) (x i))
    (hb : ∀ i x, HasDerivAt (section3 b i x) (Db i x) (x i)) :
    ∀ i x, HasDerivAt
      (section3 (spatialKernel3 A b) i x)
      (spatialKernelFirst3 A b DA Db i x) (x i) := by
  intro i x
  have ha' : HasDerivAt (section3 A i x)
      ((section3 (DA i) i x) (x i)) (x i) := by
    simpa only [section3, update_at_coordinate] using hA i x
  have hb' : HasDerivAt (section3 b i x)
      ((section3 (Db i) i x) (x i)) (x i) := by
    simpa only [section3, update_at_coordinate] using hb i x
  have h := sr_signed_kernel_integrand_first_spatial_derivative
    (section3 A i x) (section3 (DA i) i x)
    (section3 b i x) (section3 (Db i) i x)
    (x i) ha' hb'
  -- The coordinate-section function is definitionally the kernel product;
  -- only the derivative VALUE needs `update x i (x i) = x`.
  convert h using 1
  all_goals
    first
    | rfl
    | simp only [section3, spatialKernel3, spatialKernelFirst3,
        update_at_coordinate, Pi.mul_apply, Pi.sub_apply] <;> ring

/-- Every mixed derivative `∂ⱼ(∂ᵢK)` is computed directly from the
*physical* exponential product. In particular the diagonal and the six
off-diagonal ordered derivatives are all covered. No symmetry of the
second-derivative input arrays is required. -/
theorem spatialKernel3_second_all
    (A b : (Fin 3 → ℝ) → ℝ)
    (DA Db : Fin 3 → (Fin 3 → ℝ) → ℝ)
    (DDA DDb : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (hA : ∀ i x, HasDerivAt (section3 A i x) (DA i x) (x i))
    (hb : ∀ i x, HasDerivAt (section3 b i x) (Db i x) (x i))
    (hDA : ∀ i j x, HasDerivAt (section3 (DA i) j x)
        (DDA i j x) (x j))
    (hDb : ∀ i j x, HasDerivAt (section3 (Db i) j x)
        (DDb i j x) (x j)) :
    ∀ i j x, HasDerivAt
      (section3 (spatialKernelFirst3 A b DA Db i) j x)
      (spatialKernelSecond3 A b DA Db DDA DDb i j x) (x j) := by
  intro i j x
  let slice := fun (f : (Fin 3 → ℝ) → ℝ) => section3 f j x
  have ha' : HasDerivAt (slice A)
      ((slice (DA j)) (x j)) (x j) := by
    simpa only [slice, section3, update_at_coordinate] using hA j x
  have hE := sr_signed_kernel_first_spatial_derivative
    (slice A) (slice (DA j)) (x j) ha'
  have hInside := (hDb i j x).sub ((hDA i j x).mul (hb j x))
  have h := hE.mul hInside
  -- The only remaining step is the scalar mixed Leibniz identity.
  -- The reduction `update x j (x j)=x` is critical to prevent mixing
  -- coordinate sections at different base points.
  convert h using 1
  all_goals
    first
    | rfl
    | simp only [slice, section3, spatialKernelFirst3, spatialKernelSecond3,
        update_at_coordinate, Pi.mul_apply, Pi.sub_apply] <;> ring

/-- A single result delivering the full 3D 3+9 derivative identity
for the physical smooth exponential kernel. -/
theorem spatialKernel3_classical_complete
    (A b : (Fin 3 → ℝ) → ℝ)
    (DA Db : Fin 3 → (Fin 3 → ℝ) → ℝ)
    (DDA DDb : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (hA : ∀ i x, HasDerivAt (section3 A i x) (DA i x) (x i))
    (hb : ∀ i x, HasDerivAt (section3 b i x) (Db i x) (x i))
    (hDA : ∀ i j x, HasDerivAt (section3 (DA i) j x)
        (DDA i j x) (x j))
    (hDb : ∀ i j x, HasDerivAt (section3 (Db i) j x)
        (DDb i j x) (x j)) :
    (∀ i x, HasDerivAt (section3 (spatialKernel3 A b) i x)
        (spatialKernelFirst3 A b DA Db i x) (x i)) ∧
    (∀ i j x, HasDerivAt
        (section3 (spatialKernelFirst3 A b DA Db i) j x)
        (spatialKernelSecond3 A b DA Db DDA DDb i j x) (x j)) := by
  exact ⟨spatialKernel3_first_all A b DA Db hA hb,
    spatialKernel3_second_all A b DA Db DDA DDb hA hb hDA hDb⟩

-- The five-term weak-H² L² integrability/bound is already available
-- once these classical expressions are identified as weak derivatives.
#check ReservoirSeismicityControl.sr_signed_physical_kernel_hessian_memLp2
#check ReservoirSeismicityControl.sr_signed_physical_kernel_hessian_L2_bound
#print axioms spatialKernel3_first_all
#print axioms spatialKernel3_second_all
#print axioms spatialKernel3_classical_complete

end SeismicitySignedPhysicalThreeDimensionalKernel
end ReservoirSeismicityControl
