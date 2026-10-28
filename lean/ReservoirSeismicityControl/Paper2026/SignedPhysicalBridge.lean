import ReservoirSeismicityControl.Paper2026.Scope
import ReservoirSeismicityControl.PaperPhysicalWellAverages
import ReservoirSeismicityControl.PaperPhysicalSRMultiwellInverse
import ReservoirSeismicityControl.PaperPhysicalDemandSensitivity
import ReservoirSeismicityControl.SeismicityUniformBounds

/-!
# P0 / P2: the manuscript's signed *physical* SR model

Equation (3) has s * gamma_1 * R * u_t. The SR tracking error (12)
contains another s. At the spatial well level, the input coefficient in
(15) is therefore positive and independent of s. Here its sensitivity is
the real spatial integral on V_j^*, reused from `PaperPhysicalWellAverages`.

We also reuse the already-proved s = -1 logistic differentiation theorem,
with the effective coefficient -s * gamma_1. This establishes the
pointwise signed logistic identity of Appendix A.2 for BOTH signs without
proving any new general calculus or Sobolev theorem.

Limits: differentiating regional Lebesgue integrals (P0), Caratheodory/a.e.
SR ODE integration, and local H2 regularity (P2) remain separate paper
obligations. The old Appendix B matrix `paperPhysicalSRWellMatrix` has a
negative sign: it is NOT the equation (15) matrix for the latest manuscript.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- Eq. (15), retaining the *actual* Lebesgue mean of gamma_1 R on V_j^*.
`normalization = gamma_10 * R_0^* > 0` in the manuscript. -/
noncomputable def srPhysicalMatrix
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then
    paperPhysicalSRWellMean μ (well j) γ₁ R t /
      (normalization * β * volume i) else 0

/-- The SR input coefficient BEFORE the s*s cancellation in (12)--(15).
The mean is a physical well integral; it is not an abstract sensitivity. -/
noncomputable def srSignedPhysicalMatrix
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (s normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then
    (s * (s * paperPhysicalSRWellMean μ (well j) γ₁ R t)) /
      (normalization * β * volume i) else 0

/-- P0: the *complete regional well input matrix*, not just a scalar
sensitivity, is independent of the signed SR convention. -/
theorem sr_signed_physical_matrix_eq
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (s normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ)
    (hs : admissibleSRSign s) :
    srSignedPhysicalMatrix μ well γ₁ R wellRegion s normalization β volume t =
      srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp only [srSignedPhysicalMatrix, srPhysicalMatrix, if_pos hj]
    rw [signed_sr_input_coefficient s _ hs]
  · simp [srSignedPhysicalMatrix, srPhysicalMatrix, hj]

/-- P0, equation (13): cancellation holds for the regional well action on
*any* finite-dimensional well flux Q, not only for individual columns. -/
theorem sr_signed_physical_action_eq
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (s normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ)
    (Q : Fin w → ℝ) (hs : admissibleSRSign s) :
    (srSignedPhysicalMatrix μ well γ₁ R wellRegion s normalization β volume t).mulVec Q =
      (srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t).mulVec Q := by
  rw [sr_signed_physical_matrix_eq μ well γ₁ R wellRegion
    s normalization β volume t hs]

/-- Eq. (12): ordinary differentiation of the signed regional tracking
error. The spatial part of y_R'(t) is handled by the manuscript's
integration/differentiation estimates, not asserted here. -/
theorem signed_sr_error_hasDerivAt
    (s normalization : ℝ)
    (yR rR : ℝ → ℝ) (dyR drR t : ℝ)
    (hy : HasDerivAt yR dyR t) (hr : HasDerivAt rR drR t) :
    HasDerivAt (fun τ => (s / normalization) * (yR τ - rR τ))
      ((s / normalization) * (dyR - drR)) t := by
  exact (hy.sub hr).const_mul (s / normalization)

/-- The exact nominal SR row (17), with positive coefficients on supported wells. -/
noncomputable def srNominalMatrix {r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β₀ : ℝ) (volume : Fin r → ℝ) :
    Matrix (Fin r) (Fin w) ℝ :=
  fun i j => if wellRegion j = some i then 1 / (β₀ * volume i) else 0

/-- P0 -> P4: the physical spatial integral in (15) is exactly the
normalized multiwell matrix used by the existing gain certificates, with
the *pressure ratio* β₀/β restored. Assumptions β₀>0 and |V_Ri|>0
are already required in the paper. -/
theorem sr_physical_eq_normalized_nominal
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (normalization β β₀ : ℝ) (volume : Fin r → ℝ) (t : ℝ)
    (hnormalization : normalization ≠ 0) (hβ : β ≠ 0)
    (hβ₀ : β₀ ≠ 0) (hvolume : ∀ i, volume i ≠ 0) :
    srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t =
      (β₀ / β) • paperNormalizedSRMultiwellMatrix
        (srNominalMatrix wellRegion β₀ volume)
        (fun j => paperPhysicalSRWellMean μ (well j) γ₁ R t)
        normalization := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp only [srPhysicalMatrix, paperNormalizedSRMultiwellMatrix,
      srNominalMatrix, Matrix.smul_apply, smul_eq_mul, if_pos hj]
    field_simp [hnormalization, hβ, hβ₀, hvolume i] <;> ring
  · simp [srPhysicalMatrix, paperNormalizedSRMultiwellMatrix,
      srNominalMatrix, hj, Matrix.smul_apply]

/-- P0: positivity of a supported SR well coefficient follows from the
actual spatial γ₁ R integral and the positive bounds of Assumptions 3,5,
not from an independent assumption that B(t) is positive. -/
theorem sr_physical_supported_entry_positive
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (normalization β : ℝ) (volume : Fin r → ℝ) (t : ℝ)
    (γmin γmax Rmin Rmax : ℝ)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγmin : 0 < γmin) (hRmin : 0 < Rmin)
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rmin ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ j, IntegrableOn (fun x => γ₁ x * R t x) (well j) μ)
    (hnormalization : 0 < normalization) (hβ : 0 < β)
    (hvolume : ∀ i, 0 < volume i)
    (i : Fin r) (j : Fin w) (hj : wellRegion j = some i) :
    0 < srPhysicalMatrix μ well γ₁ R wellRegion normalization β volume t i j := by
  have hm := paper_physical_sr_well_mean_interval μ (well j) γ₁ R
    γmin γmax Rmin Rmax t (hfinite j) (hpositive j) hγmin hRmin
    (hγ j) (hR j) (hint j)
  have hmean : 0 < paperPhysicalSRWellMean μ (well j) γ₁ R t :=
    lt_of_lt_of_le (mul_pos hγmin hRmin) hm.1
  have hden : 0 < normalization * β * volume i :=
    mul_pos (mul_pos hnormalization hβ) (hvolume i)
  simpa only [srPhysicalMatrix, if_pos hj] using (div_pos hmean hden)

/-- The sign of the *previous* `PaperPhysicalDemandSensitivity` SR row is
opposite to the row used in equation (15) of the latest manuscript.
This identity is diagnostic: the legacy matrix is NOT used as the current B. -/
theorem sr_legacy_matrix_is_negative
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ) :
    paperPhysicalSRWellMatrix wellRegion β volume h =
      -(fun i j => if wellRegion j = some i then
          (1 / (β * volume i)) * h j else 0) := by
  classical
  ext i j
  by_cases hj : wellRegion j = some i
  · simp [paperPhysicalSRWellMatrix, hj] <;> ring
  · simp [paperPhysicalSRWellMatrix, hj]

/-- P2: the signed physical SR ODE directly implies the exact logistic
transformation S = R exp(-s γ₁ u) of (A5). No independent logistic ODE is
assumed. The coefficient -s γ₁ is time independent by Assumption 3. -/
theorem signed_physical_sr_logistic_hasDerivAt
    {X : Type*}
    (s : ℝ) (u ut R Rt : X → ℝ → ℝ)
    (γ₁ Rstar : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (hu : ∀ x t, 0 ≤ t → HasDerivAt (u x) (ut x t) t)
    (hR : ∀ x t, 0 ≤ t → HasDerivAt (R x) (Rt x t) t)
    (hODE : ∀ x t, 0 ≤ t →
      Rt x t = s * γ₁ x * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x)) :
    ∀ x t, 0 ≤ t →
      HasDerivAt
        (fun τ => R x τ * Real.exp ((-s * γ₁ x) * u x τ))
        (γ₂ x t * Rstar x * (R x t * Real.exp ((-s * γ₁ x) * u x t)) -
          γ₂ x t * Real.exp (-((-s * γ₁ x) * u x t)) *
            (R x t * Real.exp ((-s * γ₁ x) * u x t)) ^ 2) t := by
  have hOldODE : ∀ x t, 0 ≤ t →
      Rt x t = -((-s * γ₁ x)) * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x) := by
    intro x t ht
    rw [hODE x t ht]
    ring
  exact physical_sr_logistic_hasDerivAt
    u ut R Rt (fun x => -s * γ₁ x) Rstar γ₂ hu hR hOldODE

/-- P2: reuse of the established physical SR two-sided comparison,
now for the signed equation. The scalar transformed coefficient bounds
are explicitly stated and still require checking against the uniform
A.1 pressure bound and A.3 coefficient bounds. No H² conclusion is claimed. -/
theorem signed_physical_sr_uniform_bounds
    {X : Type*}
    (s : ℝ) (u ut R Rt : X → ℝ → ℝ)
    (γ₁ Rstar : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (smin smax amin amax bmin bmax C : ℝ)
    (hsmin : 0 < smin)
    (hinit : ∀ x, smin ≤ R x 0 * Real.exp ((-s * γ₁ x) * u x 0) ∧
      R x 0 * Real.exp ((-s * γ₁ x) * u x 0) ≤ smax)
    (hamin : 0 < amin) (hbmin : 0 < bmin)
    (ha : ∀ x t, 0 ≤ t →
      amin ≤ γ₂ x t * Rstar x ∧ γ₂ x t * Rstar x ≤ amax)
    (hb : ∀ x t, 0 ≤ t →
      bmin ≤ γ₂ x t * Real.exp (-((-s * γ₁ x) * u x t)) ∧
        γ₂ x t * Real.exp (-((-s * γ₁ x) * u x t)) ≤ bmax)
    (hz : ∀ x t, 0 ≤ t → |(-s * γ₁ x) * u x t| ≤ C)
    (hu : ∀ x t, 0 ≤ t → HasDerivAt (u x) (ut x t) t)
    (hR : ∀ x t, 0 ≤ t → HasDerivAt (R x) (Rt x t) t)
    (hODE : ∀ x t, 0 ≤ t →
      Rt x t = s * γ₁ x * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x)) :
    ∀ x t, 0 ≤ t →
      (smin⁻¹ + bmax / amin)⁻¹ / Real.exp C ≤ R x t ∧
        R x t ≤ (min smax⁻¹ (bmin / amax))⁻¹ / Real.exp (-C) := by
  have hOldODE : ∀ x t, 0 ≤ t →
      Rt x t = -((-s * γ₁ x)) * R x t * ut x t -
        γ₂ x t * R x t * (R x t - Rstar x) := by
    intro x t ht
    rw [hODE x t ht]
    ring
  exact physical_sr_uniform_bounds_from_original_ode
    u ut R Rt (fun x => -s * γ₁ x) Rstar γ₂
    smin smax amin amax bmin bmax C
    hsmin hinit hamin hbmin ha hb hz hu hR hOldODE

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.sr_signed_physical_matrix_eq
#print axioms ReservoirSeismicityControl.Paper2026.sr_signed_physical_action_eq
#print axioms ReservoirSeismicityControl.Paper2026.signed_sr_error_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.sr_physical_eq_normalized_nominal
#print axioms ReservoirSeismicityControl.Paper2026.sr_physical_supported_entry_positive
#print axioms ReservoirSeismicityControl.Paper2026.sr_legacy_matrix_is_negative
#print axioms ReservoirSeismicityControl.Paper2026.signed_physical_sr_logistic_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.signed_physical_sr_uniform_bounds
