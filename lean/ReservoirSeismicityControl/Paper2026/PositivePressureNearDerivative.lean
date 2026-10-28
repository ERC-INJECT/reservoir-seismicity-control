import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: derivative of the fixed pressure-region near observation

For a pressure-output region, the localized observation weight is fixed in time. The paper's self-adjoint Neumann generator permits the transposition

  -<zeta chi_E/|E|, A p(t)> = -<A(zeta chi_E/|E|), p(t)>.

The ordinary strong L2 derivative of p can then be tested against the fixed
vector A(zeta chi_E/|E|). This proves the paper-specific pressure near-field
weak derivative *without* differentiating A p or the well flux Q.

The explicit domain and symmetry premises refer to the same elliptic
regularity/self-adjointness results invoked in Appendix A.3. No theorem about
elliptic or semigroup regularity is reproved here. The time-varying SR weight
requires a separate near-field weak product rule and remains open.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Appendix A.3, pressure channel: derivative of the actual fixed-weight
near observation. In particular, there is no hypothesis on `deriv (A p)` or
on the derivative of the well rates. The domain conditions are the exact
applicability conditions of the paper's cited elliptic regularity theorem. -/
theorem paper_pressure_near_observation_hasDerivAt
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (region : Set X) (hs : MeasurableSet region)
    (hf : mu region ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hSymm : ∀ a b : D,
      ⟪A a, (b : Lp ℝ 2 mu)⟫_ℝ = ⟪(a : Lp ℝ 2 mu), A b⟫_ℝ)
    (pressure pressureRate : ℝ → Lp ℝ 2 mu)
    (hpD : ∀ tau, pressure tau ∈ D)
    (hvD : paperPressureNearWeight mu region hs hf cutoff ∈ D)
    (t : ℝ) (hpRate : HasDerivAt pressure (pressureRate t) t) :
    HasDerivAt
      (fun tau => -⟪paperPressureNearWeight mu region hs hf cutoff,
          A ⟨pressure tau, hpD tau⟩⟫_ℝ)
      (-⟪A ⟨paperPressureNearWeight mu region hs hf cutoff, hvD⟩,
          pressureRate t⟫_ℝ) t := by
  let v : Lp ℝ 2 mu := paperPressureNearWeight mu region hs hf cutoff
  let z : Lp ℝ 2 mu := A ⟨v, hvD⟩
  have htrans :
      (fun tau => -⟪v, A ⟨pressure tau, hpD tau⟩⟫_ℝ) =
      (fun tau => -⟪z, pressure tau⟫_ℝ) := by
    funext tau
    exact congrArg (fun x : ℝ => -x)
      ((hSymm ⟨v, hvD⟩ ⟨pressure tau, hpD tau⟩).symm)
  have hfixed : HasDerivAt
      (fun tau => -⟪z, pressure tau⟫_ℝ)
      (-⟪z, pressureRate t⟫_ℝ) t := by
    -- First expose the continuous linear functional itself. This matches
    -- the pointwise negated function produced by HasDerivAt.neg.
    change HasDerivAt
      (fun tau => -((innerSL ℝ z) (pressure tau)))
      (-((innerSL ℝ z) (pressureRate t))) t
    exact ((innerSL ℝ z).hasFDerivAt.comp_hasDerivAt t hpRate).neg
  change HasDerivAt
    (fun tau => -⟪v, A ⟨pressure tau, hpD tau⟩⟫_ℝ)
    (-⟪z, pressureRate t⟫_ℝ) t
  rw [htrans]
  exact hfixed

/-- The same actual pressure-channel derivative satisfies the A.3 uniform
bound from the cited local elliptic generator estimate and (A4). -/
theorem paper_pressure_near_derivative_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (region : Set X) (hs : MeasurableSet region)
    (hf : mu region ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hvD : paperPressureNearWeight mu region hs hf cutoff ∈ D)
    (CAw CPt : ℝ)
    (hAw : ‖A ⟨paperPressureNearWeight mu region hs hf cutoff, hvD⟩‖ ≤ CAw)
    (pressureRate : Lp ℝ 2 mu) (hPt : ‖pressureRate‖ ≤ CPt) :
    |-⟪A ⟨paperPressureNearWeight mu region hs hf cutoff, hvD⟩,
        pressureRate⟫_ℝ| ≤ CAw * CPt := by
  let z : Lp ℝ 2 mu :=
    A ⟨paperPressureNearWeight mu region hs hf cutoff, hvD⟩
  change |-⟪z, pressureRate⟫_ℝ| ≤ CAw * CPt
  rw [abs_neg]
  have hCS : |⟪z, pressureRate⟫_ℝ| ≤ ‖z‖ * ‖pressureRate‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) z pressureRate)
  calc
    _ ≤ ‖z‖ * ‖pressureRate‖ := hCS
    _ ≤ CAw * ‖pressureRate‖ :=
      mul_le_mul_of_nonneg_right hAw (norm_nonneg _)
    _ ≤ CAw * CPt :=
      mul_le_mul_of_nonneg_left hPt ((norm_nonneg _).trans hAw)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_derivative_bound
