import ReservoirSeismicityControl.Paper2026.PhysicalA9TruncatedMildProjection
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): finite-well physical truncated mild term = scalar causal convolution

The previous accepted `PhysicalA9TruncatedMildProjection` theorem commutes
far spatial projection with a truncated Bochner mild integral.  Here we
identify the pairing of that *same physical integral* against the actual
smooth SR far weight with the **finite sum of frozen-observation scalar
kernels** in the paper.

The rate Q is not differentiated; it may be merely measurable and bounded.
The two positive-lag integrability statements below are the standard
analytic-semigroup applicability inputs.  They are NOT the unknown A9
observation-derivative identity.

This is not the epsilon-to-zero passage and does not establish (A9) in full.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Exact physical scalar-kernel identification for the positive-lag
finite-well portion of the pressure mild solution. No `Qdot` premise. -/
theorem paper_A9_physical_truncated_SR_scalar_causal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Q : Fin n → ℝ → ℝ)
    (initial : Lp ℝ 2 μ) (t ε : ℝ)
    (hInt : Integrable
      (fun s : ℝ => ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t - ε))))
    (hScalar : ∀ j : Fin n, Integrable
      (fun s : ℝ => Q j s *
        paperSRFarSmoothKernel μ region hregion Kγ R
          gamma10 R0star cutoff V E hsep orbit t j (t - s))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t - ε)))) :
    let w := paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t
    ⟪w, initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε),
      ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))⟫_ℝ =
      ⟪w, initial⟫_ℝ +
        ∑ j : Fin n, ∫ s in Set.Ioc (0 : ℝ) (t - ε),
          Q j s * paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t j (t - s) := by
  let w : Lp ℝ 2 μ := paperSRFarDiffusionWeight μ region hregion Kγ R
    gamma10 R0star cutoff t
  let μT : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t - ε))
  let F : ℝ → Lp ℝ 2 μ := fun s =>
    ∑ j : Fin n, (Q j s) •
      ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))
  let kernel : Fin n → ℝ → ℝ := fun j s => Q j s *
    paperSRFarSmoothKernel μ region hregion Kγ R
      gamma10 R0star cutoff V E hsep orbit t j (t - s)
  let T : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ w
  have hpair : ⟪w, ∫ s, F s ∂μT⟫_ℝ =
      ∫ s, ⟪w, F s⟫_ℝ ∂μT := by
    simpa only [T, innerSL_apply_apply] using
      (T.integral_comp_comm (show Integrable F μT from hInt)).symm
  have hpoint (s : ℝ) : ⟪w, F s⟫_ℝ =
      ∑ j : Fin n, kernel j s := by
    simp only [F, kernel, inner_sum, real_inner_smul_right,
      paperSRFarSmoothKernel,
      ReservoirSeismicityControl.paperFarWeakNeumannKernel, innerSL_apply_apply]
    rfl
  have hsum : (∫ s, (∑ j : Fin n, kernel j s) ∂μT) =
      ∑ j : Fin n, ∫ s, kernel j s ∂μT := by
    simpa using
      (integral_finset_sum (μ := μT) (Finset.univ)
        (fun j _ => (hScalar j : Integrable (kernel j) μT)))
  change ⟪w, initial + ∫ s, F s ∂μT⟫_ℝ =
    ⟪w, initial⟫_ℝ + ∑ j : Fin n, ∫ s, kernel j s ∂μT
  rw [inner_add_right, hpair]
  have hIntegralPoint : (∫ s, ⟪w, F s⟫_ℝ ∂μT) =
      ∫ s, ∑ j : Fin n, kernel j s ∂μT := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint
  rw [hIntegralPoint, hsum]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_truncated_SR_scalar_causal
