import ReservoirSeismicityControl.SeismicityPhysicalL2RHS
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl M1: Carathéodory integral SR evolution gives the strong L² derivative a.e.

This module discharges the **strong-time-derivative hypothesis** from a natural
integral formulation of the nonlinear SR ODE. The integral formulation is the
solution notion for time-measurable forcing, not an assumption of time
smoothness. It neither assumes a pointwise classical time derivative nor Qdot.

On a finite physical horizon T, if the SR trajectory satisfies
  R(t) = R(0) + ∫₀ᵗ F(s) ds,   F(s) = -γ₁R(s)uₜ(s) - γ₂(s)R(s)(R(s)-R*),
then its **strong L² derivative** equals F(t) for almost every interior time,
with the uniform rate estimate of Appendix A.2. The earlier verified multiplier
lemmas establish the RHS estimate; here the Banach-valued Lebesgue
differentiation theorem supplies actual time differentiability.

What is not proved here: existence of the physical Carathéodory solution
from the pressure trajectory, its spatial H²(Uj) regularity, or a global
representative that simultaneously satisfies all finite horizons.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped NNReal

/-- A Bochner-integrable SR integral solution has the claimed strong
L² derivative at almost every interior physical time. This is a genuine
Lebesgue-differentiation result, without assuming `HasDerivAt R`.
It applies to all Banach-valued absolutely continuous integral solutions. -/
theorem sr_integrated_L2_evolution_hasDerivAt_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : NNReal)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (hIntegrable : IntervalIntegrable Rdot volume (0 : ℝ) (T : ℝ))
    (hIntegrated : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s) :
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt R (Rdot t) t := by
  have hAE := hIntegrable.ae_hasDerivAt_integral
  filter_upwards [hAE] with t ht
  intro htInterior
  have htClosed : t ∈ Set.uIcc (0 : ℝ) (T : ℝ) := by
    rw [Set.uIcc_of_le T.coe_nonneg]
    exact ⟨htInterior.1.le, htInterior.2.le⟩
  have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) (T : ℝ) := by
    rw [Set.uIcc_of_le T.coe_nonneg]
    exact ⟨le_refl _, T.coe_nonneg⟩
  have hPrimitive :
      HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, Rdot s)
        (Rdot t) t := ht htClosed 0 hzero
  have hSum :
      HasDerivAt (fun u : ℝ => R 0 + ∫ s in (0 : ℝ)..u, Rdot s)
        (Rdot t) t := by
    have hD := ((hasDerivAt_const t (R 0)).add hPrimitive)
    have hFunEq :
        ((fun _ : ℝ => R 0) +
          (fun u : ℝ => ∫ s in (0 : ℝ)..u, Rdot s)) =
          (fun u : ℝ => R 0 + ∫ s in (0 : ℝ)..u, Rdot s) := by
      funext u
      rfl
    rw [hFunEq] at hD
    simpa only [zero_add] using hD
  have hLocal : R =ᶠ[𝓝 t]
      (fun u : ℝ => R 0 + ∫ s in (0 : ℝ)..u, Rdot s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htInterior] with u hu
    exact hIntegrated u ⟨hu.1.le, hu.2.le⟩
  exact hSum.congr_of_eventuallyEq hLocal

/-- The **physical SR** integral equation implies BOTH the strong L²
SR derivative and the quantitative rate estimate, a.e. on (0,T).

The hypotheses about bounded coefficients and the pointwise spatial RHS
are the manuscript's SR model. `hIntegrated` is its Carathéodory/Bochner
integral solution identity, not an extra derivative hypothesis.

The spatial multiplier bounds are derived, not assumed. -/
theorem sr_physical_integrated_strong_L2_rate_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : NNReal)
    (γ₁ : X → ℝ) (γ₂ : X → ℝ → ℝ)
    (Rphysical : ℝ → X → ℝ) (Rstar : X → ℝ)
    (γmax γ2max Rmax RstarMax CU CR : ℝ)
    (hγ₁meas : Measurable γ₁)
    (hγ₂meas : ∀ t, Measurable (fun x => γ₂ x t))
    (hRmeas : ∀ t, Measurable (Rphysical t))
    (hRstarmeas : Measurable Rstar)
    (hγmax : 0 ≤ γmax) (hγ2max : 0 ≤ γ2max)
    (hRmax : 0 ≤ Rmax) (hRstarMax : 0 ≤ RstarMax)
    (hγ₁ : ∀ᵐ x ∂μ, |γ₁ x| ≤ γmax)
    (hγ₂ : ∀ t, ∀ᵐ x ∂μ, |γ₂ x t| ≤ γ2max)
    (hR : ∀ t, ∀ᵐ x ∂μ,
      0 ≤ Rphysical t x ∧ Rphysical t x ≤ Rmax)
    (hRstar : ∀ᵐ x ∂μ,
      0 ≤ Rstar x ∧ Rstar x ≤ RstarMax)
    (Udot R_L2 Rdot : ℝ → Lp ℝ 2 μ)
    (hIntegrable : IntervalIntegrable Rdot volume (0 : ℝ) (T : ℝ))
    (hIntegrated : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      R_L2 t = R_L2 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    (hU : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) → ‖Udot t‖ ≤ CU)
    (hRL2 : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) → ‖R_L2 t‖ ≤ CR)
    (hRrep : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        ∀ᵐ x ∂μ, ((R_L2 t) x : ℝ) = Rphysical t x)
    (hODE : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        ∀ᵐ x ∂μ,
          ((Rdot t) x : ℝ) =
            -γ₁ x * Rphysical t x * ((Udot t) x) -
              γ₂ x t * Rphysical t x *
                (Rphysical t x - Rstar x)) :
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt R_L2 (Rdot t) t ∧
          ‖Rdot t‖ ≤
            (γmax * Rmax) * CU +
              (γ2max * (Rmax + RstarMax)) * CR := by
  have hDerivative := sr_integrated_L2_evolution_hasDerivAt_ae
    μ T R_L2 Rdot hIntegrable hIntegrated
  have hfirst : 0 ≤ γmax * Rmax :=
    mul_nonneg hγmax hRmax
  have hsecond : 0 ≤ γ2max * (Rmax + RstarMax) :=
    mul_nonneg hγ2max (add_nonneg hRmax hRstarMax)
  filter_upwards [hDerivative, hU, hRL2, hRrep, hODE]
    with t hDeriv hUt hRt hRep hODEt
  intro ht
  have hRHS := sr_physical_L2_rhs_bound_of_pointwise_ode
    μ γ₁ γ₂ Rphysical Rstar t γmax γ2max Rmax RstarMax
    hγ₁meas (hγ₂meas t) (hRmeas t) hRstarmeas
    hγmax hγ2max hRmax hRstarMax
    hγ₁ (hγ₂ t) (hR t) hRstar
    (Udot t) (R_L2 t) (Rdot t)
    (hRep ht) (hODEt ht)
  refine ⟨hDeriv ht, ?_⟩
  calc
    ‖Rdot t‖ ≤
        (γmax * Rmax) * ‖Udot t‖ +
          (γ2max * (Rmax + RstarMax)) * ‖R_L2 t‖ := hRHS
    _ ≤ (γmax * Rmax) * CU +
        (γ2max * (Rmax + RstarMax)) * CR :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hUt ht) hfirst)
        (mul_le_mul_of_nonneg_left (hRt ht) hsecond)

#print axioms ReservoirSeismicityControl.sr_integrated_L2_evolution_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.sr_physical_integrated_strong_L2_rate_ae

end ReservoirSeismicityControl
