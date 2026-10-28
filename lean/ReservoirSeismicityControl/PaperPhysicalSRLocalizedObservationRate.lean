import ReservoirSeismicityControl.PaperFarLpSelfAdjoint
import ReservoirSeismicityControl.PaperPhysicalWellRates
import Mathlib.Tactic

/-!
# M2 — actual localized signed-SR observation weight in spatial L²

For a fixed physical multiplier `Kγ` representing multiplication by gamma_1,
and the concrete measurable-region L² projection `P`, the moving weight

    w(t) = P (Kγ (R(t)))

has an almost-everywhere strong time derivative P(Kγ(Rdot(t))) whenever the
actual spatial L² seismicity trajectory does. Its derivative and its value
inherit bounds from Rdot, R and Kγ, with no Qdot assumption.

The weight is *automatically localized* (`P w(t)=w(t)`), so its pairing with
an arbitrary spatial vector is bounded by the projected, rather than the
full, spatial vector norm. The physical representative identity is also
proved under the usual identification of Kγ R with gamma_1 * Rphysical.

This discharges SR weight differentiation, localization and L² rate bounds
in Appendix A.3. It does NOT establish membership of this weight in the
weak Neumann generator domain, any off-diagonal semigroup estimate, nor the
full moving near/far derivative theorem. Those are separate obligations.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- Concrete time-dependent SR observation weight localized to a measurable region. -/
noncomputable def paperPhysicalSRLocalizedWeight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (R : ℝ → Lp ℝ (2 : ENNReal) μ) (t : ℝ) :
    Lp ℝ (2 : ENNReal) μ :=
  paperFarLpProjection μ region hregion (Kγ (R t))

/-- The corresponding physical rate, not an independently chosen observation rate. -/
noncomputable def paperPhysicalSRLocalizedWeightRate
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (Rdot : ℝ → Lp ℝ (2 : ENNReal) μ) (t : ℝ) :
    Lp ℝ (2 : ENNReal) μ :=
  paperFarLpProjection μ region hregion (Kγ (Rdot t))

/-- The actual L² weight is equal to the spatial cutoff of
`gamma_1(x) * Rphysical(t,x)`, almost everywhere. -/
theorem paper_physical_sr_localized_weight_representative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (R : ℝ → Lp ℝ (2 : ENNReal) μ)
    (hrep : ∀ t : ℝ, ∀ᵐ x ∂μ,
      ((Kγ (R t)) x : ℝ) = γ₁ x * Rphysical t x)
    (t : ℝ) :
    (paperPhysicalSRLocalizedWeight μ region hregion Kγ R t : X → ℝ) =ᵐ[μ]
      region.indicator (fun x => γ₁ x * Rphysical t x) := by
  filter_upwards
      [paper_far_lp_cutoff_coeFn μ region hregion (Kγ (R t)), hrep t]
    with x hcut hident
  change (paperFarLpCutoff μ region hregion (Kγ (R t)) : X → ℝ) x =
    region.indicator (fun x => γ₁ x * Rphysical t x) x
  rw [hcut]
  by_cases hx : x ∈ region
  · simp only [Set.indicator_of_mem hx]
    exact hident
  · simp only [Set.indicator_of_notMem hx]

/-- The physical localized SR observation has an actual L² derivative,
a uniform rate estimate, a uniform value estimate, and a projected pairing
bound. The only differentiability assumed is that of the physical SR state.
Both signed SR models obey this result because Kγ is a fixed multiplier. -/
theorem paper_physical_sr_localized_observation_certificates
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ (2 : ENNReal) μ →L[ℝ] Lp ℝ (2 : ENNReal) μ)
    (R Rdot : ℝ → Lp ℝ (2 : ENNReal) μ)
    (Cγ CR MR : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t : ℝ, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR) :
    let P := paperFarLpProjection μ region hregion
    let w := paperPhysicalSRLocalizedWeight μ region hregion Kγ R
    let wdot := paperPhysicalSRLocalizedWeightRate μ region hregion Kγ Rdot
    (∀ t : ℝ, P (w t) = w t) ∧
    (∀ᵐ t ∂paperPositiveTime, HasDerivAt w (wdot t) t) ∧
    (∀ᵐ t ∂paperPositiveTime, ‖wdot t‖ ≤ Cγ * CR) ∧
    (∀ t : ℝ, ‖w t‖ ≤ Cγ * MR) ∧
    (∀ t : ℝ, ∀ v : Lp ℝ (2 : ENNReal) μ,
      |⟪w t, v⟫_ℝ| ≤ (Cγ * MR) * ‖P v‖) := by
  classical
  let P := paperFarLpProjection μ region hregion
  let w := paperPhysicalSRLocalizedWeight μ region hregion Kγ R
  let wdot := paperPhysicalSRLocalizedWeightRate μ region hregion Kγ Rdot
  change (∀ t : ℝ, P (w t) = w t) ∧
    (∀ᵐ t ∂paperPositiveTime, HasDerivAt w (wdot t) t) ∧
    (∀ᵐ t ∂paperPositiveTime, ‖wdot t‖ ≤ Cγ * CR) ∧
    (∀ t : ℝ, ‖w t‖ ≤ Cγ * MR) ∧
    (∀ t : ℝ, ∀ v : Lp ℝ (2 : ENNReal) μ,
      |⟪w t, v⟫_ℝ| ≤ (Cγ * MR) * ‖P v‖)
  have hvalue : ∀ t : ℝ, ‖w t‖ ≤ Cγ * MR := by
    intro t
    change ‖P (Kγ (R t))‖ ≤ Cγ * MR
    calc
      ‖P (Kγ (R t))‖ ≤ ‖Kγ (R t)‖ :=
        paper_far_lp_projection_norm_le μ region hregion (Kγ (R t))
      _ ≤ ‖Kγ‖ * ‖R t‖ := Kγ.le_opNorm (R t)
      _ ≤ Cγ * ‖R t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ Cγ * MR := mul_le_mul_of_nonneg_left (hR t) hCγ
  refine ⟨?_, ?_, ?_, hvalue, ?_⟩
  · intro t
    change P (P (Kγ (R t))) = P (Kγ (R t))
    exact paper_far_lp_projection_idempotent μ region hregion (Kγ (R t))
  · filter_upwards [hderiv] with t ht
    change HasDerivAt (fun s => (P.comp Kγ) (R s))
      ((P.comp Kγ) (Rdot t)) t
    exact (P.comp Kγ).hasFDerivAt.comp_hasDerivAt t ht
  · filter_upwards [hrate] with t ht
    change ‖P (Kγ (Rdot t))‖ ≤ Cγ * CR
    calc
      ‖P (Kγ (Rdot t))‖ ≤ ‖Kγ (Rdot t)‖ :=
        paper_far_lp_projection_norm_le μ region hregion (Kγ (Rdot t))
      _ ≤ ‖Kγ‖ * ‖Rdot t‖ := Kγ.le_opNorm (Rdot t)
      _ ≤ Cγ * ‖Rdot t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ Cγ * CR := mul_le_mul_of_nonneg_left ht hCγ
  · intro t v
    change |⟪P (Kγ (R t)), v⟫_ℝ| ≤ (Cγ * MR) * ‖P v‖
    have hlocal : |⟪P (Kγ (R t)), v⟫_ℝ| ≤
        ‖P (Kγ (R t))‖ * ‖P v‖ :=
      paper_far_projected_inner_bound P
        (paper_far_lp_projection_selfAdjoint μ region hregion)
        (P (Kγ (R t))) v
        (paper_far_lp_projection_idempotent μ region hregion (Kγ (R t)))
    exact hlocal.trans (mul_le_mul_of_nonneg_right (hvalue t) (norm_nonneg _))

#print axioms ReservoirSeismicityControl.paper_physical_sr_localized_weight_representative
#print axioms ReservoirSeismicityControl.paper_physical_sr_localized_observation_certificates

end ReservoirSeismicityControl
