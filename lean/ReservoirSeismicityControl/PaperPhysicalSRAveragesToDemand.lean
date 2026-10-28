import ReservoirSeismicityControl.PaperPhysicalDemandFinalCertificates
import ReservoirSeismicityControl.PaperPhysicalWellAverages
import ReservoirSeismicityControl.PaperPhysicalWellMatrixRates

/-!
# Stage 58: actual physical SR well integrals supply Stage 56 inputs

This module replaces Stage 56's independently supplied well-sensitivity
interval, a.e. time derivative, and derivative magnitude premises with
consequences of the spatial well integrals and the L² seismicity trajectory.

We freeze the physical SR state at t=0 for negative times, exactly as in
Stage 49, and represent that extension in L². The representative identity,
a.e. strong L² time derivative and its rate bound remain explicit analytic
inputs from Appendix A.2; this module does NOT derive them from the full PDE.
The scalar `hgeometry` assumption only specifies a uniform *numerical*
upper bound for finitely many positive-volume well factors. It does not
assume any derivative of the well sensitivities or of the fluxes Q.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The well-rate candidate obtained from the strong L² SR time derivative.
This is a concrete normalized Lebesgue mean, not a free function. -/
noncomputable def paperPhysicalSRWellRateFromL2
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (measure : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, measure (well j) ≠ ⊤)
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Rdot : ℝ → Lp ℝ 2 measure) : ℝ → Fin w → ℝ :=
  fun t j => wellMeanL2 measure (well j) (hs j) (hfinite j) (Kγ (Rdot t))

/-- Stages 49--51 discharge all four well-sensitivity premises required by
Stage 56: both sides of the box, a.e. derivative, and a uniform rate bound.
The rate bound is derived from the actual strongly differentiable SR state.
`R_L2` represents the physical SR field frozen at t=0 for negative times. -/
theorem paper_physical_sr_well_stage56_inputs_from_L2
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (measure : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        Rmin j ≤ Rphysical t x ∧ Rphysical t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * Rphysical t x) (well j) measure)
    (R_L2 Rdot : ℝ → Lp ℝ 2 measure)
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ CR Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * Rphysical (max τ 0) x)
    (hSRDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt R_L2 (Rdot t) t)
    (hSRRate : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
          measure.real (well j) ≤ Mh) :
    (∀ t j, γmin * Rmin j ≤
      paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical t j) ∧
    (∀ t j,
      paperNonnegativeTimeWellSensitivities measure well γ₁ Rphysical t j ≤
        γmax * Rmax) ∧
    (∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt
        (fun s => paperNonnegativeTimeWellSensitivities
          measure well γ₁ Rphysical s j)
        (paperPhysicalSRWellRateFromL2 measure well hs
          (fun k => ne_of_lt (hfinite k)) Kγ Rdot t j) t) ∧
    (∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      |paperPhysicalSRWellRateFromL2 measure well hs
        (fun k => ne_of_lt (hfinite k)) Kγ Rdot t j| ≤ Mh) := by
  have hbox := paper_physical_well_sensitivity_box measure well γ₁
    Rphysical γmin γmax Rmax Rmin hfinite hpositive hγmin hRmin
    hγ hR hint
  refine ⟨hbox.1, hbox.2, ?_, ?_⟩
  · intro j
    change ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt
        (fun s => paperPhysicalSRWellMean measure (well j) γ₁
          (fun τ x => Rphysical (max τ 0) x) s)
        (wellMeanL2 measure (well j) (hs j)
          (ne_of_lt (hfinite j)) (Kγ (Rdot t))) t
    exact paper_physical_well_hasDerivAt_from_sr_L2_ae
      measure (well j) (hs j) (ne_of_lt (hfinite j)) γ₁
      (fun τ x => Rphysical (max τ 0) x)
      R_L2 Rdot Kγ (hrep j) hSRDeriv
  · intro j
    have hd := paper_physical_well_hasDerivAt_from_sr_L2_ae
      measure (well j) (hs j) (ne_of_lt (hfinite j)) γ₁
      (fun τ x => Rphysical (max τ 0) x)
      R_L2 Rdot Kγ (hrep j) hSRDeriv
    have hb := paper_physical_well_mean_rate_from_sr_L2_ae
      measure (well j) (hs j) (ne_of_lt (hfinite j))
      (hpositive j) γ₁
      (fun τ x => Rphysical (max τ 0) x)
      R_L2 Rdot Kγ Cγ CR hCγ hK (hrep j) hSRDeriv hSRRate
    filter_upwards [hd, hb] with t hdt hbt
    change |deriv (fun s => paperPhysicalSRWellMean measure (well j) γ₁
      (fun τ x => Rphysical (max τ 0) x) s) t| ≤
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        measure.real (well j) at hbt
    rw [hdt.deriv] at hbt
    exact hbt.trans (hgeometry j)

end ReservoirSeismicityControl
