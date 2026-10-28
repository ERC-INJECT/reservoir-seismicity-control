import ReservoirSeismicityControl.Uncertainty
import ReservoirSeismicityControl.PaperPhysicalWellAverages
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl — constructive nominal SR scaling (Appendix A.4)

This independent physical-data milestone follows a focused M1 audit.  It DOES
NOT assume the desired coefficient-mismatch estimate: it derives it from
strictly positive sensitivity intervals, including intervals obtained from
actual physical gamma_1 R well integrals.

For h in [lo,hi], choose the nominal SR sensitivity m=(lo+hi)/2.  The
normalization error is at most (hi-lo)/(hi+lo)<1.  If the paper's nominal
coefficient is written gamma10 * R0star, set gamma10=m/R0star.

The M1 local Sobolev calculus, and the M2 off-diagonal perturbation bounds,
remain separate obligations.  This theorem does not formalize the final
MIMO super-twisting stability theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Constructive midpoint scaling, with the SHARP interval margin.
All bounds are consequences of lo <= h <= hi and lo > 0. -/
theorem paper_sr_midpoint_normalization_uniform
    (lo hi h : ℝ)
    (hloPos : 0 < lo) (hlohi : lo ≤ hi)
    (hhlo : lo ≤ h) (hhhi : h ≤ hi) :
    let nominal := (lo + hi) / 2
    let margin := (hi - lo) / (lo + hi)
    0 < nominal ∧ 0 ≤ margin ∧ margin < 1 ∧
      |h / nominal - 1| ≤ margin := by
  dsimp
  have hsum : 0 < lo + hi := by linarith
  have hnom : 0 < (lo + hi) / 2 := by linarith
  have hnonneg : 0 ≤ (hi - lo) / (lo + hi) :=
    div_nonneg (sub_nonneg.mpr hlohi) (le_of_lt hsum)
  have hmargin : (hi - lo) / (lo + hi) < 1 := by
    simpa only [add_comm hi lo] using
      (sr_midpoint_margin lo hi hloPos hlohi)
  have hscale : h / ((lo + hi) / 2) - 1 =
      (2 * h - (lo + hi)) / (lo + hi) := by
    field_simp [ne_of_gt hsum, ne_of_gt hnom]
    <;> ring
  refine ⟨hnom, hnonneg, hmargin, ?_⟩
  rw [hscale]
  apply abs_le.mpr
  constructor
  · have hnum : -(hi - lo) ≤ 2 * h - (lo + hi) := by linarith
    calc
      -((hi - lo) / (lo + hi)) = (-(hi - lo)) / (lo + hi) := by ring
      _ ≤ (2 * h - (lo + hi)) / (lo + hi) := by
        apply (div_le_div_iff₀ hsum hsum).2
        exact mul_le_mul_of_nonneg_right hnum (le_of_lt hsum)
  · have hnum : 2 * h - (lo + hi) ≤ hi - lo := by linarith
    apply (div_le_div_iff₀ hsum hsum).2
    exact mul_le_mul_of_nonneg_right hnum (le_of_lt hsum)

/-- The constructive choice of gamma10 in the paper's convention
`nominal SR sensitivity = gamma10 * R0star`.  It is positive and gives
exactly the midpoint normalization of the physical sensitivity box. -/
theorem paper_sr_gamma10_constructive_choice
    (lo hi R0star : ℝ)
    (hloPos : 0 < lo) (hlohi : lo ≤ hi)
    (hRstar : 0 < R0star) :
    let gamma10 := ((lo + hi) / 2) / R0star
    0 < gamma10 ∧ gamma10 * R0star = (lo + hi) / 2 := by
  dsimp
  have hnom : 0 < (lo + hi) / 2 := by linarith
  constructor
  · exact div_pos hnom hRstar
  · exact div_mul_cancel₀ _ (ne_of_gt hRstar)

/-- The actual pressure coefficient beta0/beta and every normalized SR
sensitivity share ONE explicitly constructed strict margin. No gain-error
margin is passed as a hypothesis. -/
theorem paper_pressure_sr_constructive_margin
    (beta beta0 lo hi : ℝ)
    (hbeta : 0 < beta) (hbeta0 : 0 < beta0)
    (hbetaUpper : beta0 < 2 * beta)
    (hloPos : 0 < lo) (hlohi : lo ≤ hi) :
    let margin := max |beta0 / beta - 1| ((hi - lo) / (lo + hi))
    0 ≤ margin ∧ margin < 1 ∧
      ∀ h : ℝ, lo ≤ h → h ≤ hi →
        |h / ((lo + hi) / 2) - 1| ≤ margin := by
  dsimp
  have hp : |beta0 / beta - 1| < 1 :=
    pressure_only_uncertainty beta beta0 hbeta hbeta0 hbetaUpper
  have hs : (hi - lo) / (lo + hi) < 1 := by
    simpa only [add_comm hi lo] using
      (sr_midpoint_margin lo hi hloPos hlohi)
  refine ⟨(abs_nonneg _).trans (le_max_left _ _),
    max_lt hp hs, ?_⟩
  intro h hlow hhigh
  have hlocal := paper_sr_midpoint_normalization_uniform
    lo hi h hloPos hlohi hlow hhigh
  exact hlocal.2.2.2.trans (le_max_right _ _)

/-- Appendix A.4 nominal coefficient, instantiated from the ACTUAL spatial
well integrals gamma_1 R. This consumes the physically derived interval
certificate of `paper_physical_well_sensitivity_box` and produces one
strict bound for every well and every time. In particular, it does NOT
assume an SR gain mismatch, or its bound, as a separate premise. -/
theorem paper_physical_well_constructive_gain_margin
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (gamma1 : X → ℝ) (R : ℝ → X → ℝ)
    (gammaMin gammaMax Rmax Rlower : ℝ) (Rmin : Fin w → ℝ)
    (hgammaMin : 0 < gammaMin) (hRlower : 0 < Rlower)
    (hgammaOrder : gammaMin ≤ gammaMax)
    (hRmaxOrder : Rlower ≤ Rmax)
    (hRmin : ∀ j, Rlower ≤ Rmin j)
    (hRminPos : ∀ j, 0 < Rmin j)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hgamma : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      gammaMin ≤ gamma1 x ∧ gamma1 x ≤ gammaMax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(μ.restrict (well j)),
        Rmin j ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => gamma1 x * R t x) (well j) μ)
    (beta beta0 : ℝ)
    (hbeta : 0 < beta) (hbeta0 : 0 < beta0)
    (hbetaUpper : beta0 < 2 * beta) :
    let lo := gammaMin * Rlower
    let hi := gammaMax * Rmax
    let nominal := (lo + hi) / 2
    let margin := max |beta0 / beta - 1| ((hi - lo) / (lo + hi))
    0 < nominal ∧ 0 ≤ margin ∧ margin < 1 ∧
      ∀ (t : ℝ) (j : Fin w),
        |paperNonnegativeTimeWellSensitivities μ well gamma1 R t j /
          nominal - 1| ≤ margin := by
  dsimp
  have hbox := paper_physical_well_sensitivity_box
    μ well gamma1 R gammaMin gammaMax Rmax Rmin
    hfinite hpositive hgammaMin hRminPos hgamma hR hint
  have hloPos : 0 < gammaMin * Rlower :=
    mul_pos hgammaMin hRlower
  have hlohi : gammaMin * Rlower ≤ gammaMax * Rmax := by
    have hRmaxNonneg : 0 ≤ Rmax := (le_of_lt hRlower).trans hRmaxOrder
    calc
      gammaMin * Rlower ≤ gammaMin * Rmax :=
        mul_le_mul_of_nonneg_left hRmaxOrder (le_of_lt hgammaMin)
      _ ≤ gammaMax * Rmax :=
        mul_le_mul_of_nonneg_right hgammaOrder hRmaxNonneg
  have hnom : 0 < (gammaMin * Rlower + gammaMax * Rmax) / 2 := by
    linarith
  have hmargin := paper_pressure_sr_constructive_margin
    beta beta0 (gammaMin * Rlower) (gammaMax * Rmax)
    hbeta hbeta0 hbetaUpper hloPos hlohi
  refine ⟨hnom, hmargin.1, hmargin.2.1, ?_⟩
  intro t j
  have hlow : gammaMin * Rlower ≤
      paperNonnegativeTimeWellSensitivities μ well gamma1 R t j :=
    (mul_le_mul_of_nonneg_left (hRmin j) (le_of_lt hgammaMin)).trans
      (hbox.1 t j)
  exact hmargin.2.2 _ hlow (hbox.2 t j)

#print axioms ReservoirSeismicityControl.paper_sr_midpoint_normalization_uniform
#print axioms ReservoirSeismicityControl.paper_sr_gamma10_constructive_choice
#print axioms ReservoirSeismicityControl.paper_pressure_sr_constructive_margin
#print axioms ReservoirSeismicityControl.paper_physical_well_constructive_gain_margin

end ReservoirSeismicityControl
