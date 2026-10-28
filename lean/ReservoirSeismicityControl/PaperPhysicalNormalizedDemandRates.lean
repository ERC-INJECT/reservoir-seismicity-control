import ReservoirSeismicityControl.PaperPhysicalGainOpNormRates
import ReservoirSeismicityControl.PaperGainContraction

/-!
# Stage 54: physical demand perturbation and a.e. normalized-rate bound

This module connects the physical well-rate calculations of Stages 51--53 to
Appendix B's normalized perturbation estimate. The rate of the *unallocated*
physical matrix B is first bounded in the induced Euclidean norm. The Stage 53
bound is then used for the *allocated* gain G_W = B C_W.

The last theorem combines those physical bounds with the already established
inverse differentiation and perturbation product rules. The passage from an
actual finite matrix to the corresponding Euclidean continuous linear operator
is kept explicit in the two `hBRateModel`/`hGainRateModel` hypotheses, together
with differentiability of these operator representations. They are finite-
dimensional representation obligations, NOT bounds independently assumed on
Bdot or Gdot. Later stages should discharge these representation obligations.

The regionwise PDE estimate on PsiRate and the small-gain certificate are still
hypotheses from the manuscript. No hypothesis on Qdot or Qddot is introduced.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix
section OperatorNorm
open scoped Matrix.Norms.L2Operator

/-- The unallocated physical matrix rate has a genuine Euclidean operator-norm
bound. This is the counterpart of Stage 53 before multiplying by C_W. -/
theorem paper_physical_well_matrix_rate_opNorm_bound
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ)
    (v : Fin w → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ j : Fin w, |v j| ≤ M) :
    paperMatrixEuclideanOpNorm
      (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume v 0 κ) ≤
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M := by
  classical
  have hvnorm : ‖v‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).2
    intro j
    simpa [Real.norm_eq_abs] using hv j
  have hbound :
      ‖paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume v 0 κ‖ ≤
        ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ * M := by
    rw [paper_physical_demand_rate_geometry_factor]
    calc
      ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
          Matrix.diagonal v‖ ≤
        ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ *
          ‖Matrix.diagonal v‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ *
          ‖v‖ := by rw [Matrix.l2_opNorm_diagonal]
      _ ≤ ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ * M :=
        mul_le_mul_of_nonneg_left hvnorm (norm_nonneg _)
  simpa only [paperMatrixEuclideanOpNorm, ← Matrix.l2_opNorm_def] using hbound

end OperatorNorm

-- Matrix differentiation uses the entrywise norm, not the L2 operator norm.
open scoped Matrix.Norms.Elementwise

/-- A.e. bound for the actual (not hypothesized) derivative of B(h(t)). -/
theorem paper_physical_well_matrix_actual_rate_opNorm_ae
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hrate : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       |hRate t j| ≤ M) :
    ∀ᵐ t ∂paperPositiveTime,
      paperMatrixEuclideanOpNorm
        (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
          wellRegion β volume (h s) α κ) t) ≤
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M := by
  have hdall := paper_physical_well_rates_common_ae h hRate hderiv
  have hrall : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin w, |hRate t j| ≤ M :=
    Filter.eventually_all.mpr hrate
  filter_upwards [hdall, hrall] with t hdt hrt
  rw [paper_physical_demand_matrix_deriv
    Bᵤ₀ wellRegion β volume h hRate α κ t hdt]
  exact paper_physical_well_matrix_rate_opNorm_bound
    Bᵤ₀ wellRegion β volume κ (hRate t) M hM hrt

/-- Appendix B, for the physical demand gain: an explicit uniform upper bound
for the actual normalized perturbation derivative, almost everywhere.

`hBRateModel` and `hGainRateModel` specify that the CLM representations do not
have a larger norm than the *actual* derivatives of the displayed physical
matrices. They are deliberately visible proof obligations. `hBDeriv` and
`hGainDeriv` identify the derivatives of those representations. The scalar
well derivative and its bound are supplied by the SR estimates, not by Qdot.
-/
theorem paper_physical_normalized_demand_rate_bound_ae
    {E U R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (psi psiRate : ℝ → E)
    (B BRate : ℝ → U →L[ℝ] E)
    (FD : R →L[ℝ] U) (D DRate : ℝ → R)
    (gain gainRate : ℝ → E →L[ℝ] E)
    (δ LB Lpsi LpsiRate LD LDRate M : ℝ)
    (hδ : δ < 1) (hLB : 0 ≤ LB)
    (_hLpsi : 0 ≤ Lpsi) (_hLpsiRate : 0 ≤ LpsiRate)
    (_hLD : 0 ≤ LD) (_hLDRate : 0 ≤ LDRate) (hM : 0 ≤ M)
    (hwellDeriv : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hwellRate : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       |hRate t j| ≤ M)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hB : ∀ᵐ t ∂paperPositiveTime, ‖B t‖ ≤ LB)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt psi (psiRate t) t)
    (hBDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt B (BRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt D (DRate t) t)
    (hGainDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt gain (gainRate t) t)
    (hBRateModel : ∀ᵐ t ∂paperPositiveTime,
       ‖BRate t‖ ≤ paperMatrixEuclideanOpNorm
         (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
           wellRegion β volume (h s) α κ) t))
    (hGainRateModel : ∀ᵐ t ∂paperPositiveTime,
       ‖gainRate t‖ ≤ paperMatrixEuclideanOpNorm
         (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
           wellRegion β volume (h s) α κ * C) t))
    (hcontraction : ∀ t, ‖(1 : E →L[ℝ] E) - gain t‖ ≤ δ) :
    ∀ᵐ t ∂paperPositiveTime,
      ‖deriv (fun s : ℝ => Ring.inverse (gain s)
          (paperDemandPsi psi B FD D s)) t‖ ≤
        (1 / (1 - δ)) *
          (LpsiRate +
            (paperMatrixEuclideanOpNorm
              (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M) *
                (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
        (1 / (1 - δ)) *
          ((paperMatrixEuclideanOpNorm
              (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M *
                paperMatrixEuclideanOpNorm C) *
            ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD)))) := by
  let J : ℝ → E →L[ℝ] E := fun s => Ring.inverse (gain s)
  have hRight : ∀ s x, gain s (J s x) = x := by
    intro s x
    exact paper_gain_ringInverse_right_of_contraction
      gain δ hδ hcontraction s x
  have hLeft : ∀ s x, J s (gain s x) = x := by
    intro s x
    exact paper_gain_ringInverse_left_of_contraction
      gain δ hδ hcontraction s x
  have hJDeriv := paper_inverse_gain_hasDerivAt_from_gain_ae
    gain J gainRate hGainDeriv hRight hLeft
  have hJRule := paper_inverse_gain_rule_ae
    gain J gainRate (fun t => deriv J t)
    hGainDeriv hJDeriv hRight hLeft
  have htransport := paper_demand_normalized_psi_deriv_ae
    psi psiRate B BRate FD D DRate J (fun t => deriv J t) gainRate
    hpsiDeriv hBDeriv hDDeriv hJDeriv hJRule
  have hBphysical := paper_physical_well_matrix_actual_rate_opNorm_ae
    Bᵤ₀ wellRegion β volume h hRate α κ M hM hwellDeriv hwellRate
  have hGphysical := paper_physical_demand_actual_gain_rate_opNorm_ae
    Bᵤ₀ wellRegion β volume h hRate α κ C M hM hwellDeriv hwellRate
  let LBR := paperMatrixEuclideanOpNorm
    (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M
  let LGR := LBR * paperMatrixEuclideanOpNorm C
  let LW := Lpsi + LB * (‖FD‖ * LD)
  let LWR := LpsiRate + LBR * (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)
  have hLBR : 0 ≤ LBR := mul_nonneg (norm_nonneg _) hM
  have hLGR : 0 ≤ LGR := mul_nonneg hLBR (norm_nonneg _)
  have hq : 0 ≤ (1 / (1 - δ)) := by
    apply div_nonneg
    · norm_num
    · exact le_of_lt (sub_pos.mpr hδ)
  filter_upwards [htransport, hBphysical, hGphysical,
      hBRateModel, hGainRateModel, hpsi, hpsiRate, hB, hD, hDRate]
    with t htr hBphys hGphys hBRmodel hGRmodel hp hpr hb hd hdr
  have hBR : ‖BRate t‖ ≤ LBR := hBRmodel.trans hBphys
  have hGR : ‖gainRate t‖ ≤ LGR := hGRmodel.trans hGphys
  have hFD : ‖FD (D t)‖ ≤ ‖FD‖ * LD := by
    calc
      _ ≤ ‖FD‖ * ‖D t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖FD‖ * LD := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
  have hFDR : ‖FD (DRate t)‖ ≤ ‖FD‖ * LDRate := by
    calc
      _ ≤ ‖FD‖ * ‖DRate t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖FD‖ * LDRate := mul_le_mul_of_nonneg_left hdr (norm_nonneg _)
  have hBval : ‖B t (FD (D t))‖ ≤ LB * (‖FD‖ * LD) := by
    calc
      _ ≤ ‖B t‖ * ‖FD (D t)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ LB * ‖FD (D t)‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ LB * (‖FD‖ * LD) := mul_le_mul_of_nonneg_left hFD hLB
  have hBRval : ‖BRate t (FD (D t))‖ ≤ LBR * (‖FD‖ * LD) := by
    calc
      _ ≤ ‖BRate t‖ * ‖FD (D t)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ LBR * ‖FD (D t)‖ :=
        mul_le_mul_of_nonneg_right hBR (norm_nonneg _)
      _ ≤ LBR * (‖FD‖ * LD) := mul_le_mul_of_nonneg_left hFD hLBR
  have hBDval : ‖B t (FD (DRate t))‖ ≤ LB * (‖FD‖ * LDRate) := by
    calc
      _ ≤ ‖B t‖ * ‖FD (DRate t)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ LB * ‖FD (DRate t)‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ LB * (‖FD‖ * LDRate) := mul_le_mul_of_nonneg_left hFDR hLB
  have hW : ‖paperDemandPsi psi B FD D t‖ ≤ LW := by
    calc
      _ = ‖psi t + B t (FD (D t))‖ := rfl
      _ ≤ ‖psi t‖ + ‖B t (FD (D t))‖ := norm_add_le _ _
      _ ≤ LW := add_le_add hp hBval
  have hWR : ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ ≤ LWR := by
    change ‖psiRate t + BRate t (FD (D t)) + B t (FD (DRate t))‖ ≤ LWR
    have ha := norm_add_le (psiRate t) (BRate t (FD (D t)))
    have hc := norm_add_le (psiRate t + BRate t (FD (D t)))
      (B t (FD (DRate t)))
    dsimp [LWR]
    linarith
  have hJ : ∀ x, ‖J t x‖ ≤ (1 / (1 - δ)) * ‖x‖ := by
    intro x
    exact paper_gain_ringInverse_action_bound_of_contraction
      gain δ hδ hcontraction t x
  have hGaction : ∀ x, ‖gainRate t x‖ ≤ LGR * ‖x‖ := by
    intro x
    calc
      _ ≤ ‖gainRate t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ LGR * ‖x‖ := mul_le_mul_of_nonneg_right hGR (norm_nonneg _)
  have hfirst :
      ‖J t (paperDemandPsiRate psiRate B BRate FD D DRate t)‖ ≤
        (1 / (1 - δ)) * LWR := by
    calc
      _ ≤ (1 / (1 - δ)) *
        ‖paperDemandPsiRate psiRate B BRate FD D DRate t‖ := hJ _
      _ ≤ (1 / (1 - δ)) * LWR := mul_le_mul_of_nonneg_left hWR hq
  have hsecond :
      ‖J t (gainRate t (J t (paperDemandPsi psi B FD D t)))‖ ≤
        (1 / (1 - δ)) *
          (LGR * ((1 / (1 - δ)) * LW)) := by
    calc
      _ ≤ (1 / (1 - δ)) *
        ‖gainRate t (J t (paperDemandPsi psi B FD D t))‖ := hJ _
      _ ≤ (1 / (1 - δ)) *
        (LGR * ‖J t (paperDemandPsi psi B FD D t)‖) :=
          mul_le_mul_of_nonneg_left (hGaction _) hq
      _ ≤ (1 / (1 - δ)) *
        (LGR * ((1 / (1 - δ)) * ‖paperDemandPsi psi B FD D t‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hJ _) hLGR) hq
      _ ≤ (1 / (1 - δ)) *
        (LGR * ((1 / (1 - δ)) * LW)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hW hq) hLGR) hq
  change ‖deriv (fun s : ℝ => J s (paperDemandPsi psi B FD D s)) t‖ ≤ _
  rw [htr]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

end ReservoirSeismicityControl
