import ReservoirSeismicityControl.PaperPhysicalWellRates
import ReservoirSeismicityControl.PaperPhysicalDemandSensitivity

/-!
# Stage 51: actual time derivatives of the physical SR control matrix

The well coefficient used in Appendix A.4 and Appendix B is
  Bhat_R(h(t))_ij = -(beta * regionVolume_i)^(-1) * h_j(t)
when well j is in region i, and zero otherwise. In Stage 50, h_j(t) is
an actual normalized Lebesgue integral, and its a.e. derivative was bounded
using the SR dynamics in L².

We now differentiate the *actual physical coefficient* and transfer the
scalar well-rate estimate to the corresponding matrix entry. In particular,
no derivative of Q is required. This module is an entrywise result; it does
not yet claim an induced operator-norm estimate for the full matrix B'(t).
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- At a regular time, the derivative of each regional SR sensitivity
coefficient is the same fixed coefficient times the actual well mean rate.
The off-region coefficient stays zero, including its derivative. -/
theorem paper_physical_sr_entry_hasDerivAt
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ)
    (t : ℝ) (i : Fin r) (j : Fin w)
    (hd : HasDerivAt (fun s => h s j) (hRate t j) t) :
    HasDerivAt
      (fun s => paperPhysicalSRWellMatrix wellRegion β volume (h s) i j)
      (paperPhysicalSRWellMatrix wellRegion β volume (hRate t) i j) t := by
  by_cases hj : wellRegion j = some i
  · simp only [paperPhysicalSRWellMatrix, if_pos hj]
    exact hd.const_mul (-1 / (β * volume i))
  · simp only [paperPhysicalSRWellMatrix, if_neg hj]
    exact hasDerivAt_const t (0 : ℝ)

/-- The a.e. derivative is the actual derivative, not an independently
postulated matrix rate. This is valid at every regular time of h_j. -/
theorem paper_physical_sr_entry_deriv_ae
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (i : Fin r) (j : Fin w)
    (hd : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (fun s => paperPhysicalSRWellMatrix
        wellRegion β volume (h s) i j) t =
        paperPhysicalSRWellMatrix wellRegion β volume (hRate t) i j := by
  filter_upwards [hd] with t ht
  exact (paper_physical_sr_entry_hasDerivAt
    wellRegion β volume h hRate t i j ht).deriv

/-- An a.e. scalar well-rate bound implies the corresponding a.e.
coefficient-rate bound, with the *physical regional volume* retained. -/
theorem paper_physical_sr_entry_rate_bound_ae
    {r w : ℕ} (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (C : Fin w → ℝ)
    (i : Fin r) (j : Fin w)
    (hd : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t)
    (hb : ∀ᵐ t ∂paperPositiveTime, |hRate t j| ≤ C j) :
    ∀ᵐ t ∂paperPositiveTime,
      |deriv (fun s => paperPhysicalSRWellMatrix
        wellRegion β volume (h s) i j) t| ≤
        |(-1 / (β * volume i))| * C j := by
  filter_upwards [hd, hb] with t ht hbound
  rw [(paper_physical_sr_entry_hasDerivAt
    wellRegion β volume h hRate t i j ht).deriv]
  have hnonneg : 0 ≤ C j := (abs_nonneg _).trans hbound
  by_cases hj : wellRegion j = some i
  · simp only [paperPhysicalSRWellMatrix, if_pos hj, abs_mul]
    exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
  · simp only [paperPhysicalSRWellMatrix, if_neg hj, abs_zero]
    exact mul_nonneg (abs_nonneg _) hnonneg

/-- The pressure block of the full physical well matrix is constant in
 h; the SR block has the actual derivative of the well mean. -/
theorem paper_physical_demand_entry_hasDerivAt
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (t : ℝ) (i : Sum (Fin u) (Fin r)) (j : Fin w)
    (hd : HasDerivAt (fun s => h s j) (hRate t j) t) :
    HasDerivAt
      (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (h s) α κ i j)
      (match i with
        | Sum.inl _ => 0
        | Sum.inr k => κ *
            paperPhysicalSRWellMatrix wellRegion β volume (hRate t) k j)
      t := by
  cases i with
  | inl k =>
      change HasDerivAt (fun _ : ℝ => α * Bᵤ₀ k j) 0 t
      exact hasDerivAt_const t (α * Bᵤ₀ k j)
  | inr k =>
      change HasDerivAt
        (fun s : ℝ => κ * paperPhysicalSRWellMatrix
          wellRegion β volume (h s) k j)
        (κ * paperPhysicalSRWellMatrix wellRegion β volume (hRate t) k j) t
      exact (paper_physical_sr_entry_hasDerivAt
        wellRegion β volume h hRate t k j hd).const_mul κ

/-- The L² seismicity-rate estimate from Stage 50 gives an a.e. *strong*
 derivative of the actual spatially integrated well mean. The multiplier
 representative equality is the same explicit obligation as in Stage 50. -/
theorem paper_physical_well_hasDerivAt_from_sr_L2_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ τ : ℝ, ∀ᵐ x ∂(μ.restrict s),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t) :
    ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt
        (fun τ => paperPhysicalSRWellMean μ s γ₁ Rphysical τ)
        (wellMeanL2 μ s hs hfinite (Kγ (Rdot t))) t := by
  have heq : (fun τ => paperPhysicalSRWellMean μ s γ₁ Rphysical τ) =
      (fun τ => wellMeanL2 μ s hs hfinite (Kγ (R τ))) := by
    funext τ
    exact paper_physical_well_mean_eq_L2 μ s hs hfinite γ₁
      Rphysical (Kγ (R τ)) τ (hrep τ)
  filter_upwards [hderiv] with t hd
  rw [heq]
  exact well_mean_L2_hasDerivAt μ s hs hfinite
    (fun τ => Kγ (R τ)) (Kγ (Rdot t)) t
    (Kγ.hasFDerivAt.comp_hasDerivAt t hd)

/-- Direct bridge from the genuine spatial SR average to the physical
well coefficient derivative. The SR field supplies the a.e. derivative;
there is no hypothesis about Qdot. -/
theorem paper_physical_sr_entry_deriv_from_sr_L2_ae
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) ≠ ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (i : Fin r) (j : Fin w) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (fun τ => paperPhysicalSRWellMatrix wellRegion β volume
        (fun k => paperPhysicalSRWellMean μ (well k) γ₁ Rphysical τ) i j) t =
      paperPhysicalSRWellMatrix wellRegion β volume
        (fun k => wellMeanL2 μ (well k) (hs k) (hfinite k)
          (Kγ (Rdot t))) i j := by
  exact paper_physical_sr_entry_deriv_ae wellRegion β volume
    (fun τ k => paperPhysicalSRWellMean μ (well k) γ₁ Rphysical τ)
    (fun τ k => wellMeanL2 μ (well k) (hs k) (hfinite k) (Kγ (Rdot τ)))
    i j (paper_physical_well_hasDerivAt_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) γ₁ Rphysical
      R Rdot Kγ (hrep j) hderiv)


/-- Appendix A.4: an explicit coefficient derivative bound obtained directly
from the actual SR L² rate. The bound depends only on the fixed physical
well volume, region volume, beta, coefficient multiplier bound and SR rate.
It is not a hypothesis on the derivative of the controlled well fluxes. -/
theorem paper_physical_sr_entry_rate_from_sr_L2_ae
    {X : Type*} [MeasurableSpace X] {r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) ≠ ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Cγ CR : ℝ) (hCγ : 0 ≤ Cγ)
    (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t)
    (hRdot : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (i : Fin r) (j : Fin w) :
    ∀ᵐ t ∂paperPositiveTime,
      |deriv (fun τ => paperPhysicalSRWellMatrix wellRegion β volume
        (fun k => paperPhysicalSRWellMean μ (well k) γ₁ Rphysical τ) i j) t| ≤
      |(-1 / (β * volume i))| *
        (((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
          μ.real (well j)) := by
  let h : ℝ → Fin w → ℝ :=
    fun t k => paperPhysicalSRWellMean μ (well k) γ₁ Rphysical t
  let hRate : ℝ → Fin w → ℝ :=
    fun t k => wellMeanL2 μ (well k) (hs k) (hfinite k) (Kγ (Rdot t))
  have hmeanDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t := by
    exact paper_physical_well_hasDerivAt_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) γ₁ Rphysical
      R Rdot Kγ (hrep j) hderiv
  have hmeanBound : ∀ᵐ t ∂paperPositiveTime,
      |deriv (fun s => h s j) t| ≤
        ((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
          μ.real (well j) := by
    exact paper_physical_well_mean_rate_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) (hpositive j)
      γ₁ Rphysical R Rdot Kγ Cγ CR hCγ hK
      (hrep j) hderiv hRdot
  have hbound : ∀ᵐ t ∂paperPositiveTime,
      |hRate t j| ≤
        ((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
          μ.real (well j) := by
    filter_upwards [hmeanDeriv, hmeanBound] with t hd hb
    rw [hd.deriv] at hb
    exact hb
  exact paper_physical_sr_entry_rate_bound_ae wellRegion β volume
    h hRate
    (fun k => ((μ.real (well k)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
      μ.real (well k))
    i j hmeanDeriv hbound

end ReservoirSeismicityControl
