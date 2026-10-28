import ReservoirSeismicityControl.Paper2026.PhysicalA14GainRate
import ReservoirSeismicityControl.PaperPhysicalEuclideanDemandBridge
import ReservoirSeismicityControl.PaperInverseGainDifferentiability
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: inverse differentiation for the actual physical gain

Use the PASSED A11/A12 full physical matrix and the PASSED A14 derivative
of its actual well integrals. The published Banach-algebra inverse rule
is reused through the project's established inverse-gain theorems.

A3's spatial value bounds are required uniformly in time, as in the
manuscript. Strong L² differentiability is required only almost everywhere.
The derivative of Psi remains an explicit P3 obligation; this module
neither assumes nor establishes Qdot.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix
open scoped Matrix.Norms.Elementwise

/-- The exact full physical gain from (A11), with the nominal Gram right
inverse constructed from Assumption 4; here `normalization` is fixed. -/
noncomputable def paperA14ActualGainCLM
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) :
    ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => ReservoirSeismicityControl.paperMatrixToEuclideanCLM
    (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
      β normalization volume t *
      paperA12FullNominalRightInverse
        (paperA12FullNominalMatrix assignment β₀ volume))

/-- The *actual* A14 rate, including the positive signed-SR well integral
rates and the constant nominal inverse. No independent Gdot premise. -/
noncomputable def paperA14ActualGainRateCLM
    {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ)
    (rate : ℝ → Fin w → ℝ) :
    ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  fun t => ReservoirSeismicityControl.paperMatrixToEuclideanCLM
    (paperA14FullPhysicalRateMatrix assignment β normalization volume
      (rate t) *
      paperA12FullNominalRightInverse
        (paperA12FullNominalMatrix assignment β₀ volume))

/-- A14's true matrix derivative, transported to the same real Euclidean
CLM algebra in which the existing inverse theorem is proved. -/
theorem paper_A14_actual_gainCLM_hasDerivAt_from_wells
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ)
    (rate : ℝ → Fin w → ℝ) (t : ℝ)
    (hwell : ∀ j : Fin w,
      HasDerivAt (fun s => paperPhysicalSRWellMean μ (well j)
        γ₁ Rphysical s) (rate t j) t) :
    HasDerivAt
      (paperA14ActualGainCLM μ well γ₁ Rphysical assignment
        β β₀ normalization volume)
      (paperA14ActualGainRateCLM assignment β β₀ normalization
        volume rate t) t := by
  let C := paperA12FullNominalRightInverse
    (paperA12FullNominalMatrix assignment β₀ volume)
  change HasDerivAt
    (fun s => ReservoirSeismicityControl.paperMatrixToEuclideanCLM
      (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
        β normalization volume s * C))
    (ReservoirSeismicityControl.paperMatrixToEuclideanCLM
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (rate t) * C)) t
  exact ReservoirSeismicityControl.paper_matrix_toEuclideanCLM_hasDerivAt
    (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
      β normalization volume s * C)
    (paperA14FullPhysicalRateMatrix assignment β normalization volume
      (rate t) * C) t
    (paper_A14_full_physical_gain_hasDerivAt μ well γ₁ Rphysical
      assignment β normalization volume C rate t hwell)

/-- Derivative of the actual full physical gain as a Euclidean operator,
obtained almost everywhere from the SR L² trajectory and the spatial
well-average representative identity. -/
theorem paper_A14_actual_gainCLM_hasDerivAt_from_SR_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) ≠ ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperA14ActualGainCLM μ well γ₁ Rphysical assignment
          β β₀ normalization volume)
        (paperA14ActualGainRateCLM assignment β β₀ normalization
          volume (fun t j => wellMeanL2 μ (well j) (hs j) (hfinite j)
            (Kγ (Rdot t))) t) t := by
  let rate : ℝ → Fin w → ℝ := fun t j =>
    wellMeanL2 μ (well j) (hs j) (hfinite j) (Kγ (Rdot t))
  have hwell : ∀ j : Fin w, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t := by
    intro j
    exact ReservoirSeismicityControl.paper_physical_well_hasDerivAt_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) γ₁ Rphysical
      R Rdot Kγ (hrep j) hSRDeriv
  have hcommon : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin w, HasDerivAt
        (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t := Filter.eventually_all.mpr hwell
  filter_upwards [hcommon] with t ht
  exact paper_A14_actual_gainCLM_hasDerivAt_from_wells
    μ well γ₁ Rphysical assignment β β₀ normalization volume
    rate t ht

/-- Full A14: the inverse derivative and the normalized perturbation
product rule for the *actual* physical matrix. All-time A3 pointwise
bounds are used to instantiate the PASSED A12 contraction theorem;
no separate contraction/inverse hypothesis is made.

The only `psi` condition is its a.e. derivative, whose physical
near/far applicability is tracked separately under P3. -/
theorem paper_A14_actual_normalized_derivative_from_A3_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) < ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (γmin γmax Rlower Rmax : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγorder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ s j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rlower ≤ Rphysical s x ∧ Rphysical s x ≤ Rmax)
    (hint : ∀ s j, IntegrableOn
      (fun x => γ₁ x * Rphysical s x) (well j) μ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (hpsiDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t) :
    let normalization := (β₀ / β) *
      ((γmin * Rlower + γmax * Rmax) / 2)
    let gain := paperA14ActualGainCLM μ well γ₁ Rphysical assignment
      β β₀ normalization volume
    let gainRate := paperA14ActualGainRateCLM assignment β β₀
      normalization volume
      (fun t j => wellMeanL2 μ (well j) (hs j) (ne_of_lt (hfinite j))
        (Kγ (Rdot t)))
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      deriv (fun s => Ring.inverse (gain s) (psi s)) t =
        Ring.inverse (gain t) (psiRate t) -
          Ring.inverse (gain t)
            (gainRate t (Ring.inverse (gain t) (psi t))) := by
  classical
  let lo := γmin * Rlower
  let hi := γmax * Rmax
  let normalization := (β₀ / β) * ((lo + hi) / 2)
  let gain := paperA14ActualGainCLM μ well γ₁ Rphysical assignment
    β β₀ normalization volume
  let gainRate := paperA14ActualGainRateCLM assignment β β₀
    normalization volume
    (fun t j => wellMeanL2 μ (well j) (hs j) (ne_of_lt (hfinite j))
      (Kγ (Rdot t)))
  let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
  change ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
    deriv (fun s => Ring.inverse (gain s) (psi s)) t =
      Ring.inverse (gain t) (psiRate t) -
        Ring.inverse (gain t)
          (gainRate t (Ring.inverse (gain t) (psi t)))
  have hA12 (s : ℝ) :
      0 ≤ δB ∧ δB < 1 ∧
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
          (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
            β normalization volume s *
            paperA12FullNominalRightInverse
              (paperA12FullNominalMatrix assignment β₀ volume))‖ ≤ δB := by
    exact paper_A12_full_physical_opNorm_from_A3
      μ well γ₁ Rphysical assignment β β₀ volume
      γmin γmax Rlower Rmax s
      hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
      hvolume hcovered hfinite
      hpositive hγ (hR s) (hint s)
  have hδ : δB < 1 := (hA12 0).2.1
  have hrepr (A : Matrix (Sum (Fin u) (Fin r))
      (Sum (Fin u) (Fin r)) ℝ) :
      ReservoirSeismicityControl.paperMatrixToEuclideanCLM A =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r)) A := by
    rfl
  have hclose : ∀ s : ℝ,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) - gain s‖ ≤ δB := by
    intro s
    rw [show gain s = Matrix.toEuclideanCLM (𝕜 := ℝ)
       (n := Sum (Fin u) (Fin r))
         (paperA12FullPhysicalMatrix μ well γ₁ Rphysical assignment
           β normalization volume s *
           paperA12FullNominalRightInverse
             (paperA12FullNominalMatrix assignment β₀ volume)) from hrepr _]
    exact (hA12 s).2.2
  have hgd : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt gain (gainRate t) t :=
    paper_A14_actual_gainCLM_hasDerivAt_from_SR_ae
      μ well hs (fun j => ne_of_lt (hfinite j)) γ₁ Rphysical R Rdot Kγ
      hrep hSRDeriv assignment β β₀ normalization volume
  let inverseGain : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun s => Ring.inverse (gain s)
  have hright : ∀ s x, gain s (inverseGain s x) = x := by
    intro s x
    exact ReservoirSeismicityControl.paper_gain_ringInverse_right_of_contraction
      gain δB hδ hclose s x
  have hleft : ∀ s x, inverseGain s (gain s x) = x := by
    intro s x
    exact ReservoirSeismicityControl.paper_gain_ringInverse_left_of_contraction
      gain δB hδ hclose s x
  have hinvd : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt inverseGain (deriv inverseGain t) t :=
    ReservoirSeismicityControl.paper_inverse_gain_hasDerivAt_from_gain_ae
      gain inverseGain gainRate hgd hright hleft
  have hinvrule : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ x : EuclideanSpace ℝ (Sum (Fin u) (Fin r)),
        deriv inverseGain t x =
          -inverseGain t (gainRate t (inverseGain t x)) :=
    ReservoirSeismicityControl.paper_inverse_gain_rule_ae
      gain inverseGain gainRate (fun t => deriv inverseGain t)
      hgd hinvd hright hleft
  exact ReservoirSeismicityControl.paper_normalized_psi_deriv_ae
    psi psiRate inverseGain (fun t => deriv inverseGain t) gainRate
    hpsiDeriv hinvd hinvrule

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_wells
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_gainCLM_hasDerivAt_from_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_actual_normalized_derivative_from_A3_ae
