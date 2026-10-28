import ReservoirSeismicityControl.PaperConstructiveNominalGain
import ReservoirSeismicityControl.PaperMatrixGainBridge
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl — physical multiwell SR gain from actual well averages

This module closes the disjoint-support, unconstrained SR *matrix* gap:
the actual normalized sensitivity in each output row is a nonnegative
Gram-weighted average of the individual well sensitivities.  Therefore
bounds on the **physical integrals** gamma1*R give uniform Euclidean
operator contraction and the Neumann inverse-action bound, WITHOUT a
separately assumed interval for any assembled matrix row gain.

The nominal SR row B0 includes the physical sign/volume factors; hence
B(t) i j = (h_j(t)/h_nom) * B0 i j. We assume the nominal Gram row is
nonzero and different output rows have disjoint well support, exactly as
in the pre-existing `MatrixRightInverse` construction.

This is the SR block of the unconstrained allocation, not Appendix B's
weighted-demand controller.  The pressure scalar is proved separately in
`PaperConstructiveNominalGain`. Physical local positivity and integrability
of R remain stated hypotheses (as in Appendix A.2). Nothing here invokes
an external MIMO super-twisting theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The actual unweighted SR well row, normalized against the common
constructive nominal sensitivity; B0 may contain negative entries. -/
noncomputable def paperNormalizedSRMultiwellMatrix {m w : ℕ}
    (B₀ : Matrix (Fin m) (Fin w) ℝ) (h : Fin w → ℝ)
    (nominal : ℝ) : Matrix (Fin m) (Fin w) ℝ :=
  fun i j => (h j / nominal) * B₀ i j

/-- Algebraic core: the row gain is a convex Gram-weighted average of
physical well sensitivities. No assumption on the *assembled* row gain. -/
theorem paper_normalized_sr_multiwell_row_interval
    {m w : ℕ}
    (B₀ : Matrix (Fin m) (Fin w) ℝ)
    (h : Fin w → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hbox : ∀ j, lo ≤ h j ∧ h j ≤ hi)
    (hgram : ∀ i, nominalGramDiag B₀ i ≠ 0)
    (i : Fin m) :
    let nominal : ℝ := (lo + hi) / 2
    lo / nominal ≤
        ∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i ∧
    (∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i) ≤ hi / nominal := by
  classical
  dsimp only
  let nominal : ℝ := (lo + hi) / 2
  let d : ℝ := nominalGramDiag B₀ i
  let weighted : ℝ := ∑ j : Fin w, h j * (B₀ i j * B₀ i j)
  have hnom : 0 < nominal := by
    dsimp [nominal]
    linarith
  have hd0 : 0 ≤ d := by
    dsimp [d, nominalGramDiag]
    apply Finset.sum_nonneg
    intro j _
    exact mul_self_nonneg _
  have hd : 0 < d := lt_of_le_of_ne hd0 (Ne.symm (hgram i))
  have hden : 0 < nominal * d := mul_pos hnom hd
  have hlow : lo * d ≤ weighted := by
    calc
      lo * d = ∑ j : Fin w, lo * (B₀ i j * B₀ i j) := by
        simp only [d, nominalGramDiag, Finset.mul_sum]
      _ ≤ ∑ j : Fin w, h j * (B₀ i j * B₀ i j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hbox j).1 (mul_self_nonneg _)
      _ = weighted := rfl
  have hupp : weighted ≤ hi * d := by
    calc
      weighted = ∑ j : Fin w, h j * (B₀ i j * B₀ i j) := rfl
      _ ≤ ∑ j : Fin w, hi * (B₀ i j * B₀ i j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hbox j).2 (mul_self_nonneg _)
      _ = hi * d := by
        simp only [d, nominalGramDiag, Finset.mul_sum]
  have hfactor :
      (∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i) = weighted / (nominal * d) := by
    dsimp only [weighted]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [paperNormalizedSRMultiwellMatrix, nominalRightInverse, d]
    ring_nf
  have hlo_ratio : lo / nominal ≤ weighted / (nominal * d) := by
    apply (div_le_div_iff₀ hnom hden).2
    calc
      lo * (nominal * d) = (lo * d) * nominal := by ring
      _ ≤ weighted * nominal :=
        mul_le_mul_of_nonneg_right hlow (le_of_lt hnom)
  have hhi_ratio : weighted / (nominal * d) ≤ hi / nominal := by
    apply (div_le_div_iff₀ hden hnom).2
    calc
      weighted * nominal ≤ (hi * d) * nominal :=
        mul_le_mul_of_nonneg_right hupp (le_of_lt hnom)
      _ = hi * (nominal * d) := by ring
  constructor
  · change lo / nominal ≤
        ∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i
    calc
      lo / nominal ≤ weighted / (nominal * d) := hlo_ratio
      _ = ∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i := hfactor.symm
  · change
        (∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i) ≤ hi / nominal
    calc
      (∑ j : Fin w, paperNormalizedSRMultiwellMatrix B₀ h nominal i j *
          nominalRightInverse B₀ j i) = weighted / (nominal * d) := hfactor
      _ ≤ hi / nominal := hhi_ratio

/-- A full Euclidean inverse certificate for the ACTUAL disjoint-support
multiwell SR matrix; no row-gain or operator-contraction hypothesis is given.
The output-space dimension can be arbitrary and every row may contain
several wells with different sensitivities. -/
theorem paper_normalized_sr_multiwell_inverse_certificate
    {m w : ℕ}
    (B₀ : Matrix (Fin m) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (hgram : ∀ i, nominalGramDiag B₀ i ≠ 0)
    (h : ℝ → Fin w → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hbox : ∀ t j, lo ≤ h t j ∧ h t j ≤ hi) :
    let nominal : ℝ := (lo + hi) / 2
    let loN : ℝ := lo / nominal
    let hiN : ℝ := hi / nominal
    let δ : ℝ := max |loN - 1| |hiN - 1|
    let B : ℝ → Matrix (Fin m) (Fin w) ℝ :=
      fun t => paperNormalizedSRMultiwellMatrix B₀ (h t) nominal
    let G : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) :=
      fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
        (paperWellGainMatrix (B t) B₀)
    δ < 1 ∧ ∀ t (x : EuclideanSpace ℝ (Fin m)),
      IsUnit (G t) ∧
        ‖Ring.inverse (G t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ := by
  classical
  dsimp only
  let nominal : ℝ := (lo + hi) / 2
  let loN : ℝ := lo / nominal
  let hiN : ℝ := hi / nominal
  let δ : ℝ := max |loN - 1| |hiN - 1|
  let B : ℝ → Matrix (Fin m) (Fin w) ℝ :=
    fun t => paperNormalizedSRMultiwellMatrix B₀ (h t) nominal
  let G : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) :=
    fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
      (paperWellGainMatrix (B t) B₀)
  have hnom : 0 < nominal := by
    dsimp [nominal]
    linarith
  have hloN : 0 < loN := div_pos hlo hnom
  have hlohiN : loN ≤ hiN := by
    dsimp [loN, hiN]
    exact (div_le_div_iff₀ hnom hnom).2
      (mul_le_mul_of_nonneg_right hlohi (le_of_lt hnom))
  have hhiN : hiN < 2 := by
    dsimp [hiN, nominal]
    have hs : 0 < lo + hi := by linarith
    have hnomPos : 0 < (lo + hi) / 2 := by linarith
    apply (div_lt_iff₀ hnomPos).2
    linarith
  have hB : ∀ t i j, wellRegion j ≠ some i → B t i j = 0 := by
    intro t i j hj
    simp [B, paperNormalizedSRMultiwellMatrix, hB₀ i j hj]
  have hgain : ∀ t i,
      loN ≤ (∑ j : Fin w, B t i j * nominalRightInverse B₀ j i) ∧
      (∑ j : Fin w, B t i j * nominalRightInverse B₀ j i) ≤ hiN := by
    intro t i
    have hrow := paper_normalized_sr_multiwell_row_interval B₀
      (h t) lo hi hlo hlohi (hbox t) hgram i
    simpa only [B, nominal, loN, hiN] using hrow
  have hmargin := interval_gain_margin_lt_one loN hiN hloN hlohiN hhiN
  refine ⟨hmargin.2, ?_⟩
  intro t x
  have hcert := paper_actual_well_gain_inverse_certificate
    B B₀ wellRegion hB hB₀ loN hiN hloN hlohiN hhiN
    hgain t x
  change IsUnit (G t) ∧
    ‖Ring.inverse (G t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ at hcert
  exact hcert

/-- Specialize the full actual multiwell-matrix inverse to physical
spatial integrals gamma1*R on well supports, with no independent interval
hypothesis on assembled gains. The logistic SR field's a.e. bounds are
exactly the Appendix A.2 inputs, not an assumption of matrix contraction. -/
theorem paper_physical_sr_multiwell_integral_inverse_certificate
    {X : Type*} [MeasurableSpace X] {m w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmax Rlower : ℝ) (Rmin : Fin w → ℝ)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγOrder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hRmin : ∀ j, Rlower ≤ Rmin j)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(μ.restrict (well j)),
        Rmin j ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * R t x) (well j) μ)
    (B₀ : Matrix (Fin m) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin m))
    (hB₀ : ∀ i j, wellRegion j ≠ some i → B₀ i j = 0)
    (hgram : ∀ i, nominalGramDiag B₀ i ≠ 0) :
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let nominal : ℝ := (lo + hi) / 2
    let loN : ℝ := lo / nominal
    let hiN : ℝ := hi / nominal
    let δ : ℝ := max |loN - 1| |hiN - 1|
    let h := paperNonnegativeTimeWellSensitivities μ well γ₁ R
    let B : ℝ → Matrix (Fin m) (Fin w) ℝ :=
      fun t => paperNormalizedSRMultiwellMatrix B₀ (h t) nominal
    let G : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) :=
      fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
        (paperWellGainMatrix (B t) B₀)
    δ < 1 ∧ ∀ t (x : EuclideanSpace ℝ (Fin m)),
      IsUnit (G t) ∧
        ‖Ring.inverse (G t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ := by
  classical
  have hRminpos (j : Fin w) : 0 < Rmin j :=
    lt_of_lt_of_le hRlower (hRmin j)
  have hphysical := paper_physical_well_sensitivity_box
    μ well γ₁ R γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRminpos hγ hR hint
  have hloPos : 0 < γmin * Rlower := mul_pos hγmin hRlower
  have hlohi : γmin * Rlower ≤ γmax * Rmax := by
    have hRmaxNonneg : 0 ≤ Rmax :=
      (le_of_lt hRlower).trans hRorder
    calc
      γmin * Rlower ≤ γmin * Rmax :=
        mul_le_mul_of_nonneg_left hRorder (le_of_lt hγmin)
      _ ≤ γmax * Rmax :=
        mul_le_mul_of_nonneg_right hγOrder hRmaxNonneg
  have hbox : ∀ t j,
      γmin * Rlower ≤ paperNonnegativeTimeWellSensitivities μ well γ₁ R t j ∧
      paperNonnegativeTimeWellSensitivities μ well γ₁ R t j ≤ γmax * Rmax := by
    intro t j
    constructor
    · exact (mul_le_mul_of_nonneg_left (hRmin j) (le_of_lt hγmin)).trans
        (hphysical.1 t j)
    · exact hphysical.2 t j
  exact paper_normalized_sr_multiwell_inverse_certificate B₀ wellRegion
    hB₀ hgram (paperNonnegativeTimeWellSensitivities μ well γ₁ R)
    (γmin * Rlower) (γmax * Rmax) hloPos hlohi hbox

#print axioms ReservoirSeismicityControl.paper_normalized_sr_multiwell_row_interval
#print axioms ReservoirSeismicityControl.paper_normalized_sr_multiwell_inverse_certificate
#print axioms ReservoirSeismicityControl.paper_physical_sr_multiwell_integral_inverse_certificate

end ReservoirSeismicityControl
