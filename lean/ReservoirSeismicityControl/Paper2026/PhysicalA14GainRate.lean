import ReservoirSeismicityControl.Paper2026.PhysicalA12FullInverse
import ReservoirSeismicityControl.PaperPhysicalWellMatrixRates
import ReservoirSeismicityControl.PaperPhysicalGainOpNormRates
import Mathlib.Tactic

/-!
# P4 / Appendix A.4: the actual full physical gain rate before (A14)

The manuscript differentiates the well integrals in (A11) and then bounds
`Gdot` for `G = B(t) B₀⁺`. The pressure rows of `B` are time independent and
the SR rows depend on the actual spatial means of `gamma1 * R`.

This module uses the already verified L² spatial-mean derivative and the
finite-dimensional Euclidean matrix norm. It does not use `Qdot`, reprove
semigroup/Sobolev theory, or silently replace the signed SR model with the
legacy negative-sign coefficient.

The strong L² representative/differentiability properties are explicit
applicability inputs from Appendix A.2. Boundedness of their rate is the
existing A7 estimate. P3 and final A14 normalized-perturbation assembly
remain separate obligations.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

section MatrixDifferentiation
open scoped Matrix.Norms.Elementwise

/-- The derivative candidate for the *actual* physical full well matrix.
Pressure entries have zero rate. Every SR rate is the positive well-mean
rate divided by its time-independent physical normalization and volume. -/
noncomputable def paperA14FullPhysicalRateMatrix {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (rate : Fin w → ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  fun i j => match i with
    | Sum.inl _ => 0
    | Sum.inr _ =>
      if assignment j = some i then
        rate j / (normalization * β * volume i)
      else 0

/-- Differentiability of every physical well average implies the exact
matrix derivative. In particular, the pressure block has zero derivative. -/
theorem paper_A14_full_physical_matrix_hasDerivAt
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (rate : ℝ → Fin w → ℝ) (t : ℝ)
    (hd : ∀ j : Fin w,
      HasDerivAt (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t) :
    HasDerivAt
      (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
        assignment β normalization volume s)
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (rate t)) t := by
  apply (hasDerivAt_pi).2
  intro i
  apply (hasDerivAt_pi).2
  intro j
  cases i with
  | inl i =>
      change HasDerivAt
        (fun _ : ℝ => if assignment j = some (Sum.inl i) then
          (1 : ℝ) / (β * volume (Sum.inl i)) else 0) 0 t
      exact hasDerivAt_const t _
  | inr i =>
      by_cases hj : assignment j = some (Sum.inr i)
      · simpa [paperA12FullPhysicalMatrix, paperA14FullPhysicalRateMatrix, hj]
          using (hd j).div_const (normalization * β * volume (Sum.inr i))
      · simpa [paperA12FullPhysicalMatrix, paperA14FullPhysicalRateMatrix, hj]
          using (hasDerivAt_const t (0 : ℝ))

/-- Exact derivative of the *full physical gain* for any fixed allocator.
In A.4 the allocator is the already verified nominal right inverse. -/
theorem paper_A14_full_physical_gain_hasDerivAt
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (rate : ℝ → Fin w → ℝ) (t : ℝ)
    (hd : ∀ j : Fin w,
      HasDerivAt (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t) :
    HasDerivAt
      (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
        assignment β normalization volume s * C)
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (rate t) * C) t := by
  let B : ℝ → Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
      assignment β normalization volume s
  let Bdot : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    paperA14FullPhysicalRateMatrix assignment β normalization volume (rate t)
  have hB : HasDerivAt B Bdot t :=
    paper_A14_full_physical_matrix_hasDerivAt μ well γ₁ Rphysical
      assignment β normalization volume rate t hd
  have hentry (i : Sum (Fin u) (Fin r)) (k : Fin w) :
      HasDerivAt (fun s => B s i k) (Bdot i k) t :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i)) k
  apply (hasDerivAt_pi).2
  intro i
  apply (hasDerivAt_pi).2
  intro j
  change HasDerivAt
    (fun s : ℝ => ∑ k : Fin w, B s i k * C k j)
    (∑ k : Fin w, Bdot i k * C k j) t
  apply HasDerivAt.fun_sum
  intro k _
  exact (hentry i k).mul_const (C k j)

/-- A common set of regular times for the finitely many *actual* spatial
well integrals. This is the exact matrix gain derivative used before (A14). -/
theorem paper_A14_full_physical_gain_deriv_from_SR_ae
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
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      deriv (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
        assignment β normalization volume s * C) t =
        paperA14FullPhysicalRateMatrix assignment β normalization volume
          (fun j => wellMeanL2 μ (well j) (hs j) (hfinite j)
            (Kγ (Rdot t))) * C := by
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
  have hactual : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin w,
      HasDerivAt
        (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t := by
    exact Filter.eventually_all.mpr hwell
  filter_upwards [hactual] with t ht
  exact (paper_A14_full_physical_gain_hasDerivAt
    μ well γ₁ Rphysical assignment β normalization volume C rate t ht).deriv

/-- A14 with exactly the nominal Gram right inverse from (17), not a free
allocator. The pressure/SR derivative matrix has the correct positive sign. -/
theorem paper_A14_full_nominal_gain_deriv_from_SR_ae
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
      deriv (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
        assignment β normalization volume s *
          paperA12FullNominalRightInverse
            (paperA12FullNominalMatrix assignment β₀ volume)) t =
        paperA14FullPhysicalRateMatrix assignment β normalization volume
          (fun j => wellMeanL2 μ (well j) (hs j) (hfinite j)
            (Kγ (Rdot t))) *
          paperA12FullNominalRightInverse
            (paperA12FullNominalMatrix assignment β₀ volume) := by
  exact paper_A14_full_physical_gain_deriv_from_SR_ae
    μ well hs hfinite γ₁ Rphysical R Rdot Kγ hrep hSRDeriv
    assignment β normalization volume
    (paperA12FullNominalRightInverse
      (paperA12FullNominalMatrix assignment β₀ volume))

end MatrixDifferentiation

/-- The physical SR rate matrix factors columnwise through its fixed
well geometry; the pressure rate remains identically zero. -/
theorem paper_A14_full_rate_geometry_factor {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (v : Fin w → ℝ) :
    paperA14FullPhysicalRateMatrix assignment β normalization volume v =
      paperA14FullPhysicalRateMatrix assignment β normalization volume
        (fun _ => 1) * Matrix.diagonal v := by
  classical
  ext i j
  cases i with
  | inl i =>
      simp [paperA14FullPhysicalRateMatrix, Matrix.mul_diagonal]
  | inr i =>
      by_cases hj : assignment j = some (Sum.inr i)
      · simp [paperA14FullPhysicalRateMatrix, Matrix.mul_diagonal,
          hj, div_eq_mul_inv]
        ring
      · simp [paperA14FullPhysicalRateMatrix, Matrix.mul_diagonal, hj]

section OperatorNorm
open scoped Matrix.Norms.L2Operator

/-- The **induced Euclidean** gain-rate bound from the finite-column
factorization, with no new matrix norm or analytic theorem. -/
theorem paper_A14_full_physical_rate_opNorm_bound {u r w : ℕ}
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β normalization : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (v : Fin w → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ j : Fin w, |v j| ≤ M) :
    ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (paperA14FullPhysicalRateMatrix assignment β normalization volume v * C) ≤
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (paperA14FullPhysicalRateMatrix assignment β normalization volume
          (fun _ => 1)) * M *
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C := by
  classical
  let A := paperA14FullPhysicalRateMatrix assignment β normalization volume
    (fun _ => 1)
  have hvnorm : ‖v‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).2
    intro j
    simpa [Real.norm_eq_abs] using hv j
  have hgeom : ‖A * Matrix.diagonal v‖ ≤ ‖A‖ * M := by
    calc
      ‖A * Matrix.diagonal v‖ ≤ ‖A‖ * ‖Matrix.diagonal v‖ :=
        Matrix.l2_opNorm_mul _ _
      _ = ‖A‖ * ‖v‖ := by rw [Matrix.l2_opNorm_diagonal]
      _ ≤ ‖A‖ * M :=
        mul_le_mul_of_nonneg_left hvnorm (norm_nonneg _)
  have hbound :
      ‖paperA14FullPhysicalRateMatrix assignment β normalization volume v * C‖ ≤
        ‖A‖ * M * ‖C‖ := by
    rw [paper_A14_full_rate_geometry_factor]
    calc
      ‖(A * Matrix.diagonal v) * C‖ ≤
          ‖A * Matrix.diagonal v‖ * ‖C‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖A‖ * M) * ‖C‖ :=
        mul_le_mul_of_nonneg_right hgeom (norm_nonneg _)
  simpa only [ReservoirSeismicityControl.paperMatrixEuclideanOpNorm,
    ← Matrix.l2_opNorm_def] using hbound

end OperatorNorm

section MatrixRate
open scoped Matrix.Norms.Elementwise

/-- The **actual** full gain derivative has a uniform induced Euclidean
bound at almost every positive time. The finite-volume factor `M` is a
numerical bound on the manuscript's explicit Hölder estimates for the
finitely many well supports; it is not a premise on `Gdot` itself.
The only differentiation input is the already verified strong L²
representative/derivative bridge for the SR state. -/
theorem paper_A14_full_nominal_gain_rate_from_SR_ae
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) ≠ ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Cγ CR M : ℝ) (hCγ : 0 ≤ Cγ) (hM : 0 ≤ M)
    (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (hgeometry : ∀ j : Fin w,
      ((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        μ.real (well j) ≤ M)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ normalization : ℝ)
    (volume : Sum (Fin u) (Fin r) → ℝ) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (deriv (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
          assignment β normalization volume s *
          paperA12FullNominalRightInverse
            (paperA12FullNominalMatrix assignment β₀ volume)) t) ≤
        ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
          (paperA14FullPhysicalRateMatrix assignment β normalization volume
            (fun _ => 1)) * M *
        ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
          (paperA12FullNominalRightInverse
            (paperA12FullNominalMatrix assignment β₀ volume)) := by
  let rate : ℝ → Fin w → ℝ := fun t j =>
    wellMeanL2 μ (well j) (hs j) (hfinite j) (Kγ (Rdot t))
  let C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ :=
    paperA12FullNominalRightInverse
      (paperA12FullNominalMatrix assignment β₀ volume)
  have hwell : ∀ j : Fin w, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
        (rate t j) t := by
    intro j
    exact ReservoirSeismicityControl.paper_physical_well_hasDerivAt_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) γ₁ Rphysical
      R Rdot Kγ (hrep j) hSRDeriv
  have hrate : ∀ j : Fin w, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |rate t j| ≤ M := by
    intro j
    have hb := ReservoirSeismicityControl.paper_physical_well_mean_rate_from_sr_L2_ae
      μ (well j) (hs j) (hfinite j) (hpositive j)
      γ₁ Rphysical R Rdot Kγ Cγ CR hCγ hK
      (hrep j) hSRDeriv hSRRate
    filter_upwards [hwell j, hb] with t hd ht
    rw [hd.deriv] at ht
    exact ht.trans (hgeometry j)
  have hcommon : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      (∀ j : Fin w,
        HasDerivAt
          (fun s => paperPhysicalSRWellMean μ (well j) γ₁ Rphysical s)
          (rate t j) t) ∧
      (∀ j : Fin w, |rate t j| ≤ M) := by
    filter_upwards [Filter.eventually_all.mpr hwell,
      Filter.eventually_all.mpr hrate] with t hdt hrt
    exact ⟨hdt, hrt⟩
  filter_upwards [hcommon] with t ht
  -- Use an equality between the *explicit* physical gain derivatives.
  -- Rewriting failed previously because `C` is a local abbreviation for
  -- the nominal right inverse appearing in the theorem's conclusion.
  have hgainDeriv :
      deriv (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
        assignment β normalization volume s * C) t =
        paperA14FullPhysicalRateMatrix assignment β normalization volume
          (rate t) * C :=
    (paper_A14_full_physical_gain_hasDerivAt μ well γ₁ Rphysical
      assignment β normalization volume C rate t ht.1).deriv
  have hnormEq :
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (deriv (fun s => paperA12FullPhysicalMatrix μ well γ₁ Rphysical
          assignment β normalization volume s * C) t) =
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (paperA14FullPhysicalRateMatrix assignment β normalization volume
          (rate t) * C) :=
    congrArg ReservoirSeismicityControl.paperMatrixEuclideanOpNorm hgainDeriv
  calc
    _ = ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
          (paperA14FullPhysicalRateMatrix assignment β normalization volume
            (rate t) * C) := hnormEq
    _ ≤ _ := paper_A14_full_physical_rate_opNorm_bound
      assignment β normalization volume C (rate t) M hM ht.2

end MatrixRate
end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_physical_matrix_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_physical_gain_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_deriv_from_SR_ae
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_rate_geometry_factor
#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_physical_rate_opNorm_bound

#print axioms ReservoirSeismicityControl.Paper2026.paper_A14_full_nominal_gain_rate_from_SR_ae
