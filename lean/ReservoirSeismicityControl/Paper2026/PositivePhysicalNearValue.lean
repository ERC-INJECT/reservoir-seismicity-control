import ReservoirSeismicityControl.Paper2026.PositiveSRNearWeakIncrement
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionCoordinates
import ReservoirSeismicityControl.WellIntegralL2
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: VALUE of the actual finite-output near observation

The paper uses the static pressure observation weight chi_(V_u)/|V_u|
and the time-varying SR observation weight chi_(V_R)*gamma1*R /
(gamma10*R0star*|V_R|).  We apply the SAME fixed smooth cutoff
operator to both weights, and collect their negative diffusion pairings
in the pressure and SR output coordinates of equation (14).

This closes the independent near-observation VALUE bound at the level of
actual physical output weights.  It does not claim a weak derivative or
prove the external local H2 -> D(A) regularity statement.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The fixed pressure near weight used in Appendix A.3: zeta chi_V / |V|.
The cutoff operator is the L2 multiplier by the paper's smooth zeta;
identification with a particular geometric zeta remains an applicability check. -/
noncomputable def paperPressureNearWeight
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (region : Set X) (hs : MeasurableSet region) (hf : mu region ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) : Lp ℝ 2 mu :=
  (1 / mu.real region : ℝ) •
    cutoff (indicatorConstLp 2 hs hf (1 : ℝ))

/-- The pressure part of the smooth near weight has the exact L2 bound
following from the norm of a finite-volume indicator. -/
theorem paper_pressure_near_weight_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (region : Set X) (hs : MeasurableSet region) (hf : mu region ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) :
    ‖paperPressureNearWeight mu region hs hf cutoff‖ ≤
      |1 / mu.real region| *
        (‖cutoff‖ * (mu.real region) ^ (1 / (2 : ℝ))) := by
  have hind :
      ‖indicatorConstLp (2 : ENNReal) hs hf (1 : ℝ)‖ =
        (mu.real region) ^ (1 / (2 : ℝ)) := by
    simpa using (MeasureTheory.norm_indicatorConstLp
      (μ := mu) (p := (2 : ENNReal)) (hs := hs) (hμs := hf)
      (c := (1 : ℝ)) (by norm_num) (by norm_num))
  change ‖(1 / mu.real region : ℝ) •
      cutoff (indicatorConstLp 2 hs hf (1 : ℝ))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |1 / mu.real region| * ‖cutoff (indicatorConstLp 2 hs hf (1 : ℝ))‖ ≤
        |1 / mu.real region| *
          (‖cutoff‖ * ‖indicatorConstLp 2 hs hf (1 : ℝ)‖) :=
      mul_le_mul_of_nonneg_left
        (cutoff.le_opNorm (indicatorConstLp 2 hs hf (1 : ℝ))) (abs_nonneg _)
    _ = _ := by rw [hind]

/-- Pressure output near diffusion VALUE, with no derivative of the input. -/
theorem paper_pressure_near_observation_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (region : Set X) (hs : MeasurableSet region) (hf : mu region ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Ap : Lp ℝ 2 mu) (CAp : ℝ) (hAp : ‖Ap‖ ≤ CAp) :
    |-⟪paperPressureNearWeight mu region hs hf cutoff, Ap⟫_ℝ| ≤
      (|1 / mu.real region| *
        (‖cutoff‖ * (mu.real region) ^ (1 / (2 : ℝ)))) * CAp := by
  have hcs :
      |⟪paperPressureNearWeight mu region hs hf cutoff, Ap⟫_ℝ| ≤
        ‖paperPressureNearWeight mu region hs hf cutoff‖ * ‖Ap‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ)
        (paperPressureNearWeight mu region hs hf cutoff) Ap)
  rw [abs_neg]
  calc
    _ ≤ ‖paperPressureNearWeight mu region hs hf cutoff‖ * ‖Ap‖ := hcs
    _ ≤ (|1 / mu.real region| *
        (‖cutoff‖ * (mu.real region) ^ (1 / (2 : ℝ)))) * ‖Ap‖ :=
      mul_le_mul_of_nonneg_right
        (paper_pressure_near_weight_bound mu region hs hf cutoff) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hAp
      ((norm_nonneg _).trans (paper_pressure_near_weight_bound mu region hs hf cutoff))

/-- Canonical pressure injection in the full pressure+SR output space. -/
noncomputable def paperPressureCoordinateEmbed {u r : ℕ} (i : Fin u) :
    ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (EuclideanSpace.single (Sum.inl i) (1 : ℝ))

/-- The actual full near-diffusion component of (14), INCLUDING both
pressure and signed-model SR observations; the minus sign comes from -Ap.
The near weight has no additional SR sign factor. -/
noncomputable def paperPhysicalFiniteNearPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X)
    (pressureRegions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pressureRegions i))
    (hpFin : ∀ i, mu (pressureRegions i) ≠ ⊤)
    (srRegions : Fin r → Set X)
    (hsMeas : ∀ i, MeasurableSet (srRegions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R : ℝ → Lp ℝ 2 mu) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Ap : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  (∑ i : Fin u,
    paperPressureCoordinateEmbed (u := u) (r := r) i
      (-⟪paperPressureNearWeight mu (pressureRegions i)
            (hpMeas i) (hpFin i) cutoff, Ap t⟫_ℝ)) +
  (∑ i : Fin r,
    paperSRCoordinateEmbed (u := u) (r := r) i
      (-⟪paperSRNearDiffusionWeight mu (srRegions i) (hsMeas i)
            Kgamma R gamma10 R0star cutoff t, Ap t⟫_ℝ))

/-- All finite-output near-observation VALUE bounds follow from the actual
indicator and gamma1*R weights, A.3's uniform Ap estimate, and A.7's SR
L2 bounds. No standalone assumption on the near Psi vector is used. -/
theorem paper_physical_finite_near_value_bound
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X)
    (pressureRegions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pressureRegions i))
    (hpFin : ∀ i, mu (pressureRegions i) ≠ ⊤)
    (srRegions : Fin r → Set X)
    (hsMeas : ∀ i, MeasurableSet (srRegions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R Rdot : ℝ → Lp ℝ 2 mu) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Cgamma CR MR : ℝ)
    (hCgamma : 0 ≤ Cgamma) (hK : ‖Kgamma‖ ≤ Cgamma)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (Ap : ℝ → Lp ℝ 2 mu) (CAp : ℝ)
    (hAp : ∀ t, ‖Ap t‖ ≤ CAp) :
    ∀ t,
    ‖paperPhysicalFiniteNearPsi mu pressureRegions hpMeas hpFin
        srRegions hsMeas Kgamma R gamma10 R0star cutoff Ap t‖ ≤
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / mu.real (pressureRegions i)| *
          (‖cutoff‖ * (mu.real (pressureRegions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((‖cutoff‖ *
          (|1 / (gamma10 * R0star * mu.real (srRegions i))| *
            (Cgamma * MR))) * CAp)) := by
  classical
  intro t
  let p : Fin u → ℝ := fun i =>
    -⟪paperPressureNearWeight mu (pressureRegions i)
      (hpMeas i) (hpFin i) cutoff, Ap t⟫_ℝ
  let q : Fin r → ℝ := fun i =>
    -⟪paperSRNearDiffusionWeight mu (srRegions i) (hsMeas i)
      Kgamma R gamma10 R0star cutoff t, Ap t⟫_ℝ
  have hp (i : Fin u) : |p i| ≤
      (|1 / mu.real (pressureRegions i)| *
        (‖cutoff‖ * (mu.real (pressureRegions i)) ^ (1 / (2 : ℝ)))) * CAp :=
    paper_pressure_near_observation_bound mu (pressureRegions i)
      (hpMeas i) (hpFin i) cutoff (Ap t) CAp (hAp t)
  have hq (i : Fin r) : |q i| ≤
      (‖cutoff‖ *
        (|1 / (gamma10 * R0star * mu.real (srRegions i))| *
          (Cgamma * MR))) * CAp := by
    change abs (-⟪paperSRNearDiffusionWeight mu (srRegions i) (hsMeas i)
      Kgamma R gamma10 R0star cutoff t, Ap t⟫_ℝ) ≤ _
    rw [abs_neg]
    exact paper_sr_near_observation_value_bound mu (srRegions i) (hsMeas i)
      Kgamma R Rdot gamma10 R0star Cgamma CR MR cutoff
      hCgamma hK hR hderiv hrate Ap CAp hAp t
  change ‖(∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i (p i)) +
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i (q i))‖ ≤ _
  calc
    _ ≤ ‖∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i (p i)‖ +
        ‖∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i (q i)‖ :=
      norm_add_le _ _
    _ ≤ (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i (p i)‖) +
        (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i (q i)‖) := by
      exact add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
          ((|1 / mu.real (pressureRegions i)| *
            (‖cutoff‖ * (mu.real (pressureRegions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
        (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
          ((‖cutoff‖ *
            (|1 / (gamma10 * R0star * mu.real (srRegions i))| *
              (Cgamma * MR))) * CAp)) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        calc
          ‖paperPressureCoordinateEmbed (u := u) (r := r) i (p i)‖ ≤
              ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * |p i| := by
            simpa only [Real.norm_eq_abs] using
              (paperPressureCoordinateEmbed (u := u) (r := r) i).le_opNorm (p i)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hp i) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro i _
        calc
          ‖paperSRCoordinateEmbed (u := u) (r := r) i (q i)‖ ≤
              ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * |q i| := by
            simpa only [Real.norm_eq_abs] using
              (paperSRCoordinateEmbed (u := u) (r := r) i).le_opNorm (q i)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hq i) (norm_nonneg _)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_weight_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_pressure_near_observation_bound
#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_value_bound
