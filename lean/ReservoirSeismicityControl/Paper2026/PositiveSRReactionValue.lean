import ReservoirSeismicityControl.Paper2026.PositiveSRReactionFiniteRegions

/-!
# P3 / Appendix A.3: value of the signed finite-region SR reaction

The preceding finite-region certificate treats the time derivative of the
actual signed reaction integral. Appendix A.3 and the B19 perturbation bound
also need the value of that reaction contribution. These lemmas reuse the
already established finite-volume L² integral estimate; they do not assume
bounds on the regional reaction contribution itself.

The physical L² representative and its uniform norm bound remain explicit
A3/A7 applicability obligations. No differentiation-under-integral result,
semigroup theorem, Qdot assumption, or extra condition on the sign is added.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped BigOperators

/-- Actual normalized reaction value in one SR output region, estimated from
its spatial L² representative. The sign `s` remains in the coefficient. -/
theorem physical_sr_reaction_regional_value_from_L2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (region : Set X)
    (hs : MeasurableSet region) (hfinite : μ region ≠ ⊤)
    (hpositive : 0 < μ.real region)
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (F : Lp ℝ 2 μ) (t : ℝ)
    (hrep : ∀ᵐ x ∂(μ.restrict region),
      (F x : ℝ) = gamma2 t x * R t x * (R t x - Rstar x)) :
    |physicalSRRegionalReaction μ region gamma2 R Rstar
        sign gamma10 R0star t| ≤
      |(-sign / (gamma10 * R0star))| *
        (((μ.real region) ^ (1 / (2 : ℝ)) * ‖F‖) / μ.real region) := by
  unfold physicalSRRegionalReaction
  rw [physical_sr_reaction_setIntegral_eq_L2 μ region hs hfinite
    (fun x => gamma2 t x * R t x * (R t x - Rstar x)) F hrep]
  change |(-sign / (gamma10 * R0star)) *
      ReservoirSeismicityControl.wellMeanL2 μ region hs hfinite F| ≤
    |(-sign / (gamma10 * R0star))| *
      (((μ.real region) ^ (1 / (2 : ℝ)) * ‖F‖) / μ.real region)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (ReservoirSeismicityControl.well_mean_L2_bound μ region hs hfinite hpositive F)
    (abs_nonneg _)

/-- Finite-dimensional P3 reaction VALUE bound from the physical regional
Lebesgue integrals. This uses the same output embedding as the verified
finite-region derivative identity; no free bound on `reactionPsi` appears. -/
theorem physical_sr_finite_reaction_value_from_L2
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hs : ∀ i, MeasurableSet (regions i))
    (hfinite : ∀ i, μ (regions i) ≠ ⊤)
    (hpositive : ∀ i, 0 < μ.real (regions i))
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (F : Fin r → Lp ℝ 2 μ) (t : ℝ)
    (hrep : ∀ i, ∀ᵐ x ∂(μ.restrict (regions i)),
      ((F i) x : ℝ) = gamma2 t x * R t x * (R t x - Rstar x)) :
    ‖physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
        sign gamma10 R0star embed t‖ ≤
      ∑ i : Fin r, ‖embed i‖ *
        (|(-sign / (gamma10 * R0star))| *
          (((μ.real (regions i)) ^ (1 / (2 : ℝ)) * ‖F i‖) /
            μ.real (regions i))) := by
  classical
  unfold physicalSRFiniteReactionPsi
  calc
    ‖∑ i : Fin r, embed i (physicalSRRegionalReaction μ (regions i)
        gamma2 R Rstar sign gamma10 R0star t)‖
      ≤ ∑ i : Fin r, ‖embed i (physicalSRRegionalReaction μ (regions i)
          gamma2 R Rstar sign gamma10 R0star t)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin r, ‖embed i‖ *
        |physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
          sign gamma10 R0star t| := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Real.norm_eq_abs] using
        (embed i).le_opNorm
          (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
            sign gamma10 R0star t)
    _ ≤ ∑ i : Fin r, ‖embed i‖ *
        (|(-sign / (gamma10 * R0star))| *
          (((μ.real (regions i)) ^ (1 / (2 : ℝ)) * ‖F i‖) /
            μ.real (regions i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (physical_sr_reaction_regional_value_from_L2
          μ (regions i) (hs i) (hfinite i) (hpositive i)
          gamma2 R Rstar sign gamma10 R0star (F i) t (hrep i))
        (norm_nonneg (embed i))

/-- A uniform VALUE bound suitable for the P3 component input to B19.
The only new uniform premise is the L² estimate of the *reaction field*
`γ₂ R(R-R*)` itself, to be checked from A3 and the SR bounds (A7).
It is not a bound assumed for the final regional perturbation. -/
theorem physical_sr_finite_reaction_value_uniform
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hs : ∀ i, MeasurableSet (regions i))
    (hfinite : ∀ i, μ (regions i) ≠ ⊤)
    (hpositive : ∀ i, 0 < μ.real (regions i))
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star : ℝ)
    (embed : Fin r → (ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r))))
    (F : Fin r → ℝ → Lp ℝ 2 μ) (C : Fin r → ℝ)
    (hrep : ∀ i t, ∀ᵐ x ∂(μ.restrict (regions i)),
      ((F i t) x : ℝ) = gamma2 t x * R t x * (R t x - Rstar x))
    (hL2 : ∀ i t, 0 ≤ t → ‖F i t‖ ≤ C i) :
    ∀ t, 0 ≤ t →
      ‖physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
          sign gamma10 R0star embed t‖ ≤
        ∑ i : Fin r, ‖embed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((μ.real (regions i)) ^ (1 / (2 : ℝ)) * C i) /
              μ.real (regions i))) := by
  intro t ht
  calc
    ‖physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
        sign gamma10 R0star embed t‖
      ≤ ∑ i : Fin r, ‖embed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((μ.real (regions i)) ^ (1 / (2 : ℝ)) * ‖F i t‖) /
              μ.real (regions i))) :=
        physical_sr_finite_reaction_value_from_L2 μ regions
          hs hfinite hpositive gamma2 R Rstar sign gamma10 R0star
          embed (fun i => F i t) t (fun i => hrep i t)
    _ ≤ ∑ i : Fin r, ‖embed i‖ *
          (|(-sign / (gamma10 * R0star))| *
            (((μ.real (regions i)) ^ (1 / (2 : ℝ)) * C i) /
              μ.real (regions i))) := by
      classical
      apply Finset.sum_le_sum
      intro i hi
      have hroot : 0 ≤ (μ.real (regions i)) ^ (1 / (2 : ℝ)) := by
        positivity
      have hmean :
          ((μ.real (regions i)) ^ (1 / (2 : ℝ)) * ‖F i t‖) /
            μ.real (regions i) ≤
          ((μ.real (regions i)) ^ (1 / (2 : ℝ)) * C i) /
            μ.real (regions i) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hL2 i t ht) hroot)
          (hpositive i).le
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmean (abs_nonneg _))
        (norm_nonneg (embed i))

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_regional_value_from_L2
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_from_L2
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_finite_reaction_value_uniform
