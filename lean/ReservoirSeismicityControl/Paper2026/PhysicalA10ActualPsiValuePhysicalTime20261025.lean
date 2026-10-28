import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualFarValue20261025
import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionValue
import ReservoirSeismicityControl.PaperRegionalPerturbationComponents
import Mathlib.Tactic

/-!
# A.3 physical perturbation VALUE bound on t >= 0

This uses only the manuscript's physical-time A4/A7 bounds on `R` and `Ap`.
For the near term it instantiates the already-proved finite near-value result
on time-constant trajectories, avoiding its unnecessarily global-time premise.
The far bound is supplied by the PASSED actual far-value theorem. Reaction
and reference bounds are the existing physical L2/finite-output estimates.
No Qdot is assumed. The distinct A9 applicability obligations remain open.
-/

namespace ReservoirSeismicityControl.Paper2026
open MeasureTheory
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 2000000

theorem paper_A10_physical_psi_value_from_A4_A7_A2
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pregions i))
    (hpFin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrMeas : ∀ i, MeasurableSet (rregions i))
    (hrFin : ∀ i, μ (rregions i) ≠ ⊤)
    (hrPositive : ∀ i, 0 < μ.real (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ)
    (γ10 R0star Cγ MR : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, 0 ≤ t → ‖R t‖ ≤ MR)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (CAp : ℝ)
    (hAp : ∀ t, 0 ≤ t → ‖Ap t‖ ≤ CAp)
    (gamma2 Rphysical : ℝ → X → ℝ) (Rstar : X → ℝ) (sign : ℝ)
    (reactionF : Fin r → ℝ → Lp ℝ 2 μ)
    (reactionC : Fin r → ℝ)
    (hReactionRep : ∀ i t, ∀ᵐ x ∂(μ.restrict (rregions i)),
      ((reactionF i t) x : ℝ) =
        gamma2 t x * Rphysical t x * (Rphysical t x - Rstar x))
    (hReactionL2 : ∀ i t, 0 ≤ t → ‖reactionF i t‖ ≤ reactionC i)
    (referenceVelocity : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceScale : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lreference : ℝ)
    (hReference : ∀ t, 0 ≤ t → ‖referenceVelocity t‖ ≤ Lreference) :
    let near := paperA10PhysicalNearPsi μ pregions hpMeas hpFin rregions hrMeas
      Kγ R γ10 R0star cutoff Ap
    let far := paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
      Kγ R γ10 R0star cutoff Ap
    let reaction := physicalSRFiniteReactionPsi μ rregions gamma2 Rphysical Rstar
      sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let reference := fun t => -(referenceScale (referenceVelocity t))
    let Psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents near far reaction reference
    let Lnear :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / μ.real (pregions i)| *
          (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((‖cutoff‖ *
          (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * CAp))
    let Lfar :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
          |1 / μ.real (pregions i)| *
            (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
          ‖cutoff‖ * (|1 / (γ10 * R0star * μ.real (rregions i))| *
            (Cγ * MR))) * CAp))
    let Lreaction :=
      ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        (|(-sign / (γ10 * R0star))| *
          (((μ.real (rregions i)) ^ (1 / (2 : ℝ)) * reactionC i) /
            μ.real (rregions i)))
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Psi t‖ ≤ Lnear + Lfar + Lreaction + ‖referenceScale‖ * Lreference := by
  classical
  dsimp only
  let near := paperA10PhysicalNearPsi μ pregions hpMeas hpFin rregions hrMeas
    Kγ R γ10 R0star cutoff Ap
  let far := paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
    Kγ R γ10 R0star cutoff Ap
  let reaction := physicalSRFiniteReactionPsi μ rregions gamma2 Rphysical Rstar
    sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
  let reference : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun t => -(referenceScale (referenceVelocity t))
  let Lnear : ℝ :=
    (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
      ((|1 / μ.real (pregions i)| *
        (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
    (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
      ((‖cutoff‖ *
        (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * CAp))
  let Lfar : ℝ :=
    (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
      ((|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
        |1 / μ.real (pregions i)| *
          (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
    (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
      ((|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
        ‖cutoff‖ * (|1 / (γ10 * R0star * μ.real (rregions i))| *
          (Cγ * MR))) * CAp))
  let Lreaction : ℝ :=
    ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
      (|(-sign / (γ10 * R0star))| *
        (((μ.real (rregions i)) ^ (1 / (2 : ℝ)) * reactionC i) /
          μ.real (rregions i)))
  -- The previously proved near VALUE lemma was stated for all real times.
  -- Apply it to constant-in-time fields at each physical t >= 0. This is a
  -- direct specialization of the old result, not a new regularity assumption.
  have hNear : ∀ t, 0 ≤ t → ‖near t‖ ≤ Lnear := by
    intro t ht
    have hRc : ∀ τ : ℝ, ‖(fun _ : ℝ => R t) τ‖ ≤ MR := by
      intro τ
      exact hR t ht
    have hRDc : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
        HasDerivAt (fun _ : ℝ => R t)
          ((fun _ : ℝ => (0 : Lp ℝ 2 μ)) τ) τ :=
      Filter.Eventually.of_forall (fun τ => hasDerivAt_const τ (R t))
    have hRatec : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖(fun _ : ℝ => (0 : Lp ℝ 2 μ)) τ‖ ≤ (0 : ℝ) :=
      Filter.Eventually.of_forall (fun _ => by simp)
    have hApc : ∀ τ : ℝ, ‖(fun _ : ℝ => Ap t) τ‖ ≤ CAp := by
      intro τ
      exact hAp t ht
    have hConst := paper_physical_finite_near_value_bound
      μ pregions hpMeas hpFin rregions hrMeas Kγ
      (fun _ : ℝ => R t) (fun _ : ℝ => (0 : Lp ℝ 2 μ))
      γ10 R0star cutoff Cγ (0 : ℝ) MR
      hCγ hK hRc hRDc hRatec
      (fun _ : ℝ => Ap t) CAp hApc t
    change ‖near t‖ ≤ Lnear at hConst
    exact hConst
  have hFar : ∀ t, 0 ≤ t → ‖far t‖ ≤ Lfar := by
    intro t ht
    exact paper_A10_physical_far_value_from_A4_A7
      μ pregions hpMeas hpFin rregions hrMeas Kγ R
      γ10 R0star Cγ MR hCγ hK hR cutoff Ap CAp hAp t ht
  have hReaction : ∀ t, 0 ≤ t → ‖reaction t‖ ≤ Lreaction := by
    intro t ht
    exact physical_sr_finite_reaction_value_uniform μ rregions hrMeas
      hrFin hrPositive gamma2 Rphysical Rstar sign γ10 R0star
      (paperSRCoordinateEmbed (u := u) (r := r))
      reactionF reactionC hReactionRep hReactionL2 t ht
  have hRef : ∀ t, 0 ≤ t → ‖reference t‖ ≤ ‖referenceScale‖ * Lreference := by
    intro t ht
    change ‖-(referenceScale (referenceVelocity t))‖ ≤ _
    rw [norm_neg]
    calc
      _ ≤ ‖referenceScale‖ * ‖referenceVelocity t‖ :=
        referenceScale.le_opNorm _
      _ ≤ ‖referenceScale‖ * Lreference :=
        mul_le_mul_of_nonneg_left (hReference t ht) (norm_nonneg _)
  have hn : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖near t‖ ≤ Lnear := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hNear t (le_of_lt ht)
  have hf : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖far t‖ ≤ Lfar := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hFar t (le_of_lt ht)
  have hr : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖reaction t‖ ≤ Lreaction := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hReaction t (le_of_lt ht)
  have href : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖reference t‖ ≤ ‖referenceScale‖ * Lreference := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hRef t (le_of_lt ht)
  exact ReservoirSeismicityControl.paper_regional_psi_norm_from_components_ae
    near far reaction reference Lnear Lfar Lreaction
    (‖referenceScale‖ * Lreference) hn hf hr href

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_physical_psi_value_from_A4_A7_A2
