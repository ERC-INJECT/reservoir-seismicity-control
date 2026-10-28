import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualSRNearFinite20261025
import ReservoirSeismicityControl.Paper2026.PositivePressureNearFiniteDerivative
import ReservoirSeismicityControl.Paper2026.PositiveSRReactionFiniteRegions
import ReservoirSeismicityControl.PaperRegionalPerturbationComponents
import Mathlib.Tactic

/-!
# Physical regional perturbation (A10): connection of existing certificates

This is a manuscript-level APPLICATION of the already-proved finite pressure
near-field, finite actual SR near-field, and physical reaction modules to the
previously proved four-component derivative assembly. It does not repeat their
analytic estimates or assume the derivative of the assembled perturbation.

The far-field *finite-output* differentiation and bound are displayed as the
remaining component certificate to be obtained by collecting the physical A9
per-region statements. Hence this does NOT yet claim unconditional (A10).

No derivative of Q is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- The actual near-field part of (14): fixed pressure weights plus the
moving SR weights, both supported near wells. -/
noncomputable def paperA10PhysicalNearPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpmeas : ∀ i, MeasurableSet (pregions i))
    (hpfin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrmeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (γ10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  paperPhysicalPressureNearPsi (r := r) μ pregions hpmeas hpfin cutoff Ap t +
    paperA10ActualSRNearPsi (u := u) μ rregions hrmeas Kγ R γ10 R0star cutoff Ap t

/-- Rate of the actual near-field part. The pressure and SR contributions
are exactly those of the previously passed finite-region theorems. -/
noncomputable def paperA10PhysicalNearRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpmeas : ∀ i, MeasurableSet (pregions i))
    (hpfin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrmeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Rdot : ℝ → Lp ℝ 2 μ) (γ10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (pD : ∀ i : Fin u,
      paperPressureNearWeight μ (pregions i) (hpmeas i) (hpfin i) cutoff ∈ D)
    (w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Ap pdot : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  paperPhysicalPressureNearRate (r := r) μ pregions hpmeas hpfin cutoff
      D A pD pdot t +
    paperA10ActualSRNearRate (u := u) μ rregions hrmeas Kγ Rdot γ10 R0star cutoff
      V E hsep w Ap pdot t

/-- Manuscript (A10) for the physical finite near-field, physical SR reaction,
and fixed-reference contribution, conditional only on a finite-output far-field
A9 certificate and the already established *component* certificates.

`hPressureNear` comes from `paper_physical_pressure_near_finite_derivative_ae`,
`hSRNear` from `paper_A10_actual_SR_near_finite_from_A7`, and `hReaction` from
`physical_sr_finite_reaction_ae_from_evolution`. The premise `hFar` is the
remaining finite-output A9 applicability: it is NOT an assumption on the
assembled `Psi` or its derivative.
-/
theorem paper_A10_actual_regional_derivative_from_physical_components
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpmeas : ∀ i, MeasurableSet (pregions i))
    (hpfin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrmeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (γ10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (pD : ∀ i : Fin u,
      paperPressureNearWeight μ (pregions i) (hpmeas i) (hpfin i) cutoff ∈ D)
    (w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Ap pdot : ℝ → Lp ℝ 2 μ)
    (gamma2 gamma2Rate Rphysical RphysicalRate : ℝ → X → ℝ)
    (Rstar : X → ℝ) (sign : ℝ)
    (farPsi farRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceVelocity referenceAcceleration :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceScale :
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lpnear Lsrnear Lfar Lreaction Lacceleration : ℝ)
    (hPressureNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperPhysicalPressureNearPsi (r := r) μ pregions hpmeas hpfin cutoff Ap)
        (paperPhysicalPressureNearRate (r := r) μ pregions hpmeas hpfin cutoff
          D A pD pdot t) t ∧
      ‖paperPhysicalPressureNearRate (r := r) μ pregions hpmeas hpfin cutoff
          D A pD pdot t‖ ≤ Lpnear)
    (hSRNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperA10ActualSRNearPsi (u := u) μ rregions hrmeas Kγ R γ10 R0star cutoff Ap)
        (paperA10ActualSRNearRate (u := u) μ rregions hrmeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t) t ∧
      ‖paperA10ActualSRNearRate (u := u) μ rregions hrmeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t‖ ≤ Lsrnear)
    (hFar : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar)
    (hReaction : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRFiniteReactionPsi μ rregions gamma2 Rphysical Rstar
          sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r)))
        (physicalSRFiniteReactionRate μ rregions gamma2 gamma2Rate
          Rphysical RphysicalRate Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r)) t) t ∧
      ‖physicalSRFiniteReactionRate μ rregions gamma2 gamma2Rate
          Rphysical RphysicalRate Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r)) t‖ ≤ Lreaction)
    (hReference : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt referenceVelocity (referenceAcceleration t) t)
    (hAcceleration : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceAcceleration t‖ ≤ Lacceleration) :
    let nearPsi := paperA10PhysicalNearPsi μ pregions hpmeas hpfin rregions
      hrmeas Kγ R γ10 R0star cutoff Ap
    let nearRate := paperA10PhysicalNearRate μ pregions hpmeas hpfin
      rregions hrmeas Kγ Rdot γ10 R0star cutoff D A V E hsep pD w Ap pdot
    let reactionPsi := physicalSRFiniteReactionPsi μ rregions gamma2
      Rphysical Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let reactionRate := physicalSRFiniteReactionRate μ rregions gamma2
      gamma2Rate Rphysical RphysicalRate Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let referencePsi := fun t => -(referenceScale (referenceVelocity t))
    let referenceRate := fun t => -(referenceScale (referenceAcceleration t))
    let Psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents
      nearPsi farPsi reactionPsi referencePsi
    let PsiRate := ReservoirSeismicityControl.paperRegionalPsiRateFromComponents
      nearRate farRate reactionRate referenceRate
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt Psi (PsiRate t) t ∧
      ‖deriv Psi t‖ ≤
        (Lpnear + Lsrnear) + Lfar + Lreaction +
          ‖referenceScale‖ * Lacceleration := by
  dsimp only
  let nearPsi := paperA10PhysicalNearPsi μ pregions hpmeas hpfin rregions
      hrmeas Kγ R γ10 R0star cutoff Ap
  let nearRate := paperA10PhysicalNearRate μ pregions hpmeas hpfin
      rregions hrmeas Kγ Rdot γ10 R0star cutoff D A V E hsep pD w Ap pdot
  let reactionPsi := physicalSRFiniteReactionPsi μ rregions gamma2
      Rphysical Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
  let reactionRate := physicalSRFiniteReactionRate μ rregions gamma2
      gamma2Rate Rphysical RphysicalRate Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
  let referencePsi : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun t => -(referenceScale (referenceVelocity t))
  let referenceRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun t => -(referenceScale (referenceAcceleration t))
  let Psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents
    nearPsi farPsi reactionPsi referencePsi
  let PsiRate := ReservoirSeismicityControl.paperRegionalPsiRateFromComponents
    nearRate farRate reactionRate referenceRate
  filter_upwards [hPressureNear, hSRNear, hFar, hReaction,
      hReference, hAcceleration] with t hp hs hf hr href ha
  have hNear : HasDerivAt nearPsi (nearRate t) t := by
    exact hp.1.add hs.1
  have hReferenceAt : HasDerivAt referencePsi (referenceRate t) t := by
    exact ((referenceScale.hasFDerivAt.comp_hasDerivAt t href).neg)
  have hPsi : HasDerivAt Psi (PsiRate t) t :=
    ReservoirSeismicityControl.paper_regional_psi_hasDerivAt_from_components
      nearPsi farPsi reactionPsi referencePsi
      nearRate farRate reactionRate referenceRate
      t hNear hf.1 hr.1 hReferenceAt
  have hNearBound : ‖nearRate t‖ ≤ Lpnear + Lsrnear := by
    exact (norm_add_le _ _).trans (add_le_add hp.2 hs.2)
  have hReferenceBound : ‖referenceRate t‖ ≤
      ‖referenceScale‖ * Lacceleration := by
    calc
      ‖referenceRate t‖ = ‖referenceScale (referenceAcceleration t)‖ := norm_neg _
      _ ≤ ‖referenceScale‖ * ‖referenceAcceleration t‖ :=
        referenceScale.le_opNorm _
      _ ≤ ‖referenceScale‖ * Lacceleration :=
        mul_le_mul_of_nonneg_left ha (norm_nonneg _)
  have hRateBound : ‖PsiRate t‖ ≤
      (Lpnear + Lsrnear) + Lfar + Lreaction +
        ‖referenceScale‖ * Lacceleration := by
    change ‖nearRate t + farRate t + reactionRate t + referenceRate t‖ ≤ _
    calc
      _ ≤ ‖nearRate t‖ + ‖farRate t‖ + ‖reactionRate t‖ +
          ‖referenceRate t‖ := by
        have h1 :
            ‖nearRate t + farRate t + reactionRate t + referenceRate t‖ ≤
              ‖nearRate t + farRate t + reactionRate t‖ +
                ‖referenceRate t‖ :=
          norm_add_le _ _
        have h2 :
            ‖nearRate t + farRate t + reactionRate t‖ ≤
              ‖nearRate t + farRate t‖ + ‖reactionRate t‖ :=
          norm_add_le _ _
        have h3 :
            ‖nearRate t + farRate t‖ ≤
              ‖nearRate t‖ + ‖farRate t‖ :=
          norm_add_le _ _
        linarith only [h1, h2, h3]
      _ ≤ (Lpnear + Lsrnear) + Lfar + Lreaction +
          ‖referenceScale‖ * Lacceleration := by
            exact add_le_add
              (add_le_add (add_le_add hNearBound hf.2) hr.2)
              hReferenceBound
  refine ⟨hPsi, ?_⟩
  rw [hPsi.deriv]
  exact hRateBound

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_actual_regional_derivative_from_physical_components
