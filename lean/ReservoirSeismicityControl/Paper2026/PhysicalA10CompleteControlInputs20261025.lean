import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualPsiValuePhysicalTime20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteFarToA10_20261025
import Mathlib.Tactic

/-!
# Manuscript A.3 -> A.4/B: actual physical Psi and PsiRate

Use the PASSED physical A10 value theorem, the PASSED regional derivative
assembly, and the PASSED finite A9-to-A10 theorem.  The resulting certificate
has precisely the two norms and the a.e. derivative required by the preexisting
A14/B19 control proofs.  In particular neither the Psi bound nor the PsiRate
bound nor HasDerivAt Psi is a new hypothesis.

The only far-field input consists of the per-region A9 certificates; their
analytic / DG / causal applicability is not claimed here. No bound on Qdot.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 2000000

/-- Actual A10 outputs in the form needed by (22) and (29).  The per-region
far-field A9 data and the physical near/reaction rate certificates are inputs.
The *assembled* Psi, its derivative, and both uniform bounds are conclusions. -/
theorem paper_A10_actual_control_inputs_from_A4_A7_A9
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
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (γ10 R0star Cγ MR : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ t, 0 ≤ t → ‖R t‖ ≤ MR)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (CAp : ℝ)
    (hAp : ∀ t, 0 ≤ t → ‖Ap t‖ ≤ CAp)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (A : D →ₗ[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (pD : ∀ i : Fin u,
      paperPressureNearWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff ∈ D)
    (w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (pdot : ℝ → Lp ℝ 2 μ)
    (gamma2 gamma2Rate Rphysical RphysicalRate : ℝ → X → ℝ)
    (Rstar : X → ℝ) (sign : ℝ)
    (reactionF : Fin r → ℝ → Lp ℝ 2 μ)
    (reactionC : Fin r → ℝ)
    (hReactionRep : ∀ i t, ∀ᵐ x ∂(μ.restrict (rregions i)),
      ((reactionF i t) x : ℝ) =
        gamma2 t x * Rphysical t x * (Rphysical t x - Rstar x))
    (hReactionL2 : ∀ i t, 0 ≤ t → ‖reactionF i t‖ ≤ reactionC i)
    (referenceVelocity referenceAcceleration :
      ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (referenceScale :
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lreference : ℝ)
    (hReferenceValue : ∀ t, 0 ≤ t → ‖referenceVelocity t‖ ≤ Lreference)
    (pRate : Fin u → ℝ → ℝ) (rRate : Fin r → ℝ → ℝ)
    (Lp : Fin u → ℝ) (Lr : Fin r → ℝ)
    (hPressureA9 : ∀ i : Fin u, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
            (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
        (pRate i t) t)
    (hPressureA8Bound : ∀ i : Fin u, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |pRate i t| ≤ Lp i)
    (hSRA9 : ∀ i : Fin r, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
            (hrMeas i) Kγ R γ10 R0star cutoff τ, Ap τ⟫_ℝ)
        (rRate i t) t)
    (hSRA8Bound : ∀ i : Fin r, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |rRate i t| ≤ Lr i)
    (Lpnear Lsrnear LreactionRate Lacceleration : ℝ)
    (hPressureNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperPhysicalPressureNearPsi (r := r) μ pregions hpMeas hpFin cutoff Ap)
        (paperPhysicalPressureNearRate (r := r) μ pregions hpMeas hpFin cutoff
          D A pD pdot t) t ∧
      ‖paperPhysicalPressureNearRate (r := r) μ pregions hpMeas hpFin cutoff
          D A pD pdot t‖ ≤ Lpnear)
    (hSRNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperA10ActualSRNearPsi (u := u) μ rregions hrMeas Kγ R γ10 R0star cutoff Ap)
        (paperA10ActualSRNearRate (u := u) μ rregions hrMeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t) t ∧
      ‖paperA10ActualSRNearRate (u := u) μ rregions hrMeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t‖ ≤ Lsrnear)
    (hReactionDerivative : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (physicalSRFiniteReactionPsi μ rregions gamma2 Rphysical Rstar
          sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r)))
        (physicalSRFiniteReactionRate μ rregions gamma2 gamma2Rate
          Rphysical RphysicalRate Rstar sign γ10 R0star
          (paperSRCoordinateEmbed (u := u) (r := r)) t) t ∧
      ‖physicalSRFiniteReactionRate μ rregions gamma2 gamma2Rate
          Rphysical RphysicalRate Rstar sign γ10 R0star
          (paperSRCoordinateEmbed (u := u) (r := r)) t‖ ≤ LreactionRate)
    (hReferenceDerivative : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt referenceVelocity (referenceAcceleration t) t)
    (hAcceleration : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖referenceAcceleration t‖ ≤ Lacceleration) :
    let near := paperA10PhysicalNearPsi μ pregions hpMeas hpFin rregions
      hrMeas Kγ R γ10 R0star cutoff Ap
    let far := paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions
      hrMeas Kγ R γ10 R0star cutoff Ap
    let reaction := physicalSRFiniteReactionPsi μ rregions gamma2
      Rphysical Rstar sign γ10 R0star (paperSRCoordinateEmbed (u := u) (r := r))
    let reference := fun t => -(referenceScale (referenceVelocity t))
    let Psi := ReservoirSeismicityControl.paperRegionalPsiFromComponents near far reaction reference
    let nearRate := paperA10PhysicalNearRate μ pregions hpMeas hpFin rregions
      hrMeas Kγ Rdot γ10 R0star cutoff D A V E hsep pD w Ap pdot
    let farRate := paperA10PhysicalFarRate pRate rRate
    let reactionRate := physicalSRFiniteReactionRate μ rregions gamma2
      gamma2Rate Rphysical RphysicalRate Rstar sign γ10 R0star
      (paperSRCoordinateEmbed (u := u) (r := r))
    let referenceRate := fun t => -(referenceScale (referenceAcceleration t))
    let PsiRate := ReservoirSeismicityControl.paperRegionalPsiRateFromComponents
      nearRate farRate reactionRate referenceRate
    let Lnear :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / μ.real (pregions i)| *
          (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((‖cutoff‖ *
          (|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR))) * CAp))
    let LfarValue :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / μ.real (pregions i)| * (μ.real (pregions i)) ^ (1 / (2 : ℝ)) +
          |1 / μ.real (pregions i)| *
            (‖cutoff‖ * (μ.real (pregions i)) ^ (1 / (2 : ℝ)))) * CAp)) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((|1 / (γ10 * R0star * μ.real (rregions i))| * (Cγ * MR) +
          ‖cutoff‖ * (|1 / (γ10 * R0star * μ.real (rregions i))| *
            (Cγ * MR))) * CAp))
    let LreactionValue :=
      ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        (|(-sign / (γ10 * R0star))| *
          (((μ.real (rregions i)) ^ (1 / (2 : ℝ)) * reactionC i) /
            μ.real (rregions i)))
    let Lpsi := Lnear + LfarValue + LreactionValue + ‖referenceScale‖ * Lreference
    let LfarRate :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i)
    let LpsiRate := (Lpnear + Lsrnear) + LfarRate + LreactionRate +
      ‖referenceScale‖ * Lacceleration
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt Psi (PsiRate t) t ∧
      ‖Psi t‖ ≤ Lpsi ∧ ‖PsiRate t‖ ≤ LpsiRate := by
  classical
  have hValue := paper_A10_physical_psi_value_from_A4_A7_A2
    μ pregions hpMeas hpFin rregions hrMeas hrFin hrPositive
    Kγ R γ10 R0star Cγ MR hCγ hK hR cutoff Ap CAp hAp
    gamma2 Rphysical Rstar sign reactionF reactionC
    hReactionRep hReactionL2 referenceVelocity referenceScale
    Lreference hReferenceValue
  have hFar := paper_A9_actual_finite_far_certificate_for_A10
    μ pregions hpMeas hpFin rregions hrMeas Kγ R γ10 R0star
    cutoff Ap pRate rRate Lp Lr hPressureA9 hPressureA8Bound
    hSRA9 hSRA8Bound
  have hDerivative := paper_A10_actual_regional_derivative_from_physical_components
    μ pregions hpMeas hpFin rregions hrMeas Kγ R Rdot γ10 R0star
    cutoff D A V E hsep pD w Ap pdot gamma2 gamma2Rate
    Rphysical RphysicalRate Rstar sign
    (paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
      Kγ R γ10 R0star cutoff Ap)
    (paperA10PhysicalFarRate pRate rRate)
    referenceVelocity referenceAcceleration referenceScale
    Lpnear Lsrnear
    ((∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i))
    LreactionRate Lacceleration
    hPressureNear hSRNear hFar hReactionDerivative
    hReferenceDerivative hAcceleration
  dsimp only at hValue hDerivative
  dsimp only
  filter_upwards [hValue, hDerivative] with t hv hd
  refine ⟨hd.1, hv, ?_⟩
  simpa only [hd.1.deriv] using hd.2

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_actual_control_inputs_from_A4_A7_A9
