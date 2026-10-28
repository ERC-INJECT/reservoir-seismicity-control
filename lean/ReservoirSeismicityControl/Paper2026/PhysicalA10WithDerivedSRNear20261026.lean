import ReservoirSeismicityControl.Paper2026.PhysicalA10WithDerivedPressureNear20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualSRNearFinite20261025
import Mathlib.Tactic

/-!
# A10: construct the actual signed SR near derivative from A7

Uses the PASSED finite-region A7 near theorem and the PASSED A10 theorem
with physical A9 rates and pressure near-field. The weak Neumann and symmetric
pressure realizations are explicitly identified as the SAME physical field.
The near-field derivative and its bound, and the domain representatives w,
are CONSTRUCTED, not assumptions. The signed SR H² and local elliptic cutoff
certificates remain explicit inputs to be discharged in the next step.
No Qdot assumption; no proof of the already established kernel theory.
-/
namespace ReservoirSeismicityControl.Paper2026
open MeasureTheory
open scoped NNReal InnerProductSpace BigOperators Topology
set_option maxHeartbeats 2000000

theorem paper_A10_actual_control_inputs_with_derived_pressure_and_SR_near
    {X U H2 : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [NormedAddCommGroup H2] [NormedSpace ℝ H2] {u r : ℕ}
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
    (pdot : ℝ → Lp ℝ 2 μ)
    /- Identifies Ap with the physical symmetric Neumann generator on pressure. -/
    (hPressureSymm : ∀ a b : D,
      ⟪A a, (b : Lp ℝ 2 μ)⟫_ℝ = ⟪(a : Lp ℝ 2 μ), A b⟫_ℝ)
    (pressure : ℝ → Lp ℝ 2 μ)
    (hPressureD : ∀ t, pressure t ∈ D)
    (hApPressure : ∀ t, Ap t = A ⟨pressure t, hPressureD t⟩)
    (CAw : Fin u → ℝ) (CPt : ℝ)
    (hAw : ∀ i, ‖A ⟨paperPressureNearWeight μ (pregions i)
      (hpMeas i) (hpFin i) cutoff, pD i⟩‖ ≤ CAw i)
    (hPressureRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt pressure (pdot t) t)
    (hPtBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖pdot t‖ ≤ CPt)
    /- SAME physical pressure in the symmetric and weak Neumann realizations.
       This identifies the two generators; it is not a second evolution. -/
    (hEsym : ∀ a b : V, E a b = E b a)
    (pWeak : ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hSamePressure : ∀ t,
      (((pWeak t : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
        Lp ℝ 2 μ) = pressure t)
    (hSameGenerator : ∀ t,
      ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (pWeak t) =
        A ⟨pressure t, hPressureD t⟩)
    /- Positive-time physical pressure generator continuity from A.1. -/
    (hApContinuous : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ContinuousAt Ap t)
    /- A.2 signed SR local H², and A.3 cited cutoff-to-Neumann lift. -/
    (μU : Fin r → Measure U)
    (embedU : (i : Fin r) → H2 →L[ℝ] Lp ℝ 2 (μU i))
    (localRestriction : (i : Fin r) →
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μU i))
    (CH2 CA : Fin r → ℝ)
    (hCA : ∀ i, 0 ≤ CA i)
    (hCH2 : ∀ i, 0 ≤ CH2 i)
    (hRH2 : ∀ i τ, 0 ≤ τ → ∃ y : H2,
      embedU i y = localRestriction i (R τ) ∧ ‖y‖ ≤ CH2 i)
    (lift : Fin r → H2 → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hLiftRep : ∀ (i : Fin r) (y : H2) (rr : Lp ℝ 2 μ),
      embedU i y = localRestriction i rr →
        ((((lift i y : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
          Lp ℝ 2 μ)) =
            cutoff ((1 / (γ10 * R0star * μ.real (rregions i)) : ℝ) •
              ReservoirSeismicityControl.paperFarLpProjection μ (rregions i) (hrMeas i) (Kγ rr)))
    (hLiftBound : ∀ i y,
      ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (lift i y)‖ ≤
        CA i * ‖y‖)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hRdot : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
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
    /- The actual A5/SR premises of the PASSED global far-field theorem.
       No individual A9 scalar derivative/bound is assumed. -/
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ)
    (Tfar : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hPhysicalKernel : ∀ i : Fin m, ∀ lag : ℝ, 0 < lag →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i lag)) =
          -(Tfar lag (f i)))
    (hA5Causal : ∀ t : NNReal,
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (Ap (t : ℝ)) =
          -(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
            (S t (S.generator p₀)) +
              ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
                (Q i s) • Tfar ((t : ℝ) - s) (f i)))
    (hPressureWeight : ∀ i : Fin u,
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff) =
          paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff)
    /- Physical initial-flux compatibility: p_t(0) ∈ D(A), not A p(0) ∈ D(A). -/
    (pt0 : S.generatorDomain)
    (hInitial : (pt0 : Lp ℝ 2 μ) =
      S.generator p₀ + ∑ i : Fin m, (Q i 0) • f i)
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (Mhom : Fin m → ℝ)
    (hFarDG : ∀ (i : Fin m) (t : ℝ) (ht : 0 < t),
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)‖
        ≤ Mhom i)
    /- Actual physical causal forcing: second-order Neumann kernel data. -/
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (B₀ B₁ : Fin m → ℝ → ℝ)
    (hB₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₀ j lag)
    (hB₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₁ j lag)
    (hDG₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))‖
        ≤ B₀ j lag)
    (hDG₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (second j lag)‖
        ≤ B₁ j lag)
    (hB₀Int : ∀ j : Fin m,
      Integrable (B₀ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₁Int : ∀ j : Fin m,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₀Zero : ∀ j : Fin m,
      Filter.Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hOrbitMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSecondMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
          (second j lag))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (qext : Fin m → ℝ → ℝ)
    (hQext : ∀ j s, qext j s = if 0 ≤ s then Q j s else 0)
    (hqLoc : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (qext j) (volume : Measure ℝ))
    (Mflux : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |qext j s| ≤ Mflux j)
    (hDensity : PaperA9BanachW11Density μ)
    (hRInt : ∀ N : ℕ, IntervalIntegrable Rdot volume (0 : ℝ) ((N : ℝ) + 1))
    (hRIntegrated : ∀ t : ℝ, 0 ≤ t →
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    (Cpw : Fin u → ℝ) (Crw Crwd : Fin r → ℝ)
    (Cp : ℝ)
    (hPWBound : ∀ i : Fin u,
      ‖paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ ≤ Cpw i)
    (hRWBound : ∀ i : Fin r, ∀ t : ℝ, 0 < t →
      ‖paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        γ10 R0star cutoff t‖ ≤ Crw i)
    (hRwdBound : ∀ i : Fin r, ∀ᵐ t : ℝ ∂volume,
      0 < t →
        ‖paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          γ10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              γ10 R0star t)‖ ≤ Crwd i)
    (hApBound : ∀ t : ℝ, 0 < t →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)‖ ≤ Cp)
    (hcutoffAll : ∀ j : Fin r, ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ (rregions j) (hrMeas j) Kγ R
        γ10 R0star τ)) x : ℝ) =
      ζ x * ((paperSRDiffusionWeight μ (rregions j) (hrMeas j) Kγ R
        γ10 R0star τ) x : ℝ))
    (LreactionRate Lacceleration : ℝ)
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
    let Lsrnear : ℝ :=
      ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
        ((‖cutoff‖ *
          (|1 / (γ10 * R0star * μ.real (rregions i))| *
            (Cγ * CR))) * CAp + (CA i * CH2 i) * CPt)
    ∃ w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E,
    let Lpnear : ℝ :=
      ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
        (CAw i * CPt)
    let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
    let wellRate : Fin m → ℝ → Lp ℝ 2 μ := fun i t =>
      if ht : 0 < t then
        P (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)
      else 0
    let hRate : ℝ → Lp ℝ 2 μ := fun t =>
      -(P (S (Real.toNNReal t) (S.generator pt0))) +
        ∑ i : Fin m, (Q i 0) • wellRate i t
    let Ch : ℝ := ‖P‖ * ‖S.generator pt0‖ +
      ∑ i : Fin m, |Q i 0| * Mhom i
    let forcingKernelRate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    let fRate : ℝ → Lp ℝ 2 μ := fun t =>
      ∑ j : Fin m, ∫ s : ℝ, qext j s • forcingKernelRate j (t - s)
    let Cf : ℝ := ∑ j : Fin m,
      Mflux j * (∫ lag : ℝ, ‖forcingKernelRate j lag‖)
    let pRate := fun (i : Fin u) (t : ℝ) =>
      ⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
        hRate t + fRate t⟫_ℝ
    let rRate := fun (i : Fin r) (t : ℝ) =>
      ⟪paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          γ10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              γ10 R0star t),
        ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)⟫_ℝ +
      ⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        γ10 R0star cutoff t, hRate t + fRate t⟫_ℝ
    let Lp := fun (i : Fin u) => Cpw i * (Ch + Cf)
    let Lr := fun (i : Fin r) => Crwd i * Cp + Crw i * (Ch + Cf)
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
  let Lsrnear : ℝ :=
    ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
      ((‖cutoff‖ *
        (|1 / (γ10 * R0star * μ.real (rregions i))| *
          (Cγ * CR))) * CAp + (CA i * CH2 i) * CPt)
  have hWeakTrajectory :
      (fun t : ℝ =>
        (((pWeak t : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
          Lp ℝ 2 μ)) = pressure := by
    funext t
    exact hSamePressure t
  have hWeakPressureDerivative : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ =>
          (((pWeak τ : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
            Lp ℝ 2 μ)) (pdot t) t := by
    simpa only [hWeakTrajectory] using hPressureRate
  have hApWeak :
      (fun t : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (pWeak t))
        = Ap := by
    funext t
    exact (hSameGenerator t).trans (hApPressure t).symm
  have hWeakGraphContinuous : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ContinuousAt
        (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (pWeak τ)) t := by
    simpa only [hApWeak] using hApContinuous
  have hWeakApBound : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (pWeak t)‖ ≤ CAp := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have htEq : ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (pWeak t) =
        Ap t := congrFun hApWeak t
    simpa only [htEq] using hAp t ht.le
  obtain ⟨w, hwRep, hwBound, hSRNearPhysical⟩ :=
    paper_A10_actual_SR_near_finite_from_A7 (u := u)
      μ μU embedU localRestriction rregions hrMeas
      Kγ R Rdot γ10 R0star cutoff V E hsep hEsym pWeak pdot
      CH2 CA hCA hCH2 hRH2 lift hLiftRep hLiftBound
      Cγ CR CAp CPt hCγ hCR hK
      hRderiv hRdot hWeakPressureDerivative hWeakGraphContinuous
      hWeakApBound hPtBound
  have hSRNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperA10ActualSRNearPsi (u := u) μ rregions hrMeas Kγ R γ10 R0star cutoff Ap)
        (paperA10ActualSRNearRate (u := u) μ rregions hrMeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t) t ∧
      ‖paperA10ActualSRNearRate (u := u) μ rregions hrMeas Kγ Rdot γ10 R0star
          cutoff V E hsep w Ap pdot t‖ ≤ Lsrnear := by
    simpa only [hApWeak, Lsrnear] using hSRNearPhysical
  let Lpnear : ℝ :=
    ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
      (CAw i * CPt)
  have hPressureNearPhysical :=
    paper_physical_pressure_near_finite_derivative_ae (r := r)
      μ pregions hpMeas hpFin cutoff D A hPressureSymm
      pressure pdot hPressureD pD CAw CPt
      hAw hPressureRate hPtBound
  have hApFunction : Ap = (fun t => A ⟨pressure t, hPressureD t⟩) := by
    funext t
    exact hApPressure t
  have hPressureNear : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperPhysicalPressureNearPsi (r := r) μ pregions hpMeas hpFin cutoff Ap)
        (paperPhysicalPressureNearRate (r := r) μ pregions hpMeas hpFin cutoff
          D A pD pdot t) t ∧
      ‖paperPhysicalPressureNearRate (r := r) μ pregions hpMeas hpFin cutoff
          D A pD pdot t‖ ≤ Lpnear := by
    rw [hApFunction]
    exact hPressureNearPhysical
  have hA10 := paper_A10_actual_control_inputs_with_physical_A9_rates
    μ pregions hpMeas hpFin rregions hrMeas hrFin hrPositive
    Kγ R Rdot γ10 R0star Cγ MR hCγ hK hR cutoff Ap CAp hAp
    D A V E hsep pD w pdot gamma2 gamma2Rate Rphysical RphysicalRate
    Rstar sign reactionF reactionC hReactionRep hReactionL2
    referenceVelocity referenceAcceleration referenceScale Lreference
    hReferenceValue ζ hfar S p₀ m f Q Tfar orbit hPhysicalKernel
    hA5Causal hPressureWeight pt0 hInitial hSmooth Mhom hFarDG
    second hOrbit B₀ B₁ hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
    hOrbitMeas hSecondMeas qext hQext hqLoc hqMeas Mflux hqBound hDensity
    hRInt hRIntegrated Cpw Crw Crwd Cp hPWBound hRWBound hRwdBound
    hApBound hcutoffAll Lpnear Lsrnear LreactionRate Lacceleration
    hPressureNear hSRNear hReactionDerivative hReferenceDerivative hAcceleration
  dsimp only at hA10
  dsimp only
  exact ⟨w, hA10⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_actual_control_inputs_with_derived_pressure_and_SR_near
