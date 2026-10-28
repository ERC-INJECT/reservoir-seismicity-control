import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteOutputsOnHorizon20261025
import Mathlib.Tactic

/-!
# Physical regional A9, local-to-global WITHOUT assuming the far derivative

Reuse the user-confirmed PASSED finite-horizon actual A5/SR far-field theorem.
The physical pressure generator, SR evolution and component bounds are required
uniformly over all positive times.  Countably many finite horizons cover the
positive half-line, and each finite-horizon A9 result gives a.e. estimates.
The result directly supplies the actual A10 `hFar` positive-time premise.
Neither the final far derivative nor its bound is assumed. No Qdot premise.
-/

namespace ReservoirSeismicityControl.Paper2026
open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology
set_option maxHeartbeats 2000000

/-- Global positive-time ACTUAL physical finite-output far-field certificate.
    The same physical trajectory and uniform constants work on all horizons.
    No global derivative assertion is introduced as a premise. -/
theorem paper_A9_physical_finite_far_rate_on_all_positive_time
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pregions i))
    (hpFin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrMeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
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
    (Ap : ℝ → Lp ℝ 2 μ)
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
    (hRate fRate : ℝ → Lp ℝ 2 μ)
    (hHomDerivative : ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => if hτ : 0 ≤ τ then
          -(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
            (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀))) else 0)
        (hRate t) t)
    (hForcingDerivative : ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => ∑ i : Fin m,
          ∫ s in (0 : ℝ)..τ, (Q i s) •
            ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
                (orbit i (τ - s))))
        (fRate t) t)
    (hRInt : ∀ N : ℕ, IntervalIntegrable Rdot volume (0 : ℝ) ((N : ℝ) + 1))
    (hRIntegrated : ∀ t : ℝ, 0 ≤ t →
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    (Cpw : Fin u → ℝ) (Crw Crwd : Fin r → ℝ)
    (Cp Ch Cf : ℝ)
    (hPWBound : ∀ i : Fin u,
      ‖paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ ≤ Cpw i)
    (hRWBound : ∀ i : Fin r, ∀ t : ℝ, 0 < t →
      ‖paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        gamma10 R0star cutoff t‖ ≤ Crw i)
    (hRwdBound : ∀ i : Fin r, ∀ᵐ t : ℝ ∂volume,
      0 < t →
        ‖paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          gamma10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              gamma10 R0star t)‖ ≤ Crwd i)
    (hApBound : ∀ t : ℝ, 0 < t →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)‖ ≤ Cp)
    (hHBound : ∀ t : ℝ, 0 < t → ‖hRate t‖ ≤ Ch)
    (hFBound : ∀ t : ℝ, 0 < t → ‖fRate t‖ ≤ Cf)
    (hcutoffAll : ∀ j : Fin r, ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ (rregions j) (hrMeas j) Kγ R
        gamma10 R0star τ)) x : ℝ) =
      ζ x * ((paperSRDiffusionWeight μ (rregions j) (hrMeas j) Kγ R
        gamma10 R0star τ) x : ℝ)) :
    let pRate := fun (i : Fin u) (t : ℝ) =>
      ⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
        hRate t + fRate t⟫_ℝ
    let rRate := fun (i : Fin r) (t : ℝ) =>
      ⟪paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          gamma10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              gamma10 R0star t),
        ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)⟫_ℝ +
      ⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        gamma10 R0star cutoff t, hRate t + fRate t⟫_ℝ
    let Lp := fun (i : Fin u) => Cpw i * (Ch + Cf)
    let Lr := fun (i : Fin r) => Crwd i * Cp + Crw i * (Ch + Cf)
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
          Kγ R gamma10 R0star cutoff Ap)
        (paperA10PhysicalFarRate pRate rRate t) t ∧
      ‖paperA10PhysicalFarRate pRate rRate t‖ ≤
        (∑ i : Fin u,
          ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
        (∑ i : Fin r,
          ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i) := by
  classical
  dsimp only
  let pRate := fun (i : Fin u) (t : ℝ) =>
    ⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff,
      hRate t + fRate t⟫_ℝ
  let rRate := fun (i : Fin r) (t : ℝ) =>
    ⟪paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
        gamma10 R0star t - cutoff
          (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
            gamma10 R0star t),
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t)⟫_ℝ +
    ⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
      gamma10 R0star cutoff t, hRate t + fRate t⟫_ℝ
  let Lp := fun (i : Fin u) => Cpw i * (Ch + Cf)
  let Lr := fun (i : Fin r) => Crwd i * Cp + Crw i * (Ch + Cf)
  let farPsi := paperA10PhysicalFarPsi μ pregions hpMeas hpFin
    rregions hrMeas Kγ R gamma10 R0star cutoff Ap
  let farRate := paperA10PhysicalFarRate pRate rRate
  let Lfar :=
    (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
    (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i)
  have hEach (N : ℕ) : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) →
        HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar := by
    let T : NNReal := ⟨(N : ℝ) + 1, by positivity⟩
    have hRwdLocal : ∀ i : Fin r, ∀ᵐ t : ℝ ∂volume,
        t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        ‖paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          gamma10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              gamma10 R0star t)‖ ≤ Crwd i := by
      intro i
      filter_upwards [hRwdBound i] with t ht
      intro hτ
      exact ht hτ.1
    have hLocal := paper_A9_physical_finite_far_rate_from_actual_A5_SR_on_horizon
      μ pregions hpMeas hpFin rregions hrMeas Kγ R Rdot
      gamma10 R0star cutoff ζ hfar V E hsep
      S T p₀ m f Q Tfar orbit hPhysicalKernel Ap
      (fun t _ => hA5Causal t) hPressureWeight
      hRate fRate hHomDerivative hForcingDerivative
      (hRInt N) (fun t ht => hRIntegrated t ht.1)
      Cpw Crw Crwd Cp Ch Cf hPWBound
      (fun i t ht => hRWBound i t ht.1)
      hRwdLocal (fun t ht => hApBound t ht.1)
      hHBound hFBound hcutoffAll
    have hT : (T : ℝ) = (N : ℝ) + 1 := rfl
    simpa only [farPsi, farRate, Lfar, pRate, rRate, Lp, Lr, hT]
      using hLocal
  have hAll : ∀ᵐ t : ℝ ∂volume,
      ∀ N : ℕ, t ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) →
        HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar := by
    exact eventually_countable_forall.mpr hEach
  have hReal : ∀ᵐ t : ℝ ∂volume,
      0 < t → HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar := by
    filter_upwards [hAll] with t hNt ht
    obtain ⟨N, hN⟩ := exists_nat_gt t
    apply hNt N
    exact ⟨ht, by linarith⟩
  change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
    HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar
  exact (ae_restrict_iff' measurableSet_Ioi).2 hReal

#print axioms paper_A9_physical_finite_far_rate_on_all_positive_time

end ReservoirSeismicityControl.Paper2026
