import ReservoirSeismicityControl.Paper2026.PhysicalA9SRFarFiniteHorizon20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9FiniteFarToA10_20261025
import Mathlib.Tactic

/-!
Appendix A9, genuine finite-horizon physical regional far-field assembly.
The scalar A9 pressure and moving-SR derivatives are supplied by the already
proved A5/W¹,¹/DG and Bochner SR results, NOT taken as new hypotheses.
The final finite-dimensional rate bound is derived coordinatewise.

IMPORTANT: this is a.e. on 0<t<T and is NOT an all-time A10 certificate.
The positive-lag kernel, causal value, homogeneous/forcing vector derivative,
physical projection, and vector bounds have the precise applicability inputs
stated in the theorem. No bounded derivative of Q is assumed.
-/
namespace ReservoirSeismicityControl.Paper2026
open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology
set_option maxHeartbeats 2000000

/-- Reuse the established finite-output A9 assembly proof with the only
necessary change: local scalar statements on a finite physical horizon.
This private helper does not assert any physical scalar derivative. -/
private theorem paper_A9_finite_far_horizon_assembly_from_local_scalar
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X)
    (pregions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pregions i))
    (hpFin : ∀ i, μ (pregions i) ≠ ⊤)
    (rregions : Fin r → Set X)
    (hrMeas : ∀ i, MeasurableSet (rregions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ)
    (pRate : Fin u → ℝ → ℝ) (rRate : Fin r → ℝ → ℝ)
    (Lp : Fin u → ℝ) (Lr : Fin r → ℝ)
    (T : NNReal)
    (hPressureLocal : ∀ i : Fin u, ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
            (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
          (pRate i t) t ∧ |pRate i t| ≤ Lp i)
    (hSRLocal : ∀ i : Fin r, ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
            (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
          (rRate i t) t ∧ |rRate i t| ≤ Lr i) :
    let farPsi := paperA10PhysicalFarPsi μ pregions hpMeas hpFin
      rregions hrMeas Kγ R gamma10 R0star cutoff Ap
    let farRate := paperA10PhysicalFarRate pRate rRate
    let Lfar :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i)
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar := by
  classical
  dsimp only
  have hPfinite (s : Finset (Fin u)) : ∀ᵐ t : ℝ ∂volume,
      ∀ i ∈ s, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
            (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
          (pRate i t) t ∧ |pRate i t| ≤ Lp i := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with t
        simp
    | @insert i s hi ih =>
        filter_upwards [hPressureLocal i, ih] with t hit hst j hj ht
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hit ht
        · exact hst j hjs ht
  have hRfinite (s : Finset (Fin r)) : ∀ᵐ t : ℝ ∂volume,
      ∀ i ∈ s, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
            (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
          (rRate i t) t ∧ |rRate i t| ≤ Lr i := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with t
        simp
    | @insert i s hi ih =>
        filter_upwards [hSRLocal i, ih] with t hit hst j hj ht
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hit ht
        · exact hst j hjs ht
  filter_upwards [hPfinite Finset.univ, hRfinite Finset.univ]
    with t hpall hrall
  intro ht
  have hp (i : Fin u) := hpall i (Finset.mem_univ i) ht
  have hr (i : Fin r) := hrall i (Finset.mem_univ i) ht
  have hpderiv : HasDerivAt
      (paperA10PressureFarPsi (r := r) μ pregions hpMeas hpFin cutoff Ap)
      (∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
        (-(pRate i t))) t := by
    change HasDerivAt
      (fun τ : ℝ => ∑ i : Fin u,
        paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪paperA10PressureFarWeight μ (pregions i) (hpMeas i)
              (hpFin i) cutoff, Ap τ⟫_ℝ))
      (∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
        (-(pRate i t))) t
    apply HasDerivAt.fun_sum
    intro i _
    exact (paperPressureCoordinateEmbed (u := u) (r := r) i).hasFDerivAt.comp_hasDerivAt
      t ((hp i).1.neg)
  have hrderiv : HasDerivAt
      (paperA10SRFarPsi (u := u) μ rregions hrMeas Kγ R
        gamma10 R0star cutoff Ap)
      (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
        (-(rRate i t))) t := by
    change HasDerivAt
      (fun τ : ℝ => ∑ i : Fin r,
        paperSRCoordinateEmbed (u := u) (r := r) i
          (-⟪paperSRFarDiffusionWeight μ (rregions i) (hrMeas i)
              Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ))
      (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
        (-(rRate i t))) t
    apply HasDerivAt.fun_sum
    intro i _
    exact (paperSRCoordinateEmbed (u := u) (r := r) i).hasFDerivAt.comp_hasDerivAt
      t ((hr i).1.neg)
  have hpbound : ‖∑ i : Fin u,
      paperPressureCoordinateEmbed (u := u) (r := r) i (-(pRate i t))‖ ≤
        ∑ i : Fin u,
          ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i := by
    calc
      _ ≤ ∑ i : Fin u,
            ‖paperPressureCoordinateEmbed (u := u) (r := r) i
              (-(pRate i t))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin u,
            ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
                ‖-(pRate i t)‖ :=
            (paperPressureCoordinateEmbed (u := u) (r := r) i).le_opNorm _
          _ = ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
                |pRate i t| := by rw [norm_neg, Real.norm_eq_abs]
          _ ≤ ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
                Lp i := mul_le_mul_of_nonneg_left (hp i).2 (norm_nonneg _)
  have hrbound : ‖∑ i : Fin r,
      paperSRCoordinateEmbed (u := u) (r := r) i (-(rRate i t))‖ ≤
        ∑ i : Fin r,
          ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i := by
    calc
      _ ≤ ∑ i : Fin r,
            ‖paperSRCoordinateEmbed (u := u) (r := r) i
              (-(rRate i t))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin r,
            ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
                ‖-(rRate i t)‖ :=
            (paperSRCoordinateEmbed (u := u) (r := r) i).le_opNorm _
          _ = ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
                |rRate i t| := by rw [norm_neg, Real.norm_eq_abs]
          _ ≤ ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
                Lr i := mul_le_mul_of_nonneg_left (hr i).2 (norm_nonneg _)
  have hfarDeriv : HasDerivAt
      (paperA10PhysicalFarPsi μ pregions hpMeas hpFin rregions hrMeas
        Kγ R gamma10 R0star cutoff Ap)
      (paperA10PhysicalFarRate pRate rRate t) t := by
    exact hpderiv.add hrderiv
  have hfarBound : ‖paperA10PhysicalFarRate pRate rRate t‖ ≤
      (∑ i : Fin u,
        ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
      (∑ i : Fin r,
        ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i) := by
    exact (norm_add_le _ _).trans (add_le_add hpbound hrbound)
  exact ⟨hfarDeriv, hfarBound⟩


/-- The ACTUAL physical finite-output A9 far certificate on 0<t<T.
Unlike the previously passing finite-output assembly, this theorem does not
require the individual scalar hPressureA9/hSRA9 derivatives or their bounds.
They follow from the canonical pressure A5 identity and moving SR evolution.
The remaining hHomDerivative/hForcingDerivative are vector certificates,
and the remaining estimates bound physical weights and projected vector data.
-/
theorem paper_A9_physical_finite_far_rate_from_actual_A5_SR_on_horizon
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
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ)
    (Tfar : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (hPhysicalKernel : ∀ i : Fin m, ∀ lag : ℝ, 0 < lag →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit i lag)) =
          -(Tfar lag (f i)))
    (Ap : ℝ → Lp ℝ 2 μ)
    (hA5Causal : ∀ t : NNReal, t ≤ T →
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
    (hRInt : IntervalIntegrable Rdot volume (0 : ℝ) (T : ℝ))
    (hRIntegrated : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    (Cpw : Fin u → ℝ) (Crw Crwd : Fin r → ℝ)
    (Cp Ch Cf : ℝ)
    (hPWBound : ∀ i : Fin u,
      ‖paperA10PressureFarWeight μ (pregions i) (hpMeas i) (hpFin i) cutoff‖ ≤ Cpw i)
    (hRWBound : ∀ i : Fin r, ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      ‖paperSRFarDiffusionWeight μ (rregions i) (hrMeas i) Kγ R
        gamma10 R0star cutoff t‖ ≤ Crw i)
    (hRwdBound : ∀ i : Fin r, ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        ‖paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
          gamma10 R0star t - cutoff
            (paperSRDiffusionWeightRate μ (rregions i) (hrMeas i) Kγ Rdot
              gamma10 R0star t)‖ ≤ Crwd i)
    (hApBound : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
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
    ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
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
  have hp (i : Fin u) : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
            (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
          (pRate i t) t ∧ |pRate i t| ≤ Lp i := by
    filter_upwards [] with t
    intro ht
    exact paper_A9_actual_pressure_far_rate_on_finite_horizon
      μ {x : X | ζ x ≠ 1} hfar (pregions i) (hpMeas i) (hpFin i) cutoff
      V E hsep S T p₀ m f Q Tfar orbit hPhysicalKernel Ap hA5Causal
      (hPressureWeight i) hRate fRate hHomDerivative hForcingDerivative
      (Cpw i) Ch Cf (hPWBound i) hHBound hFBound t ht
  have hr (i : Fin r) : ∀ᵐ t : ℝ ∂volume,
      t ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt
          (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
            (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
          (rRate i t) t ∧ |rRate i t| ≤ Lr i := by
    have h := paper_A9_actual_SR_far_rate_on_finite_horizon
      μ (rregions i) (hrMeas i) Kγ R Rdot gamma10 R0star cutoff
      ζ hfar (hcutoffAll i) V E hsep S T p₀ m f Q Tfar orbit
      hPhysicalKernel Ap hA5Causal hRate fRate
      (fun t ht => hHomDerivative t ht.1)
      (fun t ht => hForcingDerivative t ht.1)
      hRInt hRIntegrated (Crw i) (Crwd i) Cp Ch Cf
      (hRWBound i) (hRwdBound i) hApBound
      (fun t ht => hHBound t ht.1)
      (fun t ht => hFBound t ht.1)
    simpa only [rRate, Lr] using h
  exact paper_A9_finite_far_horizon_assembly_from_local_scalar
    μ pregions hpMeas hpFin rregions hrMeas Kγ R gamma10 R0star
    cutoff Ap pRate rRate Lp Lr T hp hr

#print axioms paper_A9_physical_finite_far_rate_from_actual_A5_SR_on_horizon

end ReservoirSeismicityControl.Paper2026
