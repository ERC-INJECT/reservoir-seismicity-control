import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualRegionalAssembly20261025
import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import ReservoirSeismicityControl.Paper2026.PhysicalA9W11ManuscriptApplicability20261025
import Mathlib.Tactic

/-!
# Appendix A.3: physical finite far observations, from scalar A9 certificates

The previously established A9 formula is scalar, and the previously passed
A10 assembly expects a single vector-valued far certificate. This module
connects them using the ACTUAL pressure and signed-SR far weights.

The input scalar derivative statements below are the conclusions to be
supplied by the EXISTING physical per-region A9 results. Their rate bounds
are the corresponding A8 / initial-pressure certificates. The theorem does
not assume the assembled far derivative, its norm bound, or bounded Qdot.

IMPORTANT: per-region physical A9 applicability (separated projected Neumann
semigroup, W1,1 approximation, and causal pressure identity) is NOT thereby
discharged. This module finishes only the finite-output bridge to A10.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- Physical pressure far weight: (1-zeta) chi_region / |region|.
The pressure near weight is already defined and verified. -/
noncomputable def paperA10PressureFarWeight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hMeas : MeasurableSet region)
    (hFin : μ region ≠ ⊤)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (1 / μ.real region : ℝ) • indicatorConstLp 2 hMeas hFin (1 : ℝ) -
    paperPressureNearWeight μ region hMeas hFin cutoff

/-- Near + far is exactly the normalized indicator pressure weight. -/
theorem paper_A10_pressure_near_far_exact_split
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hMeas : MeasurableSet region)
    (hFin : μ region ≠ ⊤)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    paperPressureNearWeight μ region hMeas hFin cutoff +
      paperA10PressureFarWeight μ region hMeas hFin cutoff =
        (1 / μ.real region : ℝ) • indicatorConstLp 2 hMeas hFin (1 : ℝ) := by
  unfold paperA10PressureFarWeight
  abel

/-- Pressure coordinates of the actual far diffusion term of (14). -/
noncomputable def paperA10PressureFarPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin u → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (hFin : ∀ i, μ (regions i) ≠ ⊤)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
    (-⟪paperA10PressureFarWeight μ (regions i) (hMeas i) (hFin i) cutoff,
        Ap t⟫_ℝ)

/-- SR coordinates of the actual moving far diffusion term of (14). -/
noncomputable def paperA10SRFarPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
    (-⟪paperSRFarDiffusionWeight μ (regions i) (hMeas i) Kγ
        R gamma10 R0star cutoff t, Ap t⟫_ℝ)

/-- Finite vector of the actual physical far pressure and SR observations. -/
noncomputable def paperA10PhysicalFarPsi
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
    (Ap : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  paperA10PressureFarPsi (r := r) μ pregions hpMeas hpFin cutoff Ap t +
    paperA10SRFarPsi (u := u) μ rregions hrMeas Kγ R
      gamma10 R0star cutoff Ap t

/-- Coordinate rate prescribed by the per-region four-term A9 formulas.
The scalar rates `pRate` and `rRate` INCLUDE the positive A9 observation
rate, so the negative sign here matches Psi's -<w,Ap>. -/
noncomputable def paperA10PhysicalFarRate
    {u r : ℕ}
    (pRate : Fin u → ℝ → ℝ) (rRate : Fin r → ℝ → ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  (∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
      (-(pRate i t))) +
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
      (-(rRate i t)))

/-- The actual finite-output `hFar` certificate needed by A10, obtained
from the individual physical A9 rates and A8 bounds. The hypotheses concern
ONLY individual A9 formulas and their quantitative rate envelopes, not
existence or boundedness of the assembled finite-dimensional derivative.
All signs and regional embeddings agree with equation (14).
-/
theorem paper_A9_actual_finite_far_certificate_for_A10
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
            (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (rRate i t) t)
    (hSRA8Bound : ∀ i : Fin r, ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      |rRate i t| ≤ Lr i) :
    let farPsi := paperA10PhysicalFarPsi μ pregions hpMeas hpFin
      rregions hrMeas Kγ R gamma10 R0star cutoff Ap
    let farRate := paperA10PhysicalFarRate pRate rRate
    let Lfar :=
      (∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ * Lp i) +
      (∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * Lr i)
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt farPsi (farRate t) t ∧ ‖farRate t‖ ≤ Lfar := by
  classical
  dsimp only
  have hPone (i : Fin u) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
          (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
        (pRate i t) t ∧ |pRate i t| ≤ Lp i := by
    filter_upwards [hPressureA9 i, hPressureA8Bound i] with t hd hb
    exact ⟨hd, hb⟩
  have hRone (i : Fin r) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
          (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (rRate i t) t ∧ |rRate i t| ≤ Lr i := by
    filter_upwards [hSRA9 i, hSRA8Bound i] with t hd hb
    exact ⟨hd, hb⟩
  have hPfinite (s : Finset (Fin u)) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ i ∈ s,
        HasDerivAt
          (fun τ : ℝ => ⟪paperA10PressureFarWeight μ (pregions i)
            (hpMeas i) (hpFin i) cutoff, Ap τ⟫_ℝ)
          (pRate i t) t ∧ |pRate i t| ≤ Lp i := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with t
        simp
    | @insert i s hi ih =>
        filter_upwards [hPone i, ih] with t hit hst j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hit
        · exact hst j hjs
  have hRfinite (s : Finset (Fin r)) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ i ∈ s,
        HasDerivAt
          (fun τ : ℝ => ⟪paperSRFarDiffusionWeight μ (rregions i)
            (hrMeas i) Kγ R gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
          (rRate i t) t ∧ |rRate i t| ≤ Lr i := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with t
        simp
    | @insert i s hi ih =>
        filter_upwards [hRone i, ih] with t hit hst j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hit
        · exact hst j hjs
  filter_upwards [hPfinite Finset.univ, hRfinite Finset.univ]
    with t hpall hrall
  have hp (i : Fin u) := hpall i (Finset.mem_univ i)
  have hr (i : Fin r) := hrall i (Finset.mem_univ i)
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

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_pressure_near_far_exact_split
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_actual_finite_far_certificate_for_A10
