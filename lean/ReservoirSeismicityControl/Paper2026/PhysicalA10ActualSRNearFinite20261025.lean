import ReservoirSeismicityControl.Paper2026.PhysicalA7ToSRNearMoving20261025
import ReservoirSeismicityControl.Paper2026.PositiveSRNearFiniteWeakRate
import Mathlib.Tactic

/-!
# ReservoirSeismicityControl (A10): finite actual signed-SR near-field derivative

This is an APPLICATION of the previously passed A7 -> actual single-region
weak-Neumann near-field derivative.  It does not redo Sobolev calculus,
Neumann product rules, pressure evolution, or SR dynamics.

The physical near-field observation is the canonical finite-dimensional sum
in the SR slots of equation (14).  Its derivative is established from the
actual strong derivatives of R and p, the local A7 H² certificates, and
ONE externally cited local cutoff/elliptic lift for each region.  No bound
on Qdot, derivative of A p, or premise asserting a near-field derivative.

The cutoff lifts are stated with the same universal representative and graph
conditions as the previously passed one-region theorem.  Thus this theorem
does NOT claim to formalize the cited local elliptic theorem itself.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter TopologicalSpace
open scoped InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- The actual SR near-diffusion part of equation (14), in its canonical
output coordinates.  The sign here is the **minus** in `Psi`, not the SR
coupling sign `s` (which is already accounted for by normalized weights). -/
noncomputable def paperA10ActualSRNearPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hregions : ∀ i, MeasurableSet (regions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Ap : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
    (-⟪paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
        gamma10 R0star cutoff t, Ap t⟫_ℝ)

/-- Actual SR near-field rate from the graph-domain representatives
constructed by the cited local A7 cutoff lift. -/
noncomputable def paperA10ActualSRNearRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : Measure X) (regions : Fin r → Set X)
    (hregions : ∀ i, MeasurableSet (regions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Ap pdot : ℝ → Lp ℝ 2 μ) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
    (-(⟪cutoff (paperSRDiffusionWeightRate μ (regions i) (hregions i)
            Kγ Rdot gamma10 R0star t), Ap t⟫_ℝ +
        ⟪ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (w i t),
          pdot t⟫_ℝ))

/-- (A10) SR near-field portion: a.e. exact derivative and uniform bound,
from the physical A7 local H² statements and existing single-region
weak-Neumann product rule.  The returned domain paths are witnesses,
not independently assumed derivatives or regularity of the physical SR.

`μU i`, `embedU i` and `localRestriction i` describe local well
neighborhoods; the common local model `H2` can be chosen as an ambient
Sobolev chart representation for the finite family of neighborhoods.
-/
theorem paper_A10_actual_SR_near_finite_from_A7
    {X U H2 : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [NormedAddCommGroup H2] [NormedSpace ℝ H2]
    {u r : ℕ}
    (μ : Measure X) (μU : Fin r → Measure U)
    (embedU : (i : Fin r) → H2 →L[ℝ] Lp ℝ 2 (μU i))
    (localRestriction : (i : Fin r) → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μU i))
    (regions : Fin r → Set X)
    (hregions : ∀ i, MeasurableSet (regions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ a b : V, E a b = E b a)
    (p : ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (pdot : ℝ → Lp ℝ 2 μ)
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
          cutoff ((1 / (gamma10 * R0star * μ.real (regions i)) : ℝ) •
            ReservoirSeismicityControl.paperFarLpProjection μ (regions i) (hregions i) (Kγ rr)))
    (hLiftBound : ∀ i y,
      ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (lift i y)‖ ≤
        CA i * ‖y‖)
    (Cγ CR CAp CPt : ℝ)
    (hCγ : 0 ≤ Cγ) (hCR : 0 ≤ CR)
    (hK : ‖Kγ‖ ≤ Cγ)
    (hRderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hRdot : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (hpderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => (((p τ : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
            Lp ℝ 2 μ)) (pdot t) t)
    (hpgraph : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ContinuousAt (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p τ)) t)
    (hAp : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p t)‖ ≤ CAp)
    (hPt : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖pdot t‖ ≤ CPt) :
    ∃ w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E,
      (∀ i t, 0 < t →
        ((((w i t : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
            Lp ℝ 2 μ)) =
          paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
            gamma10 R0star cutoff t) ∧
      (∀ i t, 0 ≤ t →
        ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (w i t)‖ ≤
          CA i * CH2 i) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        HasDerivAt
          (paperA10ActualSRNearPsi (u := u) μ regions hregions Kγ R
            gamma10 R0star cutoff
            (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p τ)))
          (paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
            gamma10 R0star cutoff V E hsep w
            (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p τ))
            pdot t) t ∧
        ‖paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
            gamma10 R0star cutoff V E hsep w
            (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p τ))
            pdot t‖ ≤
          ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
            ((‖cutoff‖ *
              (|1 / (gamma10 * R0star * μ.real (regions i))| *
                (Cγ * CR))) * CAp + (CA i * CH2 i) * CPt)) := by
  classical
  have hOne (i : Fin r) := paper_A7_actual_H2_gives_SR_near_moving_derivative
    μ (μU i) (embedU i) (localRestriction i)
    (regions i) (hregions i) Kγ R Rdot gamma10 R0star cutoff
    V E hsep hEsym p pdot (CH2 i) (CA i) (hCA i)
    (hRH2 i) (lift i) (hLiftRep i) (hLiftBound i)
  let w : Fin r → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E :=
    fun i => Classical.choose (hOne i)
  have hwRep (i : Fin r) (t : ℝ) (ht : 0 < t) :
      ((((w i t : ReservoirSeismicityControl.pressureWeakNeumannDomain V E) : V) :
          Lp ℝ 2 μ)) =
        paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
          gamma10 R0star cutoff t :=
    (Classical.choose_spec (hOne i)).1 t ht
  have hwBound (i : Fin r) (t : ℝ) (ht : 0 ≤ t) :
      ‖ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (w i t)‖ ≤
        CA i * CH2 i :=
    (Classical.choose_spec (hOne i)).2.1 t ht
  have hRateRegion (i : Fin r) : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖cutoff (paperSRDiffusionWeightRate μ (regions i) (hregions i)
            Kγ Rdot gamma10 R0star t)‖ ≤
        ‖cutoff‖ *
          (|1 / (gamma10 * R0star * μ.real (regions i))| * (Cγ * CR)) := by
    filter_upwards [hRdot] with t ht
    let P := ReservoirSeismicityControl.paperFarLpProjection μ (regions i) (hregions i)
    let c : ℝ := 1 / (gamma10 * R0star * μ.real (regions i))
    have hLocal : ‖P (Kγ (Rdot t))‖ ≤ Cγ * CR := by
      calc
        _ ≤ ‖Kγ (Rdot t)‖ :=
          ReservoirSeismicityControl.paper_far_lp_projection_norm_le μ (regions i)
            (hregions i) (Kγ (Rdot t))
        _ ≤ ‖Kγ‖ * ‖Rdot t‖ := Kγ.le_opNorm (Rdot t)
        _ ≤ Cγ * ‖Rdot t‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
        _ ≤ Cγ * CR := mul_le_mul_of_nonneg_left ht hCγ
    have hWeight : ‖c • P (Kγ (Rdot t))‖ ≤ |c| * (Cγ * CR) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hLocal (abs_nonneg _)
    change ‖cutoff (c • P (Kγ (Rdot t)))‖ ≤
      ‖cutoff‖ * (|c| * (Cγ * CR))
    exact (cutoff.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hWeight (norm_nonneg cutoff))
  have hRateAll : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ i : Fin r,
      ‖cutoff (paperSRDiffusionWeightRate μ (regions i) (hregions i)
            Kγ Rdot gamma10 R0star t)‖ ≤
        ‖cutoff‖ *
          (|1 / (gamma10 * R0star * μ.real (regions i))| * (Cγ * CR)) := by
    have hFinite (s : Finset (Fin r)) :
        ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
          ∀ i ∈ s,
          ‖cutoff (paperSRDiffusionWeightRate μ (regions i) (hregions i)
                Kγ Rdot gamma10 R0star t)‖ ≤
            ‖cutoff‖ *
              (|1 / (gamma10 * R0star * μ.real (regions i))| *
                (Cγ * CR)) := by
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with t
          simp
      | @insert i s hi ih =>
          filter_upwards [hRateRegion i, ih] with t hit hst j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · exact hit
          · exact hst j hjs
    filter_upwards [hFinite Finset.univ] with t ht i
    exact ht i (Finset.mem_univ i)
  refine ⟨w, hwRep, hwBound, ?_⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi, hRderiv, hpderiv,
      hpgraph, hAp, hPt, hRateAll]
    with t ht htR htP htGraph htAp htPt htRate
  let Ap : ℝ → Lp ℝ 2 μ :=
    fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (p τ)
  let v (i : Fin r) : Lp ℝ 2 μ :=
    cutoff (paperSRDiffusionWeightRate μ (regions i) (hregions i)
      Kγ Rdot gamma10 R0star t)
  let z (i : Fin r) : Lp ℝ 2 μ :=
    ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (w i t)
  let B (i : Fin r) : ℝ :=
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real (regions i))| *
      (Cγ * CR))
  let C (i : Fin r) : ℝ := B i * CAp + (CA i * CH2 i) * CPt
  have hScalar (i : Fin r) :
      HasDerivAt (fun τ : ℝ =>
          -⟪paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
            gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ)) t := by
    exact ((Classical.choose_spec (hOne i)).2.2 t ht htR htP htGraph).neg
  have hVector : HasDerivAt
      (paperA10ActualSRNearPsi (u := u) μ regions hregions Kγ R
        gamma10 R0star cutoff Ap)
      (paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
        gamma10 R0star cutoff V E hsep w Ap pdot t) t := by
    change HasDerivAt
      (fun τ : ℝ => ∑ i : Fin r,
        paperSRCoordinateEmbed (u := u) (r := r) i
          (-⟪paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
            gamma10 R0star cutoff τ, Ap τ⟫_ℝ))
      (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
        (-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ))) t
    apply HasDerivAt.fun_sum
    intro i _
    exact (paperSRCoordinateEmbed (u := u) (r := r) i).hasFDerivAt.comp_hasDerivAt
      t (hScalar i)
  have hBoundScalar (i : Fin r) :
      |-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ)| ≤ C i := by
    have hfirst : |⟪v i, Ap t⟫_ℝ| ≤ ‖v i‖ * ‖Ap t‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (v i) (Ap t))
    have hsecond : |⟪z i, pdot t⟫_ℝ| ≤ ‖z i‖ * ‖pdot t‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (z i) (pdot t))
    have hB : 0 ≤ B i := by
      dsimp [B]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _)
        (mul_nonneg hCγ hCR))
    have hC : 0 ≤ CA i * CH2 i := mul_nonneg (hCA i) (hCH2 i)
    have hFirstBound : |⟪v i, Ap t⟫_ℝ| ≤ B i * CAp := by
      calc
        _ ≤ ‖v i‖ * ‖Ap t‖ := hfirst
        _ ≤ B i * ‖Ap t‖ :=
          mul_le_mul_of_nonneg_right (htRate i) (norm_nonneg _)
        _ ≤ B i * CAp := mul_le_mul_of_nonneg_left htAp hB
    have hSecondBound : |⟪z i, pdot t⟫_ℝ| ≤
        (CA i * CH2 i) * CPt := by
      calc
        _ ≤ ‖z i‖ * ‖pdot t‖ := hsecond
        _ ≤ (CA i * CH2 i) * ‖pdot t‖ :=
          mul_le_mul_of_nonneg_right (hwBound i t ht.le) (norm_nonneg _)
        _ ≤ (CA i * CH2 i) * CPt :=
          mul_le_mul_of_nonneg_left htPt hC
    rw [abs_neg]
    exact (abs_add_le _ _).trans (add_le_add hFirstBound hSecondBound)
  have hVectorBound :
      ‖paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
          gamma10 R0star cutoff V E hsep w Ap pdot t‖ ≤
        ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * C i := by
    change ‖∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
        (-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ))‖ ≤ _
    calc
      _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i
        (-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
          |-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ)| := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using
          (paperSRCoordinateEmbed (u := u) (r := r) i).le_opNorm
            (-(⟪v i, Ap t⟫_ℝ + ⟪z i, pdot t⟫_ℝ))
      _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * C i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hBoundScalar i) (norm_nonneg _)
  exact ⟨hVector, hVectorBound⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_actual_SR_near_finite_from_A7
