import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualSignedDimensionalH2_20261027
import ReservoirSeismicityControl.Paper2026.PhysicalA10ActualSRNearFinite20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA10CanonicalGeneratorDomain20261027
import Mathlib.Tactic

/-!
# A7–A10: actual local H² certificates, Green cutoff lift and moving near field

The physical Neumann generator and its weak representation are already verified.
The signed actual SR local H² theorem is already verified for d = 1,2,3.
This file joins them WITHOUT assuming a `lift`, `hLiftRep`, or `hLiftBound`.

What is external and NOT claimed proved here:
* the standard compact-interior H² cutoff/multiplier construction `W`;
* local support/multiplier identity `hWRep` (Kgamma cannot be an arbitrary
  nonlocal L² operator if a lift depending only on R|U is to exist);
* its ordinary weak Green identity `hGreen`, and the quantitative
  distributional product estimate expressed by an L² map `F` and `hFNorm`.

Given those specific standard elliptic-calculus results, the weak Neumann
operator-domain membership and graph estimate are constructed/proved, and
those results are passed to the existing finite A10 SR near-field theorem.
This is a physical near-field assembly, NOT YET the full A10 reaction/far/STA
terminal theorem. No new Lean axioms and no restated output derivative input.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- A single genuine H² carrier for all finitely many local physical SR sets. -/
abbrev A7A10LocalH2Family (n_d r : ℕ)
    (U : Fin r → Set (PaperSpatial n_d)) :=
  (i : Fin r) → A7DimensionalH2 n_d (U i)

/-- Coordinate restriction of the finite local H² carrier to its i-th L². -/
noncomputable def a7A10LocalH2Embed
    {n_d r : ℕ} (U : Fin r → Set (PaperSpatial n_d)) (i : Fin r) :
    A7A10LocalH2Family n_d r U →L[ℝ]
      Lp ℝ 2 (volume.restrict (U i)) :=
  (a7DimensionalH2Embedding n_d (U i)).comp (ContinuousLinearMap.proj i)

/-- Use the already-derived A7 certificates, *without adding H² regularity*
for the physical solution, to construct a single local-family representative. -/
theorem a7_a10_actual_finite_local_certificates
    {n_d r : ℕ} (U : Fin r → Set (PaperSpatial n_d))
    (μ : Measure (PaperSpatial n_d)) (R : ℝ → Lp ℝ 2 μ)
    (localRestriction : (i : Fin r) →
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict (U i)))
    (Rlocal : (i : Fin r) → ℝ → Lp ℝ 2 (volume.restrict (U i)))
    (hLocalR : ∀ i t, 0 ≤ t → localRestriction i (R t) = Rlocal i t)
    (M : Fin r → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hA7 : ∀ i t, 0 ≤ t →
      ∃ y : A7DimensionalH2 n_d (U i),
        a7DimensionalH2Embedding n_d (U i) y = Rlocal i t ∧
        ‖y‖ ≤ M i) :
    ∀ t, 0 ≤ t → ∃ y : A7A10LocalH2Family n_d r U,
      (∀ i, a7A10LocalH2Embed U i y = localRestriction i (R t)) ∧
      ‖y‖ ≤ ∑ i : Fin r, M i := by
  classical
  intro t ht
  let y : A7A10LocalH2Family n_d r U := fun i =>
    Classical.choose (hA7 i t ht)
  have hRep (i : Fin r) :
      a7A10LocalH2Embed U i y = localRestriction i (R t) := by
    have hi := (Classical.choose_spec (hA7 i t ht)).1
    change a7DimensionalH2Embedding n_d (U i) (y i) =
      localRestriction i (R t)
    exact hi.trans (hLocalR i t ht).symm
  have hNonneg : 0 ≤ ∑ i : Fin r, M i :=
    Finset.sum_nonneg (fun i _ => hM i)
  have hNorm : ‖y‖ ≤ ∑ i : Fin r, M i := by
    apply (pi_norm_le_iff_of_nonneg hNonneg).2
    intro i
    calc
      ‖y i‖ ≤ M i := (Classical.choose_spec (hA7 i t ht)).2
      _ ≤ ∑ j : Fin r, M j :=
        Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  exact ⟨y, hRep, hNorm⟩

/-- The actual physical cutoff lift: standard H² calculus supplies its
value `W y` and the L² distributional operator `F y`. The previously
verified *definition* of the weak Neumann domain then supplies the entire
operator-domain inclusion. No domain membership is assumed for `W y`. -/
noncomputable def a7_a10_green_cutoff_lift
    {n_d r : ℕ} (U : Fin r → Set (PaperSpatial n_d))
    (μ : Measure (PaperSpatial n_d))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (W F : (i : Fin r) → A7DimensionalH2 n_d (U i) →L[ℝ]
      Lp ℝ 2 μ)
    (hWMem : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i)),
      W i y ∈ V)
    (hGreen : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i))
      (v : V), E ⟨W i y, hWMem i y⟩ v = ⟪F i y, (v : Lp ℝ 2 μ)⟫_ℝ)
    (i : Fin r) (y : A7DimensionalH2 n_d (U i)) :
    pressureWeakNeumannDomain V E :=
  ⟨⟨W i y, hWMem i y⟩, ⟨F i y, hGreen i y⟩⟩

/-- The operator of the cutoff lift is exactly the L² product-rule
candidate `F y`, not merely bounded by a chosen abstract generator. -/
theorem a7_a10_green_cutoff_operator_eq
    {n_d r : ℕ} (U : Fin r → Set (PaperSpatial n_d))
    (μ : Measure (PaperSpatial n_d))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (W F : (i : Fin r) → A7DimensionalH2 n_d (U i) →L[ℝ]
      Lp ℝ 2 μ)
    (hWMem : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i)),
      W i y ∈ V)
    (hGreen : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i))
      (v : V), E ⟨W i y, hWMem i y⟩ v = ⟪F i y, (v : Lp ℝ 2 μ)⟫_ℝ)
    (i : Fin r) (y : A7DimensionalH2 n_d (U i)) :
    pressureWeakNeumannOperator V E hsep
      (a7_a10_green_cutoff_lift U μ V E W F hWMem hGreen i y) = F i y := by
  exact pressure_weak_neumann_representer_unique V E hsep
    (a7_a10_green_cutoff_lift U μ V E W F hWMem hGreen i y)
    (F i y) (hGreen i y)

/-- No `hLiftBound`: the graph estimate follows from the ordinary
L² product-rule operator bound and uniqueness of the weak representer. -/
theorem a7_a10_green_cutoff_graph_bound
    {n_d r : ℕ} (U : Fin r → Set (PaperSpatial n_d))
    (μ : Measure (PaperSpatial n_d))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (W F : (i : Fin r) → A7DimensionalH2 n_d (U i) →L[ℝ]
      Lp ℝ 2 μ)
    (hWMem : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i)),
      W i y ∈ V)
    (hGreen : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i))
      (v : V), E ⟨W i y, hWMem i y⟩ v = ⟪F i y, (v : Lp ℝ 2 μ)⟫_ℝ)
    (CA : Fin r → ℝ)
    (hFNorm : ∀ i, ‖F i‖ ≤ CA i)
    (i : Fin r) (y : A7DimensionalH2 n_d (U i)) :
    ‖pressureWeakNeumannOperator V E hsep
        (a7_a10_green_cutoff_lift U μ V E W F hWMem hGreen i y)‖ ≤
      CA i * ‖y‖ := by
  rw [a7_a10_green_cutoff_operator_eq U μ V E hsep W F hWMem hGreen i y]
  calc
    ‖F i y‖ ≤ ‖F i‖ * ‖y‖ := (F i).le_opNorm y
    _ ≤ CA i * ‖y‖ :=
      mul_le_mul_of_nonneg_right (hFNorm i) (norm_nonneg _)

/-- A7 and the local Green/product-rule theorem imply the full finite-SR
moving near-field derivative, with no independent lift or output-derivative
hypothesis. This is the already passed A10 finite-near theorem instantiated
with a genuine finite family of physical local H² graphs. -/
theorem a7_a10_actual_signed_SR_near_from_green_cutoff
    {n_d u r : ℕ} (hd : PaperSpatialDimension n_d)
    (U : Fin r → Set (PaperSpatial n_d))
    (μ : Measure (PaperSpatial n_d))
    (localRestriction : (i : Fin r) →
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict (U i)))
    (Rlocal : (i : Fin r) → ℝ → Lp ℝ 2 (volume.restrict (U i)))
    (regions : Fin r → Set (PaperSpatial n_d))
    (hregions : ∀ i, MeasurableSet (regions i))
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ a b : V, E a b = E b a)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (pdot : ℝ → Lp ℝ 2 μ)
    (M CA : Fin r → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hCA : ∀ i, 0 ≤ CA i)
    (hLocalR : ∀ i t, 0 ≤ t → localRestriction i (R t) = Rlocal i t)
    (hA7 : ∀ i t, 0 ≤ t →
      ∃ y : A7DimensionalH2 n_d (U i),
        a7DimensionalH2Embedding n_d (U i) y = Rlocal i t ∧
        ‖y‖ ≤ M i)
    /- The physical local product-and-cutoff mapping in ordinary L². -/
    (W F : (i : Fin r) → A7DimensionalH2 n_d (U i) →L[ℝ]
      Lp ℝ 2 μ)
    (hWMem : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i)),
      W i y ∈ V)
    (hGreen : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i))
      (v : V), E ⟨W i y, hWMem i y⟩ v = ⟪F i y, (v : Lp ℝ 2 μ)⟫_ℝ)
    (hFNorm : ∀ i, ‖F i‖ ≤ CA i)
    /- Physical locality is indispensable. For nonlocal arbitrary Kγ the
       next equality is false even if R|U is H². -/
    (hWRep : ∀ (i : Fin r) (y : A7DimensionalH2 n_d (U i))
      (rr : Lp ℝ 2 μ),
      a7DimensionalH2Embedding n_d (U i) y = localRestriction i rr →
      W i y = cutoff
        ((1 / (gamma10 * R0star * μ.real (regions i)) : ℝ) •
          ReservoirSeismicityControl.paperFarLpProjection μ (regions i) (hregions i)
            (Kγ rr)))
    (Cγ CR CAp CPt : ℝ)
    (hCγ : 0 ≤ Cγ) (hCR : 0 ≤ CR)
    (hK : ‖Kγ‖ ≤ Cγ)
    (hRderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hRdot : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (hpderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ : ℝ => (((p τ : pressureWeakNeumannDomain V E) : V) :
          Lp ℝ 2 μ)) (pdot t) t)
    (hpgraph : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ContinuousAt (fun τ => pressureWeakNeumannOperator V E hsep (p τ)) t)
    (hAp : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖pressureWeakNeumannOperator V E hsep (p t)‖ ≤ CAp)
    (hPt : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖pdot t‖ ≤ CPt) :
    let CH2 := ∑ i : Fin r, M i
    ∃ w : Fin r → ℝ → pressureWeakNeumannDomain V E,
      (∀ i t, 0 < t →
        ((((w i t : pressureWeakNeumannDomain V E) : V) :
            Lp ℝ 2 μ)) =
          paperSRNearDiffusionWeight μ (regions i) (hregions i) Kγ R
            gamma10 R0star cutoff t) ∧
      (∀ i t, 0 ≤ t →
        ‖pressureWeakNeumannOperator V E hsep (w i t)‖ ≤
          CA i * CH2) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        HasDerivAt
          (paperA10ActualSRNearPsi (u := u) μ regions hregions Kγ R
            gamma10 R0star cutoff
            (fun τ => pressureWeakNeumannOperator V E hsep (p τ)))
          (paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
            gamma10 R0star cutoff V E hsep w
            (fun τ => pressureWeakNeumannOperator V E hsep (p τ))
            pdot t) t ∧
        ‖paperA10ActualSRNearRate (u := u) μ regions hregions Kγ Rdot
            gamma10 R0star cutoff V E hsep w
            (fun τ => pressureWeakNeumannOperator V E hsep (p τ))
            pdot t‖ ≤
          ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
            ((‖cutoff‖ *
              (|1 / (gamma10 * R0star * μ.real (regions i))| *
                (Cγ * CR))) * CAp + (CA i * CH2) * CPt)) := by
  classical
  let CH2 := ∑ i : Fin r, M i
  let lift : (i : Fin r) → A7A10LocalH2Family n_d r U →
      pressureWeakNeumannDomain V E := fun i y =>
    a7_a10_green_cutoff_lift U μ V E W F hWMem hGreen i (y i)
  have hRH2 : ∀ i τ, 0 ≤ τ →
      ∃ y : A7A10LocalH2Family n_d r U,
        a7A10LocalH2Embed U i y = localRestriction i (R τ) ∧
        ‖y‖ ≤ CH2 := by
    intro i τ ht
    obtain ⟨y, hy, hb⟩ :=
      a7_a10_actual_finite_local_certificates U μ R localRestriction
        Rlocal hLocalR M hM hA7 τ ht
    exact ⟨y, hy i, hb⟩
  have hLiftRep : ∀ (i : Fin r) (y : A7A10LocalH2Family n_d r U)
      (rr : Lp ℝ 2 μ),
      a7A10LocalH2Embed U i y = localRestriction i rr →
        ((((lift i y : pressureWeakNeumannDomain V E) : V) :
          Lp ℝ 2 μ)) =
          cutoff ((1 / (gamma10 * R0star * μ.real (regions i)) : ℝ) •
            ReservoirSeismicityControl.paperFarLpProjection μ (regions i) (hregions i)
              (Kγ rr)) := by
    intro i y rr hy
    change W i (y i) = _
    apply hWRep i (y i) rr
    change a7DimensionalH2Embedding n_d (U i) (y i) =
      localRestriction i rr at hy
    exact hy
  have hLiftBound : ∀ i (y : A7A10LocalH2Family n_d r U),
      ‖pressureWeakNeumannOperator V E hsep (lift i y)‖ ≤
        CA i * ‖y‖ := by
    intro i y
    calc
      ‖pressureWeakNeumannOperator V E hsep (lift i y)‖ ≤
          CA i * ‖y i‖ :=
        a7_a10_green_cutoff_graph_bound U μ V E hsep W F hWMem
          hGreen CA hFNorm i (y i)
      _ ≤ CA i * ‖y‖ :=
        mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (hCA i)
  have hCH2 : ∀ i : Fin r, 0 ≤ CH2 := by
    intro i
    exact Finset.sum_nonneg (fun j _ => hM j)
  exact paper_A10_actual_SR_near_finite_from_A7
    μ (fun i => volume.restrict (U i))
    (fun i => a7A10LocalH2Embed U i)
    localRestriction regions hregions Kγ R Rdot gamma10 R0star cutoff
    V E hsep hEsym p pdot (fun _ => CH2) CA hCA hCH2 hRH2
    lift hLiftRep hLiftBound Cγ CR CAp CPt
    hCγ hCR hK hRderiv hRdot hpderiv hpgraph hAp hPt

#print axioms a7_a10_green_cutoff_operator_eq
#print axioms a7_a10_green_cutoff_graph_bound
#print axioms a7_a10_actual_signed_SR_near_from_green_cutoff

end ReservoirSeismicityControl.Paper2026
