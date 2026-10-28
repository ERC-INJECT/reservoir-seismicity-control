import ReservoirSeismicityControl.Paper2026.PhysicalA9CanonicalCausalPath20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9W11DensityFromFTC20261025
import MarkovProcess.Semigroup.GeneratorClosed
import Mathlib.Tactic

/-!
# Physical A9: identify the actual L²-well kernel via closed analytic smoothing

The existing projected causal Duhamel theorem uses a bounded positive-lag
analytic semigroup extension. The previously proved W¹,¹ convolution theorem
uses a weak-Neumann orbit. This file identifies the two realizations for the
SAME initial L² well profile, rather than postulating kernel equality.

For generator-domain approximants `g n → f`, use:
  * the proved semigroup-generator commutation law;
  * the standard (external) positive-lag bounded analytic extension of
    `S lag ∘ generator` to the entire L² space;
  * the *proved* closedness of the generator;
  * the *proved* A5 canonical weak-Neumann/generator identification.

This does not differentiate well rates, assume the projected kernel identity,
or require an L² indicator well profile to belong to the generator domain.
The actual analytic positive-lag operator bound is a standard external
semigroup input, not a new axiom and not the conclusion of Appendix A9.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- Closed-generator smoothing: a bounded positive-lag extension of the
semigroup-generator orbit on D(A) supplies the generator orbit of a genuine
L² well profile, by graph closure, not by assuming domain membership. -/
theorem paper_A9_physical_L2_well_generator_from_closed_analytic_smoothing
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (lag : NNReal)
    (Tlag : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hAnalytic : ∀ u : S.generatorDomain,
      S lag (S.generator u) = Tlag (u : Lp ℝ 2 μ))
    (f : Lp ℝ 2 μ)
    (g : ℕ → S.generatorDomain)
    (hg : Tendsto (fun n : ℕ => (g n : Lp ℝ 2 μ)) atTop (𝓝 f)) :
    ∃ hS : S lag f ∈ S.generatorDomain,
      S.generator ⟨S lag f, hS⟩ = Tlag f := by
  let u : ℕ → S.generatorDomain :=
    fun n => ⟨S lag (g n : Lp ℝ 2 μ), S.operator_mem_generatorDomain (g n) lag⟩
  have hValue : Tendsto (fun n : ℕ => (u n : Lp ℝ 2 μ))
      atTop (𝓝 (S lag f)) := by
    change Tendsto (fun n : ℕ => S lag (g n : Lp ℝ 2 μ))
      atTop (𝓝 (S lag f))
    exact ((S lag).continuous.tendsto f).comp hg
  have hGen : Tendsto (fun n : ℕ => S.generator (u n))
      atTop (𝓝 (Tlag f)) := by
    have hEq : (fun n : ℕ => S.generator (u n)) =
        (fun n : ℕ => Tlag (g n : Lp ℝ 2 μ)) := by
      funext n
      exact (S.generator_operator (g n) lag).trans (hAnalytic (g n))
    rw [hEq]
    exact (Tlag.continuous.tendsto f).comp hg
  refine ⟨S.mem_generatorDomain_of_tendsto_generator hValue hGen, ?_⟩
  exact S.generator_eq_of_tendsto_generator hValue hGen

/-- The full analytic generator extension and the far-projected A9 analytic
extension agree on the actual L² source, by the same physical approximation.
This does NOT assume their equality at the physical well profile. -/
theorem paper_A9_full_and_far_analytic_extensions_agree_for_L2_well
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (lag : NNReal)
    (Tfull Tfar : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hFull : ∀ u : S.generatorDomain,
      S lag (S.generator u) = Tfull (u : Lp ℝ 2 μ))
    (hFar : ∀ u : S.generatorDomain,
      P (S lag (S.generator u)) = Tfar (u : Lp ℝ 2 μ))
    (f : Lp ℝ 2 μ) (g : ℕ → S.generatorDomain)
    (hg : Tendsto (fun n : ℕ => (g n : Lp ℝ 2 μ)) atTop (𝓝 f)) :
    P (Tfull f) = Tfar f := by
  have hEq (n : ℕ) : P (Tfull (g n : Lp ℝ 2 μ)) =
      Tfar (g n : Lp ℝ 2 μ) := by
    calc
      P (Tfull (g n : Lp ℝ 2 μ)) =
        P (S lag (S.generator (g n))) := by rw [hFull (g n)]
      _ = Tfar (g n : Lp ℝ 2 μ) := hFar (g n)
  have hP : Tendsto (fun n : ℕ => P (Tfull (g n : Lp ℝ 2 μ)))
      atTop (𝓝 (P (Tfull f))) := by
    exact ((P.comp Tfull).continuous.tendsto f).comp hg
  have hF : Tendsto (fun n : ℕ => Tfar (g n : Lp ℝ 2 μ))
      atTop (𝓝 (Tfar f)) := by
    exact (Tfar.continuous.tendsto f).comp hg
  have hFunctions :
      (fun n : ℕ => P (Tfull (g n : Lp ℝ 2 μ))) =
      (fun n : ℕ => Tfar (g n : Lp ℝ 2 μ)) := by
    funext n
    exact hEq n
  rw [hFunctions] at hP
  exact tendsto_nhds_unique hP hF

/-- A5 canonical weak-Neumann realization of the analytic smoothing orbit
of an actual L² well. No free identification between the two kernels:
its negative sign follows from the physically fixed convention A = -L. -/
theorem paper_A9_canonical_physical_L2_kernel_from_closed_smoothing
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (j : U →L[ℝ] Lp ℝ 2 μ)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    let S := ReservoirSeismicityControl.pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    let V : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range j.toLinearMap
    let Ew := ReservoirSeismicityControl.pressureA5CanonicalRangeEnergy j Eform hjinj
    let hsep := ReservoirSeismicityControl.pressure_A5_canonical_range_separates j hjinj hjDense
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    ∀ (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
      (g : ℕ → Fin m → S.generatorDomain)
      (hg : ∀ i : Fin m, Tendsto
        (fun n : ℕ => (g n i : Lp ℝ 2 μ)) atTop (𝓝 (f i)))
      (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hAnalytic : ∀ (lag : ℝ), 0 < lag → ∀ u : S.generatorDomain,
        S (Real.toNNReal lag) (S.generator u) = T lag (u : Lp ℝ 2 μ))
      (Tfar : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hFar : ∀ (lag : ℝ), 0 < lag → ∀ u : S.generatorDomain,
        P (S (Real.toNNReal lag) (S.generator u)) =
          Tfar lag (u : Lp ℝ 2 μ)),
      ∃ orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        ∀ (i : Fin m) (lag : ℝ), 0 < lag →
          (((orbit i lag : V) : Lp ℝ 2 μ)) =
            S (Real.toNNReal lag) (f i) ∧
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag)) =
            -(Tfar lag (f i)) := by
  classical
  intro S V Ew hsep P m f g hg T hAnalytic Tfar hFar
  have hExists (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      ∃ x : ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        (((x : V) : Lp ℝ 2 μ)) = S (Real.toNNReal lag) (f i) ∧
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep x) =
          -(Tfar lag (f i)) := by
    obtain ⟨hDom, hGen⟩ :=
      paper_A9_physical_L2_well_generator_from_closed_analytic_smoothing
        μ S (Real.toNNReal lag) (T lag) (hAnalytic lag hlag)
        (f i) (fun n => g n i) (hg i)
    obtain ⟨x, hx⟩ :=
      (ReservoirSeismicityControl.pressure_A5_canonical_range_domain_iff_generator_domain
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
        (S (Real.toNNReal lag) (f i))).mpr hDom
    have hxDom : (((x : V) : Lp ℝ 2 μ)) ∈ S.generatorDomain := by
      rw [hx]
      exact hDom
    have hweak :=
      ReservoirSeismicityControl.pressure_A5_canonical_range_operator_eq_neg_generator
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense x hxDom
    have hSame :
        (⟨(((x : V) : Lp ℝ 2 μ)), hxDom⟩ : S.generatorDomain) =
        (⟨S (Real.toNNReal lag) (f i), hDom⟩ : S.generatorDomain) :=
      Subtype.ext hx
    have hProjected : P (T lag (f i)) = Tfar lag (f i) :=
      paper_A9_full_and_far_analytic_extensions_agree_for_L2_well
        μ S P (Real.toNNReal lag) (T lag) (Tfar lag)
        (hAnalytic lag hlag) (hFar lag hlag)
        (f i) (fun n => g n i) (hg i)
    refine ⟨x, hx, ?_⟩
    calc
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep x) =
          P (-(S.generator ⟨(((x : V) : Lp ℝ 2 μ)), hxDom⟩)) := by
            exact congrArg P hweak
      _ = -(Tfar lag (f i)) := by
        rw [hSame, hGen, map_neg, hProjected]
  let orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew :=
    fun i lag => if h : 0 < lag then Classical.choose (hExists i lag h) else 0
  refine ⟨orbit, ?_⟩
  intro i lag hlag
  have hs := Classical.choose_spec (hExists i lag hlag)
  simpa only [orbit, dif_pos hlag] using hs

#print axioms paper_A9_physical_L2_well_generator_from_closed_analytic_smoothing
#print axioms paper_A9_full_and_far_analytic_extensions_agree_for_L2_well
#print axioms paper_A9_canonical_physical_L2_kernel_from_closed_smoothing

end ReservoirSeismicityControl.Paper2026
