import ReservoirSeismicityControl.Paper2026.PhysicalA9CanonicalOrbitW11Convolution20261025
import Mathlib.Tactic

/-!
# A9: compatibility of the physical W¹,¹ orbit with the Neumann generator

The passing canonical W¹,¹ convolution theorem constructs an orbit, but
its returned certificate retained only the far-projected value. The four-term
A9 formula also needs the full operator compatibility. This module derives
that identity from the A5 generator graph and the already verified closed
analytic smoothing theorem. No new differentiability input is assumed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- For the SAME canonical weak-Neumann orbit and actual L² well profile,
the positive elliptic operator equals the negative bounded analytic
extension. This is not an external operator-compatibility assumption. -/
theorem paper_A9_canonical_well_operator_compatibility
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
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
    ∀ (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
      (g : ℕ → Fin m → S.generatorDomain)
      (hg : ∀ i : Fin m, Tendsto
        (fun n : ℕ => (g n i : Lp ℝ 2 μ)) atTop (𝓝 (f i)))
      (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hAnalytic : ∀ (lag : ℝ), 0 < lag → ∀ u : S.generatorDomain,
        S (Real.toNNReal lag) (S.generator u) = T lag (u : Lp ℝ 2 μ))
      (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew)
      (hValue : ∀ (i : Fin m) (lag : ℝ), 0 < lag →
        (((orbit i lag : V) : Lp ℝ 2 μ)) =
          S (Real.toNNReal lag) (f i)),
      ∀ (i : Fin m) (lag : ℝ), 0 < lag →
        ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag) =
          -(T lag (f i)) := by
  classical
  intro S V Ew hsep m f g hg T hAnalytic orbit hValue i lag hlag
  obtain ⟨hDom, hGen⟩ :=
    paper_A9_physical_L2_well_generator_from_closed_analytic_smoothing
      μ S (Real.toNNReal lag) (T lag) (hAnalytic lag hlag)
      (f i) (fun n => g n i) (hg i)
  have hc := hValue i lag hlag
  have hxDom : (((orbit i lag : V) : Lp ℝ 2 μ)) ∈
      S.generatorDomain := by
    rw [hc]
    exact hDom
  have hweak :=
    ReservoirSeismicityControl.pressure_A5_canonical_range_operator_eq_neg_generator
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      (orbit i lag) hxDom
  have hSame :
      (⟨(((orbit i lag : V) : Lp ℝ 2 μ)), hxDom⟩ : S.generatorDomain) =
      (⟨S (Real.toNNReal lag) (f i), hDom⟩ : S.generatorDomain) :=
    Subtype.ext hc
  calc
    ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag) =
        -(S.generator ⟨(((orbit i lag : V) : Lp ℝ 2 μ)), hxDom⟩) := hweak
    _ = -(T lag (f i)) := by rw [hSame, hGen]

theorem paper_A9_canonical_W11_convolution_with_operator_compatibility
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
          Tfar lag (u : Lp ℝ 2 μ))
      (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
        S (Real.toNNReal s) x ∈ S.generatorDomain)
      (B₀ B₂ : Fin m → ℝ → ℝ)
      (hB₀ : ∀ i lag, 0 < lag → 0 ≤ B₀ i lag)
      (hB₂ : ∀ i lag, 0 < lag → 0 ≤ B₂ i lag)
      (hDG₀ : ∀ (i : Fin m) (lag : ℝ), 0 < lag →
        ‖Tfar lag (f i)‖ ≤ B₀ i lag)
      (hDG₂ : ∀ (i : Fin m) (lag : ℝ), 0 < lag →
        ‖P (paperA9CanonicalSmoothedSecond μ S hSmooth (f i) lag)‖
          ≤ B₂ i lag)
      (hB₀Int : ∀ i : Fin m,
        Integrable (B₀ i) (volume.restrict (Set.Ioi (0 : ℝ))))
      (hB₂Int : ∀ i : Fin m,
        Integrable (B₂ i) (volume.restrict (Set.Ioi (0 : ℝ))))
      (hB₀Zero : ∀ i : Fin m,
        Tendsto (B₀ i) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
      (hFarMeas : ∀ i : Fin m,
        AEStronglyMeasurable (fun lag : ℝ => Tfar lag (f i))
          (volume.restrict (Set.Ioi (0 : ℝ))))
      (hSecondMeas : ∀ i : Fin m,
        AEStronglyMeasurable
          (fun lag : ℝ => P (paperA9CanonicalSmoothedSecond
            μ S hSmooth (f i) lag))
          (volume.restrict (Set.Ioi (0 : ℝ))))
      (qext : Fin m → ℝ → ℝ)
      (hqLoc : ∀ i : Fin m, LocallyIntegrable (qext i) volume)
      (hqMeas : ∀ i : Fin m,
        AEStronglyMeasurable (qext i) (volume : Measure ℝ))
      (M : Fin m → ℝ)
      (hqBound : ∀ (i : Fin m) (s : ℝ), |qext i s| ≤ M i)
      (hDensity : PaperA9BanachW11Density μ),
    ∃ orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
      (∀ (i : Fin m) (lag : ℝ), 0 < lag →
        (((orbit i lag : V) : Lp ℝ 2 μ)) =
          S (Real.toNNReal lag) (f i) ∧
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag)) =
          -(Tfar lag (f i))) ∧
      (∀ (i : Fin m) (lag : ℝ), 0 < lag →
        ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag) =
          -(T lag (f i))) ∧
      (∀ t : ℝ,
        let second : Fin m → ℝ → Lp ℝ 2 μ := fun i lag =>
          paperA9CanonicalSmoothedSecond μ S hSmooth (f i) lag
        let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun i lag =>
          if 0 < lag then
            P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep
              (orbit i lag)) else 0
        let rate : Fin m → ℝ → Lp ℝ 2 μ := fun i lag =>
          if 0 < lag then -(P (second i lag)) else 0
        HasDerivAt
          (fun τ : ℝ => ∑ i : Fin m,
            ∫ s : ℝ, qext i s • kernel i (τ - s))
          (∑ i : Fin m,
            ∫ s : ℝ, qext i s • rate i (t - s)) t) := by
  classical
  intro S V Ew hsep P m f g hg T hAnalytic Tfar hFar hSmooth
    B₀ B₂ hB₀ hB₂ hDG₀ hDG₂ hB₀Int hB₂Int hB₀Zero
    hFarMeas hSecondMeas qext hqLoc hqMeas M hqBound hDensity
  obtain ⟨orbit, hValue, hConvolution⟩ :=
    paper_A9_canonical_L2_wells_W11_convolution_from_smoothing
      μ far hfar j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      m f g hg T hAnalytic Tfar hFar hSmooth
      B₀ B₂ hB₀ hB₂ hDG₀ hDG₂ hB₀Int hB₂Int hB₀Zero
      hFarMeas hSecondMeas qext hqLoc hqMeas M hqBound hDensity
  have hFullValue (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      (((orbit i lag : V) : Lp ℝ 2 μ)) =
        S (Real.toNNReal lag) (f i) := (hValue i lag hlag).1
  have hCompat :=
    paper_A9_canonical_well_operator_compatibility
      μ j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      m f g hg T hAnalytic orbit hFullValue
  exact ⟨orbit, hValue, hCompat, hConvolution⟩

#print axioms paper_A9_canonical_well_operator_compatibility
#print axioms paper_A9_canonical_W11_convolution_with_operator_compatibility

end ReservoirSeismicityControl.Paper2026
