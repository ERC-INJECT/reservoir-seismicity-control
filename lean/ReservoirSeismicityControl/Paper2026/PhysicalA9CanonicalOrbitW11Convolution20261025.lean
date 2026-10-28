import ReservoirSeismicityControl.Paper2026.PhysicalA9SmoothedGeneratorRate20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9W11DensityFromFTC20261025
import Mathlib.Tactic

/-!
# Appendix A.3: canonical L²-well Neumann orbit to W¹,¹ convolution

This module uses the PASSED closed analytic-kernel and smoothed-generator
results to construct, rather than hypothesize, the physical weak-Neumann
orbit, its positive-lag derivative and its associated second-order kernel.

The externally cited estimates remaining in this application are explicitly
norm bounds on the analytic far semigroup and its second-order derivative,
plus their lag measurability and integrable off-diagonal envelopes.  The
universal Banach-valued W¹,¹ density result is also explicit.  Neither an
orbit derivative, a kernel W¹,¹ statement, nor a forcing derivative is a
hypothesis.  There is no derivative assumption on Q.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- The ACTUAL second-order semigroup kernel at positive lag.  This is
constructed by two steps of generator-domain smoothing, using the same
one-third splitting as the PASSED physical-generator orbit-rate theorem.
The arbitrary zero-lag definition is harmless for the causal extension. -/
noncomputable def paperA9CanonicalSmoothedSecond
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (f : Lp ℝ 2 μ) (lag : ℝ) : Lp ℝ 2 μ :=
  if hlag : 0 < lag then
    let a : ℝ := lag / 3
    let u : S.generatorDomain :=
      ⟨S (Real.toNNReal a) f,
        hSmooth f a (by dsimp [a]; linarith)⟩
    let v : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (S.generator u),
        hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
    S (Real.toNNReal (lag - 2 * a)) (S.generator v)
  else 0

/-- The canonical-orbit specialization of the physical vector convolution
rate. The off-diagonal norm assumptions refer to the ACTUAL bounded
analytic far operator and the concrete second-order semigroup expression.
Their positive-lag envelopes are the standard cited Davies--Gaffney and
spectral-gap analytic bounds; no differentiability of the output is assumed.

The conclusion returns an orbit with the correct physical value AND its
forcing-convolution derivative, so the latter is not a free A9 premise. -/
theorem paper_A9_canonical_L2_wells_W11_convolution_from_smoothing
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
  obtain ⟨orbit, hValue, hFullRate, _hProjectedRate⟩ :=
    paper_A9_canonical_L2_well_projected_lag_rate_from_smoothing
      μ far hfar j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      m f g hg T hAnalytic Tfar hFar hSmooth
  let second : Fin m → ℝ → Lp ℝ 2 μ := fun i lag =>
    paperA9CanonicalSmoothedSecond μ S hSmooth (f i) lag
  have hOrbit (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      HasDerivAt
        (fun τ => ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i τ))
        (-(second i lag)) lag := by
    simpa only [second, paperA9CanonicalSmoothedSecond, dif_pos hlag]
      using hFullRate i lag hlag
  have hDGOrbit (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      ‖P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag))‖
        ≤ B₀ i lag := by
    calc
      ‖P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag))‖ =
          ‖-(Tfar lag (f i))‖ := by rw [(hValue i lag hlag).2]
      _ = ‖Tfar lag (f i)‖ := norm_neg _
      _ ≤ B₀ i lag := hDG₀ i lag hlag
  have hDGSecond (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      ‖P (second i lag)‖ ≤ B₂ i lag := hDG₂ i lag hlag
  have hOrbitMeas (i : Fin m) :
      AEStronglyMeasurable
        (fun lag => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep
          (orbit i lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hEq :
        (fun lag => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep
          (orbit i lag))) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun lag => -(Tfar lag (f i))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with lag hlag
      exact (hValue i lag hlag).2
    exact ((hFarMeas i).neg).congr hEq.symm
  have hRateMeas (i : Fin m) :
      AEStronglyMeasurable (fun lag => P (second i lag))
        (volume.restrict (Set.Ioi (0 : ℝ))) := hSecondMeas i
  refine ⟨orbit, hValue, ?_⟩
  intro t
  exact paper_A9_physical_projected_convolution_rate_from_DG_and_density
    μ far hfar V Ew hsep orbit second hOrbit
    B₀ B₂ hB₀ hB₂ hDGOrbit hDGSecond hB₀Int hB₂Int hB₀Zero
    hOrbitMeas hRateMeas qext hqLoc hqMeas M hqBound hDensity t

#print axioms paper_A9_canonical_L2_wells_W11_convolution_from_smoothing

end ReservoirSeismicityControl.Paper2026
