import ReservoirSeismicityControl.Paper2026.PhysicalA9CanonicalGeneratorProjection
import ReservoirSeismicityControl.Paper2026.PhysicalA9DGToCausal
import Mathlib.Tactic

/-!
# Appendix A.3: canonical physical 3D pressure and genuine positive-lag DG

This is an application of TWO existing results: A5 constructs the physical
Duhamel pressure in the canonical weak-Neumann domain; the physical localized
DG theorem identifies its generator via an a.e. causal integral. In contrast
with the earlier abstract kernel theorem, analytic smoothing is required only
almost everywhere in the source-time interval. In particular there is NO
bounded-generator-at-zero-lag assumption. No bounded Q-dot is used.

This file does NOT imply the manuscript's 1D/2D cases, nor does it by itself
supply the moving SR observation's derivative.
-/
namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- The actual A5 Duhamel pressure field has the A9 generator causal value
under physical 3D DG/source regularity. Unlike the previously used abstract
causal specialization, the smoothing identity is required only a.e. at
strictly positive semigroup lag; the source-time endpoint is not a premise. -/
theorem paper_A9_canonical_3d_pressure_causal_from_local_DG
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (j : U →L[ℝ] Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    let μ := pressureNeumann3DRestrictedMeasure Ω ν
    let S := ReservoirSeismicityControl.pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    let V : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range j.toLinearMap
    let Ew := ReservoirSeismicityControl.pressureA5CanonicalRangeEnergy j Eform hjinj
    let hsep := ReservoirSeismicityControl.pressure_A5_canonical_range_separates j hjinj hjDense
    ∀ (far : Set ↥(Ω : Set pressureNeumannE3))
      (hfar : MeasurableSet far)
      (T : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f cLp : Fin m → Lp ℝ 2 μ)
      (q : Fin m → ℝ → ℝ)
      (hq : ∀ i : Fin m, Integrable (q i)
        (volume.restrict (Set.Ico 0 (T : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
      (hBound : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i)
      (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
      (g : ℕ → Fin m → S.generatorDomain)
      (hCore : ∀ i n,
        pressureNeumann3DSmoothToL2CLM Ω μ ℝ (φ i n) ∈ S.generatorDomain)
      (hConstant : ∀ i, cLp i ∈ S.generatorDomain)
      (hConstantZero : ∀ i,
        S.generator ⟨cLp i, hConstant i⟩ = 0)
      (hCentered : ∀ n i, (g n i : Lp ℝ 2 μ) =
        pressureNeumann3DSmoothToL2CLM Ω μ ℝ (φ i n) - cLp i)
      (hApproxNorm : ∀ n i,
        ‖(g n i : Lp ℝ 2 μ) - f i‖ ≤ 1 / ((n : ℝ) + 1))
      (hgLimit : ∀ i : Fin m, Tendsto
        (fun n : ℕ => (g n i : Lp ℝ 2 μ)) atTop (𝓝 (f i)))
      (Tker : NNReal → ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hAnalytic : ∀ t : NNReal, t ≤ T →
        ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        ∀ u : S.generatorDomain,
          ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
              Tker t s (u : Lp ℝ 2 μ))
      (K : NNReal → Fin m → ℝ → ℝ)
      (hKInt : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        Integrable (K t i) (volume.restrict (Set.Ioc 0 (t : ℝ))))
      (hKNonneg : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))), 0 ≤ K t i s)
      (hDGlocal : ∀ t : NNReal, t ≤ T → ∀ i : Fin m, ∀ n : ℕ,
        ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
          ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S (Real.toNNReal ((t : ℝ) - s))
              (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω μ ℝ (φ i n),
                hCore i n⟩))‖ ≤
            K t i s * ‖pressureNeumann3DSmoothToL2CLM Ω μ ℝ (φ i n)‖),
      ∃ p : ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        (∀ τ : ℝ, (((p τ : V) : Lp ℝ 2 μ)) =
          S (ReservoirSeismicityControl.pressureA5HorizonClip T τ) (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S
            (ReservoirSeismicityControl.pressureA5HorizonClip T τ) m f q) ∧
        Continuous (fun τ : ℝ =>
          ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p τ)) ∧
        (∀ t : NNReal, t ≤ T →
          ReservoirSeismicityControl.paperFarLpProjection μ far hfar
              (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
            -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar (S t (S.generator p₀)) +
              ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
                (q i s) • Tker t s (f i))) := by
  classical
  intro μ S V Ew hsep far hfar T p₀ m f cLp q hq M hM hBound
    φ g hCore hConstant hConstantZero hCentered hApproxNorm hgLimit
    Tker hAnalytic K hKInt hKNonneg hDGlocal
  obtain ⟨hSelf, hGraph⟩ :=
    ReservoirSeismicityControl.pressure_dense_neumann_semigroup_selfadjoint_and_graph
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
  obtain ⟨p, hpCarrier, hpContinuous, hpPhysical⟩ :=
    paper_A9_physical_mild_projected_generator_identification
      μ far hfar j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      T p₀ m f q hq M hM hBound
  refine ⟨p, hpCarrier, hpContinuous, ?_⟩
  intro t ht
  have hqt : ∀ i : Fin m,
      Integrable (q i) (volume.restrict (Set.Ico 0 (t : ℝ))) := by
    intro i
    have hsub : Set.Ico (0 : ℝ) (t : ℝ) ⊆
        Set.Ico (0 : ℝ) (T : ℝ) := by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 (NNReal.coe_le_coe.mpr ht)⟩
    exact IntegrableOn.mono_set (hq i) hsub
  obtain ⟨hpDG, hDG⟩ :=
    paper_A9_physical_generator_causal_from_local_DG
      Ω ν S hSelf hGraph far hfar m t p₀ f cLp φ g
      hCore hConstant hConstantZero hCentered hApproxNorm hgLimit
      q hqt M hM (hBound t ht) (Tker t) (hAnalytic t ht)
      (K t) (hKInt t ht) (hKNonneg t ht) (hDGlocal t ht)
  obtain ⟨hpCan, hPhysicalValue⟩ := hpPhysical t ht
  have hSame :
      (⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpCan⟩ :
            S.generatorDomain) =
      (⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpDG⟩ :
            S.generatorDomain) := Subtype.ext rfl
  dsimp only at hDG
  calc
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
          -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
              ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpCan⟩)) := by
                simpa only [map_neg] using hPhysicalValue
    _ = -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
              ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpDG⟩)) := by
          rw [hSame]
    _ = -(ReservoirSeismicityControl.paperFarLpProjection μ far hfar (S t (S.generator p₀)) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (q i s) • Tker t s (f i)) := by
          rw [hDG]

#print axioms paper_A9_canonical_3d_pressure_causal_from_local_DG

end ReservoirSeismicityControl.Paper2026
