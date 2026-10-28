import ReservoirSeismicityControl.Paper2026.PhysicalA9Canonical3DLocalDG20261025
import Mathlib.Tactic

/-!
# Physical A9: remove the zero-lag analytic-kernel premise

The canonical 3D A5/Duhamel pressure is still used unchanged.
The existing physical DG theorem needs an analytic-kernel identity a.e.
on source times s ∈ (0,t]. Since the endpoint s=t is null, the *proved*
strictly positive-lag kernel identity suffices.  This lemma removes
that independent a.e. applicability hypothesis, not a derivative.
No assumption on Q-dot is introduced.
-/
namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- Physical 3D causal pressure formula using only strict positive-lag
semigroup-kernel compatibility.  It requires no a.e. analytic-kernel
identity as an extra hypothesis and never evaluates the unbounded
generator on an unsmoothed source at lag zero. -/
theorem paper_A9_canonical_3d_causal_from_strictly_positive_kernel
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
      (Tfar : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hStrictLag : ∀ lag : ℝ, 0 < lag →
        ∀ u : S.generatorDomain,
          ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S (Real.toNNReal lag) (S.generator u)) =
              Tfar lag (u : Lp ℝ 2 μ))
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
                (q i s) • Tfar ((t : ℝ) - s) (f i))) := by
  classical
  intro μ S V Ew hsep far hfar T p₀ m f cLp q hq M hM hBound
    φ g hCore hConstant hConstantZero hCentered hApproxNorm hgLimit
    Tfar hStrictLag K hKInt hKNonneg hDGlocal
  have hAnalytic : ∀ t : NNReal, t ≤ T →
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        ∀ u : S.generatorDomain,
          ReservoirSeismicityControl.paperFarLpProjection μ far hfar
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
              Tfar ((t : ℝ) - s) (u : Lp ℝ 2 μ) := by
    intro t _ht
    have hne : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        s ≠ (t : ℝ) :=
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t : ℝ))).ae_ne (t : ℝ)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc, hne]
      with s hs hst
    intro u
    have hpositive : 0 < (t : ℝ) - s := by
      apply sub_pos.mpr
      exact lt_of_le_of_ne hs.2 hst
    exact hStrictLag ((t : ℝ) - s) hpositive u
  exact paper_A9_canonical_3d_pressure_causal_from_local_DG
    Ω ν j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    far hfar T p₀ m f cLp q hq M hM hBound
    φ g hCore hConstant hConstantZero hCentered hApproxNorm hgLimit
    (fun (t : NNReal) (s : ℝ) => Tfar ((t : ℝ) - s))
    hAnalytic K hKInt hKNonneg hDGlocal

#print axioms paper_A9_canonical_3d_causal_from_strictly_positive_kernel

end ReservoirSeismicityControl.Paper2026
