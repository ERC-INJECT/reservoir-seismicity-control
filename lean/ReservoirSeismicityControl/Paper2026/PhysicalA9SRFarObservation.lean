import ReservoirSeismicityControl.Paper2026.PhysicalA9DGToCausal
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.Tactic

/-!
# Appendix A.3: actual SR far observation / physical causal generator

Closes the observation-weight identification after the passed
`paper_A9_physical_generator_causal_from_local_DG` theorem.
The actual smooth far weight is `(1-ζ) χ_{V_R} γ₁ R / (γ₁₀R₀* |V_R|)`.
Its scalar pairing with the physical generator is exactly the pairing
with the DG-controlled causal integral. This is a VALUE formula, not yet
its time derivative (A9). No derivative of the bounded well flux is used.

The quoted analytic-semigroup, DG and local elliptic core inputs retain
precisely the status they had in the imported theorem; this code does not
claim to prove those standard external PDE theorems.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- The manuscript's actual moving SR far weight sees precisely the physical
far-projected generator causal integral. This is a direct specialization of
our compiled A9 generator theorem, using the smooth-cutoff support theorem.
The remaining A9 derivative needs the causal derivative of this expression. -/
theorem paper_A9_physical_SR_far_observation_from_local_DG
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u v : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν),
      (∀ w : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν),
        ∀ hw : w ∈ S.generatorDomain,
          ⟪u, S.generator ⟨w, hw⟩⟫_ℝ = ⟪v, w⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = v)
    (far : Set ↥(Ω : Set pressureNeumannE3))
    (hfar : MeasurableSet far)
    (m : ℕ) (t : NNReal) (p₀ : S.generatorDomain)
    (f cLp : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
    (g : ℕ → Fin m → S.generatorDomain)
    (hCore : ∀ j n,
      pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) ∈ S.generatorDomain)
    (hConstant : ∀ j, cLp j ∈ S.generatorDomain)
    (hConstantZero : ∀ j, S.generator ⟨cLp j, hConstant j⟩ = 0)
    (hCentered : ∀ n j,
      (g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) =
        pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j)
    (hApproxNorm : ∀ n j,
      ‖(g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) - f j‖ ≤
        1 / ((n : ℝ) + 1))
    (hgLimit : ∀ j : Fin m, Tendsto
      (fun n : ℕ => (g n j : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν))) atTop (𝓝 (f j)))
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q j s| ≤ M j)
    (T : ℝ → (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν) →L[ℝ]
      Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    -- Only a.e. *positive lag* smoothing is required. Requiring the
    -- identity at s=t would force a bounded extension of the unbounded
    -- generator at lag zero, which is NOT asserted by analytic theory.
    (hAnalytic : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      ∀ u : S.generatorDomain,
        ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
          T s (u : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (K : Fin m → ℝ → ℝ)
    (hKInt : ∀ j,
      Integrable (K j) (volume.restrict (Set.Ioc 0 (t : ℝ))))
    (hKNonneg : ∀ j,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))), 0 ≤ K j s)
    (hDGlocal : ∀ j n,
      ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        ‖ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
              (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n),
                hCore j n⟩))‖ ≤
          K j s * ‖pressureNeumann3DSmoothToL2CLM Ω
            (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)‖)
    (region : Set ↥(Ω : Set pressureNeumannE3))
    (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν) →L[ℝ]
      Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (R : ℝ → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν) →L[ℝ]
      Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (ζ : ↥(Ω : Set pressureNeumannE3) → ℝ)
    (hcutoff : ∀ τ : ℝ,
      ∀ᵐ x ∂(pressureNeumann3DRestrictedMeasure Ω ν),
        ((cutoff (paperSRDiffusionWeight
          (pressureNeumann3DRestrictedMeasure Ω ν)
          region hregion Kγ R gamma10 R0star τ)) x : ℝ) =
          ζ x * ((paperSRDiffusionWeight
            (pressureNeumann3DRestrictedMeasure Ω ν)
            region hregion Kγ R gamma10 R0star τ) x : ℝ))
    (hζfar : ∀ x : ↥(Ω : Set pressureNeumannE3), x ∉ far → ζ x = 1) :
    ∃ hp : (S t (p₀ : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
      let μ := pressureNeumann3DRestrictedMeasure Ω ν
      let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
      let w := paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff (t : ℝ)
      ⟪w, S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩⟫_ℝ =
      ⟪w, P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ), (q j s) • T s (f j)⟫_ℝ := by
  obtain ⟨hp, hCausal⟩ :=
    paper_A9_physical_generator_causal_from_local_DG
      Ω ν S hSelf hGraph far hfar m t p₀ f cLp φ g
      hCore hConstant hConstantZero hCentered hApproxNorm hgLimit
      q hq M hM hBound T hAnalytic K hKInt hKNonneg hDGlocal
  refine ⟨hp, ?_⟩
  let μ : Measure ↥(Ω : Set pressureNeumannE3) :=
    pressureNeumann3DRestrictedMeasure Ω ν
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let w : Lp ℝ 2 μ := paperSRFarDiffusionWeight μ region hregion
    Kγ R gamma10 R0star cutoff (t : ℝ)
  have hw : P w = w := by
    exact paper_sr_smooth_far_projection_fixed
      μ region hregion Kγ R gamma10 R0star cutoff
      ζ far hfar hcutoff hζfar (t : ℝ)
  have hPair :
      ⟪w, S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩⟫_ℝ =
      ⟪w, P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩)⟫_ℝ :=
    ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint μ far hfar)
      w _ hw
  change
      ⟪w, S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩⟫_ℝ =
      ⟪w, P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ), (q j s) • T s (f j)⟫_ℝ
  exact hPair.trans
    (congrArg (fun v : Lp ℝ 2 μ => ⟪w, v⟫_ℝ) hCausal)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_SR_far_observation_from_local_DG
