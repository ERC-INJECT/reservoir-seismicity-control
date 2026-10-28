import ReservoirSeismicityControl.Paper2026.PhysicalA9UniformDGEnvelope
import ReservoirSeismicityControl.Paper2026.PhysicalA9AutomaticKernelMeasurability
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): from the *localized* DG estimate to the physical causal formula

This is the missing connection between two already verified results:
  * the uniform integrable DG majorant for centered smooth approximations;
  * the exact physical L² generator / causal Bochner integral identification.

The only PDE-specific far-field input is an integrable, localized
Davies--Gaffney/analytic-semigroup estimate, as cited in Appendix A.3.
The corresponding kernel's measurability and positive-lag convergence are
proved in the imported modules. No hypothesis on the time derivative of Q.

The quantitative bound `hApproxNorm` refers to the constructed approximants;
it is *not* a new assumption from the manuscript and must be discharged in
the final physical assembly. The external `hDGlocal` and `hAnalytic` likewise
must be instantiated for the Neumann realization before A9 is certified.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- Actual bounded-input multiwell *generator* causal identity using a
localized rather than a centered Davies--Gaffney bound. The smooth-source
Neumann constant cancels by the previous proof, and the published source
bound provides a single majorant independent of the approximation index. -/
theorem paper_A9_physical_generator_causal_from_local_DG
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
            (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)‖) :
    ∃ hp : (S t (p₀ : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
      let P := ReservoirSeismicityControl.paperFarLpProjection
        (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
      P (S.generator ⟨S t (p₀ : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν)) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩) =
        P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ), (q j s) • T s (f j) := by
  have hMeasureEq :
      (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)) =
      (volume : Measure ℝ).restrict (Set.Ico 0 (t : ℝ)) :=
    ((volume : Measure ℝ).restrict_congr_set
      (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := (t : ℝ)))).symm
  have hQ : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      |q j s| ≤ M j := by
    intro j
    rw [hMeasureEq]
    exact hBound j
  obtain ⟨b, hbInt, hOffDiag⟩ :=
    paper_A9_uniform_integrable_physical_DG_envelope
      Ω ν S far hfar m t φ cLp f hCore hConstant hConstantZero
      g hCentered hApproxNorm q M hM hQ K hKInt hKNonneg hDGlocal
  have hKernelMeas := paper_A9_kernel_measurable_from_integrable_Q
    (pressureNeumann3DRestrictedMeasure Ω ν) far hfar S t m g q hq
  have hPositiveLag (j : Fin m) :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
        Tendsto
          (fun n : ℕ => ReservoirSeismicityControl.paperFarLpProjection
            (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j))))
          atTop (𝓝 (T s (f j))) := by
    filter_upwards [hAnalytic] with s hA
    have hContinuous : Tendsto
        (fun n : ℕ => T s ((g n j : Lp ℝ 2
          (pressureNeumann3DRestrictedMeasure Ω ν))))
        atTop (𝓝 (T s (f j))) :=
      ((T s).continuous.tendsto (f j)).comp (hgLimit j)
    have hEq :
        (fun n : ℕ => ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))) =
        (fun n : ℕ => T s ((g n j : Lp ℝ 2
          (pressureNeumann3DRestrictedMeasure Ω ν)))) := by
      funext n
      exact hA (g n j)
    rw [hEq]
    exact hContinuous
  exact paper_A9_actual_L2_wells_projected_causal_of_offdiagonal
    (pressureNeumann3DRestrictedMeasure Ω ν) far hfar S hSelf hGraph
    t p₀ m f q hq M hM hBound g hgLimit
    (fun j s => T s (f j)) b hbInt hKernelMeas hOffDiag hPositiveLag

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_generator_causal_from_local_DG
