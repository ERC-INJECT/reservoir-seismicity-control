import ReservoirSeismicityControl.Paper2026.PhysicalA9LocalizedGeneratorL2Limit
import ReservoirSeismicityControl.Paper2026.PhysicalA9ChosenLocalApproximation

/-!
# A9: physical multiwell localized generator approximation and causal limit

This combines TWO ALREADY ESTABLISHED results:
* the physical 3D construction of centered, near-supported D(A) approximants
  converging in the actual reservoir L² space;
* the A5 stability theorem and smooth-well generator-to-causal identity.

The construction is performed simultaneously for a FINITE FAMILY OF WELLS.
It produces one common sequence for the smooth physical causal generator
formulas and proves its limit is the far projection of the generator of the
actual L²-forced mild pressure state.

The standard elliptic smooth-core and Neumann constant-mode inputs remain
explicit; the off-diagonal identification of the limiting causal integral
is NOT asserted here. No time derivatives of well rates are assumed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal BigOperators InnerProductSpace Distributions

set_option maxHeartbeats 2000000


/-- The physical projected causal-limit conclusion, named separately to avoid
repeated elaboration of a large dependent proposition inside a finite-well
existential. This is a transparent *definition*, not an additional axiom or
mathematical assumption. -/
private def physicalA9LocalizedCausalLimit
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ) (q : Fin m → ℝ → ℝ)
    (g : ℕ → Fin m → S.generatorDomain) : Prop :=
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
    Tendsto
      (fun n : ℕ => P (S t (S.generator p₀)) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • P (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (g n j))))
      atTop
      (𝓝 (P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩)))

/-- Assemble the previously proved *single-well* localized domain
approximations into a simultaneous *finite-well* sequence, and apply the
existing A5 profile-stability theorem. This covers the physical 3D Neumann
Lp realization, the actual centered well profiles, and bounded measurable
rates. The conclusion concerns the limit of the smooth *projected causal*
formulas, not an unproved integral formula for nonsmooth well indicators. -/
theorem paper_A9_physical_localized_multiwell_smooth_causal_limit
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (m : ℕ)
    (U : Fin m → Opens pressureNeumannE3)
    (hU : ∀ j, Bornology.IsBounded (U j : Set pressureNeumannE3))
    (hUΩ : ∀ j, (U j : Set pressureNeumannE3) ⊆
      (Ω : Set pressureNeumannE3))
    (K : Fin m → Set pressureNeumannE3)
    (hK : ∀ j, IsCompact (K j))
    (hKU : ∀ j, K j ⊆ (U j : Set pressureNeumannE3))
    (B : Fin m → pressureNeumannE3 → ℝ)
    (hB : ∀ j, MemLp (B j) 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    (hBsupport : ∀ j, Function.support (B j) ⊆ K j)
    (c : Fin m → ℝ)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν),
      (∀ v : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν),
        ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (f : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (cLp : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hcRep : ∀ j, (cLp j : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[
      pressureNeumann3DRestrictedMeasure Ω ν] fun _ => c j)
    (hfRep : ∀ j, (f j : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[
      pressureNeumann3DRestrictedMeasure Ω ν] fun x => B j x.val - c j)
    (hConstant : ∀ j, cLp j ∈ S.generatorDomain)
    (hCore : ∀ j, ∀ φ : pressureNeumann3DSmoothScalarTests Ω,
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆
        (U j : Set pressureNeumannE3) →
      (pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ φ) ∈ S.generatorDomain)
    (far : Set ↥(Ω : Set pressureNeumannE3))
    (hfar : MeasurableSet far)
    (t : NNReal) (p₀ : S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |q j s| ≤ M j) :
    ∃ (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
      (g : ℕ → Fin m → S.generatorDomain),
      (∀ j n, tsupport ((φ j n) : pressureNeumannE3 → ℝ) ⊆
        (U j : Set pressureNeumannE3)) ∧
      (∀ j n, (g n j : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν)) =
          (pressureNeumann3DSmoothToL2CLM Ω
            (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)) - cLp j) ∧
      (∀ j n, Function.support (fun x : pressureNeumannE3 =>
        (B j x - c j) - ((φ j n : pressureNeumannE3 → ℝ) x - c j)) ⊆
          (U j : Set pressureNeumannE3)) ∧
      physicalA9LocalizedCausalLimit
        (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
        S t p₀ m f q g := by
  classical
  have hEach (j : Fin m) :=
    paper_A9_localized_centered_generator_sequence_L2_tendsto
      Ω (U j) ν hΩ (hU j) (hUΩ j) (K j) (hK j) (hKU j)
      (B j) (hB j) (hBsupport j) (c j) S (cLp j) (f j)
      (hcRep j) (hfRep j) (hConstant j) (hCore j)
  choose φ g hSupport hCentered hLocalized hConverge using hEach
  obtain ⟨hp, hLimit⟩ :=
    paper_A9_chosen_local_approximants_smooth_causal_limit
      (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
      S hSelf hGraph t p₀ m f q hq M hM hBound
      (fun n j => g j n) (fun j => hConverge j)
  refine ⟨φ, (fun n j => g j n),
    (fun j n => hSupport j n),
    (fun j n => hCentered j n),
    (fun j n => hLocalized j n), ?_⟩
  show physicalA9LocalizedCausalLimit
    (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
    S t p₀ m f q (fun n j => g j n)
  exact ⟨hp, hLimit⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_localized_multiwell_smooth_causal_limit
