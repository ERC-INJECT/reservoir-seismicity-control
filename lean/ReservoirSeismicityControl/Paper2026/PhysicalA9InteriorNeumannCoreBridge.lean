import ReservoirSeismicityControl.Paper2026.PhysicalA9WellSubtypeApproximation
import ReservoirSeismicityControl.PressureNeumann3DSmoothCanonicalL2
import ReservoirSeismicityControl.PressureNeumann3DBoundedDomainMeasure
import Mathlib.Tactic

/-!
# Appendix A.3 — the *localized* Neumann generator-domain interface

The previous theorem constructed compactly supported smooth approximants
for the actual mean-corrected well in the reservoir-subtype L² norm.
Here we show that each such approximant is in D(A), provided only the two
standard physical Neumann core properties listed below:

* a compactly supported smooth test has a generator-domain representative
  (the local W¹,∞ coefficient / weak Green identity result from A3);
* the constant pressure mode lies in the Neumann generator domain.

These are EXTERNAL elliptic applicability premises. This theorem does not
prove them; it also does not assert the full A9 causal identity.
Neither Q̇ nor any new semigroup estimate is assumed.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal

/-- Combine the already verified localization theorem with the standard
Neumann smooth-core and constant-mode inclusions. The centered smooth
profile is now a genuine element of the physical generator domain, while
the quantitative localized approximation is preserved.

`hCore` must be justified by local `W¹,∞` regularity of the actual
coefficient field, not by the desired A9 conclusion. `hConstant` is the
standard Neumann constant-kernel inclusion. -/
theorem paper_A9_localized_centered_well_in_neumann_generator_domain
    (Ω U : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (hU : Bornology.IsBounded (U : Set pressureNeumannE3))
    (hUΩ : (U : Set pressureNeumannE3) ⊆ (Ω : Set pressureNeumannE3))
    (K : Set pressureNeumannE3) (hK : IsCompact K)
    (hKU : K ⊆ (U : Set pressureNeumannE3))
    (B : pressureNeumannE3 → ℝ)
    (hB : MemLp B 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    (hBsupport : Function.support B ⊆ K)
    (c : ℝ)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (cLp : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hConstant : cLp ∈ S.generatorDomain)
    (hCore : ∀ φ : pressureNeumann3DSmoothScalarTests Ω,
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆
        (U : Set pressureNeumannE3) →
      (pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ φ) ∈ S.generatorDomain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω,
      tsupport (φ : pressureNeumannE3 → ℝ) ⊆
        (U : Set pressureNeumannE3) ∧
      ((pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ φ) - cLp) ∈
        S.generatorDomain ∧
      eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        (B x.val - c) - ((φ : pressureNeumannE3 → ℝ) x.val - c)) 2
        (pressureNeumann3DRestrictedMeasure Ω ν) ≤ ENNReal.ofReal ε ∧
      Function.support (fun x : pressureNeumannE3 =>
        (B x - c) - ((φ : pressureNeumannE3 → ℝ) x - c)) ⊆
        (U : Set pressureNeumannE3) := by
  classical
  obtain ⟨φ, hφU, hφNorm, hφError⟩ :=
    paper_A9_physical_3d_centered_well_subtype_approximation
      Ω U ν hΩ hU hUΩ K hK hKU B hB hBsupport c hε
  refine ⟨φ, hφU, ?_, hφNorm, hφError⟩
  exact S.generatorDomain.sub_mem (hCore φ hφU) hConstant

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_localized_centered_well_in_neumann_generator_domain
