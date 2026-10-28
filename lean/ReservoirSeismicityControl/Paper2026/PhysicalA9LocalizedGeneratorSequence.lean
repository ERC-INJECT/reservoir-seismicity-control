import ReservoirSeismicityControl.Paper2026.PhysicalA9InteriorNeumannCoreBridge
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): one localized generator-domain approximation sequence

The previous proved result supplies, for EACH positive tolerance, a smooth
well-source approximation with near-supported error and a centered member of
the Neumann generator domain. Here we assemble those witnesses into ONE
sequence with the explicit error tolerance 1/(n+1). This is needed before
applying the existing choice-preserving A5 generator-stability theorem.

Two physical elliptic inputs remain explicit: the Neumann smooth interior
core property and the constant-mode domain property. Neither the physical
A9 formula nor the Davies--Gaffney bound is assumed in this module.

No derivative of well rates is used.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal

/-- Construct a single sequence of genuinely centered smooth well profiles
in the physical Neumann generator domain, whose approximation errors stay
inside U and whose L² seminorms are bounded by 1/(n+1).

The two domain hypotheses are precisely the standard *elliptic* inputs
already exposed in the preceding compiled theorem. -/
theorem paper_A9_localized_centered_generator_approximation_sequence
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
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ φ) ∈ S.generatorDomain) :
    ∃ (φ : ℕ → pressureNeumann3DSmoothScalarTests Ω)
      (fApprox : ℕ → S.generatorDomain),
      (∀ n, tsupport (φ n : pressureNeumannE3 → ℝ) ⊆
        (U : Set pressureNeumannE3)) ∧
      (∀ n, (fApprox n : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν)) =
        (pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ n)) - cLp) ∧
      (∀ n, eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        (B x.val - c) - ((φ n : pressureNeumannE3 → ℝ) x.val - c)) 2
        (pressureNeumann3DRestrictedMeasure Ω ν) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
      (∀ n, Function.support (fun x : pressureNeumannE3 =>
        (B x - c) - ((φ n : pressureNeumannE3 → ℝ) x - c)) ⊆
        (U : Set pressureNeumannE3)) := by
  classical
  have hε (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hExist (n : ℕ) :=
    paper_A9_localized_centered_well_in_neumann_generator_domain
      Ω U ν hΩ hU hUΩ K hK hKU B hB hBsupport c
      S cLp hConstant hCore (hε n)
  let φ (n : ℕ) : pressureNeumann3DSmoothScalarTests Ω := (hExist n).choose
  have hSupport (n : ℕ) :
      tsupport (φ n : pressureNeumannE3 → ℝ) ⊆
        (U : Set pressureNeumannE3) := (hExist n).choose_spec.1
  have hDomain (n : ℕ) :
      ((pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ n)) - cLp) ∈
        S.generatorDomain := (hExist n).choose_spec.2.1
  let fApprox (n : ℕ) : S.generatorDomain :=
    ⟨(pressureNeumann3DSmoothToL2CLM Ω
      (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ n)) - cLp,
       hDomain n⟩
  refine ⟨φ, fApprox, hSupport, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    exact (hExist n).choose_spec.2.2.1
  · intro n
    exact (hExist n).choose_spec.2.2.2

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_localized_centered_generator_approximation_sequence
