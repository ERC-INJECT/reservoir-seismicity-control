import ReservoirSeismicityControl.Paper2026.PhysicalA9LocalizedGeneratorSequence
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A9: localized generator-domain approximants converge in the physical L² norm

The earlier verified theorem supplies approximants with eLpNorm error at most
1/(n+1), but does not establish the Lp-space Tendsto required by the existing
A5 profile-stability theorem. This module performs that identification with
the *actual* physical L² representative, using the already proved canonical
smooth-test AE identification and Mathlib's Lp distance formula.

The two AE representative hypotheses have a narrow meaning: `f` is the actual
L² class of `B-c` and `cLp` is the actual constant function `c`. They are
not assumptions of convergence or of the desired A9 identity.

The standard Neumann smooth-core and constant-mode inclusions remain external
elliptic inputs, exactly as in the previous verified module. No Q derivative.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped Distributions ENNReal

set_option maxHeartbeats 2000000

/-- The geometry-preserving D(A) approximations, already constructed with
errors at most 1/(n+1), converge to the physical centered well source in the
strong reservoir-subtype L² norm. The only extra assumptions identify the
actual L² representatives of the physical functions B-c and c. -/
theorem paper_A9_localized_centered_generator_sequence_L2_tendsto
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
    (cLp f : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hcRep : (cLp : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[
      pressureNeumann3DRestrictedMeasure Ω ν] fun _ => c)
    (hfRep : (f : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[
      pressureNeumann3DRestrictedMeasure Ω ν] fun x => B x.val - c)
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
      (∀ n, Function.support (fun x : pressureNeumannE3 =>
        (B x - c) - ((φ n : pressureNeumannE3 → ℝ) x - c)) ⊆
        (U : Set pressureNeumannE3)) ∧
      Tendsto (fun n : ℕ => (fApprox n : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν))) atTop (𝓝 f) := by
  classical
  let μ' := pressureNeumann3DRestrictedMeasure Ω ν
  obtain ⟨φ, fApprox, hSupport, hApprox, hErr, hErrSupport⟩ :=
    paper_A9_localized_centered_generator_approximation_sequence
      Ω U ν hΩ hU hUΩ K hK hKU B hB hBsupport c S cLp hConstant hCore
  refine ⟨φ, fApprox, hSupport, hApprox, hErrSupport, ?_⟩
  have hSmoothAE (n : ℕ) :
      ((fApprox n : Lp ℝ 2 μ') : ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[μ']
        fun x => (φ n : pressureNeumannE3 → ℝ) x.val - c := by
    rw [hApprox n]
    have hSub := Lp.coeFn_sub
      (pressureNeumann3DSmoothToL2CLM Ω μ' ℝ (φ n)) cLp
    have hTest := pressure_neumann_3d_smooth_toL2_ae Ω μ' ℝ (φ n)
    filter_upwards [hSub, hTest, hcRep] with x hx hy hz
    simpa only [Pi.sub_apply, hy, hz] using hx
  have hDiffAE (n : ℕ) :
      (((f - (fApprox n : Lp ℝ 2 μ')) : Lp ℝ 2 μ') :
        ↥(Ω : Set pressureNeumannE3) → ℝ) =ᵐ[μ']
      fun x => (B x.val - c) - ((φ n : pressureNeumannE3 → ℝ) x.val - c) := by
    have hSub := Lp.coeFn_sub f (fApprox n : Lp ℝ 2 μ')
    filter_upwards [hSub, hfRep, hSmoothAE n] with x hx hy hz
    simpa only [Pi.sub_apply, hy, hz] using hx
  have hRate (n : ℕ) :
      dist (fApprox n : Lp ℝ 2 μ') f ≤ 1 / ((n : ℝ) + 1) := by
    rw [dist_comm, Lp.dist_def]
    have hCoeDiff := Lp.coeFn_sub f (fApprox n : Lp ℝ 2 μ')
    have hSameAE :
        ((f : ↥(Ω : Set pressureNeumannE3) → ℝ) -
          ((fApprox n : Lp ℝ 2 μ') : ↥(Ω : Set pressureNeumannE3) → ℝ))
          =ᵐ[μ'] fun x =>
            (B x.val - c) - ((φ n : pressureNeumannE3 → ℝ) x.val - c) :=
      hCoeDiff.symm.trans (hDiffAE n)
    rw [eLpNorm_congr_ae hSameAE]
    have hFinite : ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ := by simp
    have hReal := ENNReal.toReal_mono hFinite (hErr n)
    have hεn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    calc
      (eLpNorm (fun x : ↥(Ω : Set pressureNeumannE3) =>
        (B x.val - c) - ((φ n : pressureNeumannE3 → ℝ) x.val - c))
        2 μ').toReal
          ≤ (ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal := hReal
      _ = 1 / ((n : ℝ) + 1) := ENNReal.toReal_ofReal hεn
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg)
    hRate (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_localized_centered_generator_sequence_L2_tendsto
