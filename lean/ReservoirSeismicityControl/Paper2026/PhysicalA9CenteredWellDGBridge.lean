import ReservoirSeismicityControl.Paper2026.PhysicalA9AutomaticKernelMeasurability
import ReservoirSeismicityControl.Paper2026.PhysicalA9LocalizedMultiwellCausalLimit
import Mathlib.Tactic

/-!
# Appendix A.3 (A9) — centered physical wells versus localized DG sources

The forcing profile is f_j = B_j/β - |V|⁻¹/β, so its mean-zero correction
is not spatially supported near the well.  The Neumann generator kills
constants.  This module proves that the projected generator orbit of each
CENTERED smooth approximation is exactly that of its localized smooth part.

It then combines the manuscript's bounded well rates with the published
Davies–Gaffney estimate, stated only for those localized smooth parts,
to supply the uniform integrable majorant needed by the already compiled
physical L² causal identification.

External inputs remaining explicit:
* compactly supported test functions belong to the physical generator domain;
* Neumann constants lie in its kernel;
* the uniform integrated off-diagonal estimate for the physical operator
  on localized approximants (this must be checked via their uniform L² bound).

No Q derivative. No new general semigroup or convergence proof.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- The Neumann constant correction disappears from the projected generator
orbit of each centered 3D smooth well approximant. The conclusion is an
IDENTITY, rather than a separately assumed far-field estimate. -/
theorem paper_A9_centered_neumann_orbit_eq_localized_smooth
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (m : ℕ)
    (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
    (cLp : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hCore : ∀ j n, (pressureNeumann3DSmoothToL2CLM Ω
       (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)) ∈ S.generatorDomain)
    (hConstant : ∀ j, cLp j ∈ S.generatorDomain)
    (hConstantZero : ∀ j,
      S.generator ⟨cLp j, hConstant j⟩ = 0)
    (g : ℕ → Fin m → S.generatorDomain)
    (hCentered : ∀ n j, (g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν)) =
        pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j)
    (j : Fin m) (n : ℕ) (τ : NNReal) :
    S τ (S.generator (g n j)) =
      S τ (S.generator
        ⟨pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n), hCore j n⟩) := by
  let u : S.generatorDomain :=
    ⟨pressureNeumann3DSmoothToL2CLM Ω
      (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n), hCore j n⟩
  let c : S.generatorDomain := ⟨cLp j, hConstant j⟩
  have hg : g n j = u - c := by
    apply Subtype.ext
    change (g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) =
      pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j
    exact hCentered n j
  have hGen : S.generator (g n j) = S.generator u := by
    rw [hg, map_sub]
    have hc0 : S.generator c = 0 := hConstantZero j
    rw [hc0, sub_zero]
  exact congrArg (S τ) hGen

/-- Convert the off-diagonal operator estimate on the *localized smooth*
profile to the uniform Bochner majorant for the *centered* physical well.
The former is precisely where the cited DG/analytic semigroup theorem is
applied; the constancy cancellation is proved above. -/
theorem paper_A9_centered_physical_DG_majorant
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (far : Set ↥(Ω : Set pressureNeumannE3)) (hfar : MeasurableSet far)
    (m : ℕ) (t : NNReal)
    (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
    (cLp : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hCore : ∀ j n, (pressureNeumann3DSmoothToL2CLM Ω
       (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)) ∈ S.generatorDomain)
    (hConstant : ∀ j, cLp j ∈ S.generatorDomain)
    (hConstantZero : ∀ j,
      S.generator ⟨cLp j, hConstant j⟩ = 0)
    (g : ℕ → Fin m → S.generatorDomain)
    (hCentered : ∀ n j, (g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν)) =
        pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j)
    (q : Fin m → ℝ → ℝ)
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hQ : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      |q j s| ≤ M j)
    (B : Fin m → ℝ → ℝ)
    (hBnonneg : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      0 ≤ B j s)
    (hDG : ∀ j n, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      ‖ReservoirSeismicityControl.paperFarLpProjection
        (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
        (S (Real.toNNReal ((t : ℝ) - s))
          (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
            (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n),
              hCore j n⟩))‖ ≤ B j s) :
    ∀ j n, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      ‖(q j s) • ReservoirSeismicityControl.paperFarLpProjection
        (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
        (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))‖ ≤
          M j * B j s := by
  intro j n
  filter_upwards [hQ j, hBnonneg j, hDG j n] with s hq hb hdg
  let P := ReservoirSeismicityControl.paperFarLpProjection
    (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
  have horbit := paper_A9_centered_neumann_orbit_eq_localized_smooth
    Ω ν S m φ cLp hCore hConstant hConstantZero g hCentered
    j n (Real.toNNReal ((t : ℝ) - s))
  have hlocal : P (S (Real.toNNReal ((t : ℝ) - s))
        (S.generator (g n j))) =
      P (S (Real.toNNReal ((t : ℝ) - s))
        (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n), hCore j n⟩)) :=
    congrArg P horbit
  calc
    ‖(q j s) • P (S (Real.toNNReal ((t : ℝ) - s))
        (S.generator (g n j)))‖ =
      |q j s| * ‖P (S (Real.toNNReal ((t : ℝ) - s))
        (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n), hCore j n⟩))‖ := by
          rw [hlocal, norm_smul, Real.norm_eq_abs]
    _ ≤ |q j s| * B j s := mul_le_mul_of_nonneg_left hdg (abs_nonneg _)
    _ ≤ M j * B j s := mul_le_mul_of_nonneg_right hq hb

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_centered_neumann_orbit_eq_localized_smooth
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_centered_physical_DG_majorant
