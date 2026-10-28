import ReservoirSeismicityControl.Paper2026.PhysicalA9CenteredWellDGBridge
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): one uniform DG envelope for actual centered wells

This is a *physical applicability* step. The centered smooth generators have
localized parts plus the common Neumann constant mode. Cancellation of that
mode was proved in `PhysicalA9CenteredWellDGBridge`.

Here a quantitative, already constructed L² approximation estimate produces
ONE norm bound independent of the approximation index. The cited
Davies--Gaffney/analytic-semigroup estimate needs only be applied to the
localized smooth profiles, and its common scalar lag envelope produces an
integrable bound for ALL centered approximants and all bounded well rates.

The operator-valued Davies--Gaffney inequality itself is an explicitly
identified external semigroup input from Appendix A.3; it is NOT proved here.
No derivative of the well rates is assumed, and no desired A9 equality is
an assumption or conclusion of this module.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal InnerProductSpace BigOperators Distributions

set_option maxHeartbeats 2000000

/-- Quantitative uniform L² bound for the *localized, uncentered* smooth
profile. The only input beyond the already constructed centered sequence is
its pointwise norm error bound `1/(n+1)`, proved inside the earlier physical
Lp approximation argument. This bound is independent of n. -/
theorem paper_A9_localized_smooth_source_uniform_norm
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (m : ℕ)
    (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
    (cLp f : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (g : ℕ → Fin m → S.generatorDomain)
    (hCentered : ∀ n j,
      (g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) =
        pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j)
    (hApproxNorm : ∀ n j,
      ‖(g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) - f j‖ ≤
        1 / ((n : ℝ) + 1))
    (j : Fin m) (n : ℕ) :
    ‖pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)‖ ≤
      ‖f j‖ + ‖cLp j‖ + 1 := by
  let v : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν) :=
    pressureNeumann3DSmoothToL2CLM Ω
      (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)
  have hv : v = (g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν)) + cLp j := by
    exact (eq_sub_iff_add_eq.mp (hCentered n j)).symm
  have hSmall : 1 / ((n : ℝ) + 1) ≤ 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    nlinarith
  have hg : ‖(g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν))‖ ≤ ‖f j‖ + 1 := by
    calc
      ‖(g n j : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν))‖ =
          ‖((g n j : Lp ℝ 2
            (pressureNeumann3DRestrictedMeasure Ω ν)) - f j) + f j‖ := by
              rw [sub_add_cancel]
      _ ≤ ‖(g n j : Lp ℝ 2
        (pressureNeumann3DRestrictedMeasure Ω ν)) - f j‖ + ‖f j‖ :=
          norm_add_le _ _
      _ ≤ 1 / ((n : ℝ) + 1) + ‖f j‖ :=
          add_le_add_left (hApproxNorm n j) _
      _ ≤ ‖f j‖ + 1 := by linarith
  calc
    ‖pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)‖ = ‖v‖ := rfl
    _ = ‖(g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν)) + cLp j‖ := by rw [hv]
    _ ≤ ‖(g n j : Lp ℝ 2
      (pressureNeumann3DRestrictedMeasure Ω ν))‖ + ‖cLp j‖ :=
        norm_add_le _ _
    _ ≤ ‖f j‖ + ‖cLp j‖ + 1 := by linarith

/-- A single integrable lag envelope for EVERY localized centered smooth
approximation, and therefore the exact `hOffDiag` input of the previously
proved A9 physical causal identification. The source-level DG estimate is
explicitly applied only to the localized smooth profile, never to its
nonlocalized constant correction. -/
theorem paper_A9_uniform_integrable_physical_DG_envelope
    (Ω : Opens pressureNeumannE3)
    (ν : Measure pressureNeumannE3)
    [IsFiniteMeasure (pressureNeumann3DRestrictedMeasure Ω ν)]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)))
    (far : Set ↥(Ω : Set pressureNeumannE3))
    (hfar : MeasurableSet far)
    (m : ℕ) (t : NNReal)
    (φ : Fin m → ℕ → pressureNeumann3DSmoothScalarTests Ω)
    (cLp f : Fin m → Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν))
    (hCore : ∀ j n,
      pressureNeumann3DSmoothToL2CLM Ω
        (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) ∈ S.generatorDomain)
    (hConstant : ∀ j, cLp j ∈ S.generatorDomain)
    (hConstantZero : ∀ j, S.generator ⟨cLp j, hConstant j⟩ = 0)
    (g : ℕ → Fin m → S.generatorDomain)
    (hCentered : ∀ n j,
      (g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) =
        pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n) - cLp j)
    (hApproxNorm : ∀ n j,
      ‖(g n j : Lp ℝ 2 (pressureNeumann3DRestrictedMeasure Ω ν)) - f j‖ ≤
        1 / ((n : ℝ) + 1))
    (q : Fin m → ℝ → ℝ)
    (M : Fin m → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hQ : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      |q j s| ≤ M j)
    (K : Fin m → ℝ → ℝ)
    (hKInt : ∀ j,
      Integrable (K j) (volume.restrict (Set.Ioc 0 (t : ℝ))))
    (hKNonneg : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      0 ≤ K j s)
    (hDGlocal : ∀ j n, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
      ‖ReservoirSeismicityControl.paperFarLpProjection
        (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
        (S (Real.toNNReal ((t : ℝ) - s))
          (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
            (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n),
              hCore j n⟩))‖ ≤
        K j s * ‖pressureNeumann3DSmoothToL2CLM Ω
          (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n)‖) :
    ∃ b : Fin m → ℝ → ℝ,
      (∀ j, Integrable (b j)
        (volume.restrict (Set.Ioc 0 (t : ℝ)))) ∧
      (∀ j n, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        ‖(q j s) • ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))‖ ≤
        b j s) := by
  let L : Fin m → ℝ := fun j => ‖f j‖ + ‖cLp j‖ + 1
  let b : Fin m → ℝ → ℝ := fun j s => M j * (K j s * L j)
  have hL (j : Fin m) : 0 ≤ L j := by
    dsimp [L]
    positivity
  have hbInt (j : Fin m) : Integrable (b j)
      (volume.restrict (Set.Ioc 0 (t : ℝ))) := by
    dsimp [b]
    exact ((hKInt j).mul_const (L j)).const_mul (M j)
  have hbNonneg (j : Fin m) :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        0 ≤ K j s * L j := by
    filter_upwards [hKNonneg j] with s hs
    exact mul_nonneg hs (hL j)
  have hMajorant (j : Fin m) (n : ℕ) :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        ‖ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s))
            (S.generator ⟨pressureNeumann3DSmoothToL2CLM Ω
              (pressureNeumann3DRestrictedMeasure Ω ν) ℝ (φ j n),
                hCore j n⟩))‖ ≤ K j s * L j := by
    filter_upwards [hDGlocal j n, hKNonneg j] with s hbound hs
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (paper_A9_localized_smooth_source_uniform_norm
        Ω ν S m φ cLp f g hCentered hApproxNorm j n) hs)
  have hQmajorant (j : Fin m) (n : ℕ) :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 (t : ℝ))),
        ‖(q j s) • ReservoirSeismicityControl.paperFarLpProjection
          (pressureNeumann3DRestrictedMeasure Ω ν) far hfar
          (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n j)))‖ ≤
        M j * (K j s * L j) :=
    paper_A9_centered_physical_DG_majorant
      Ω ν S far hfar m t φ cLp hCore hConstant hConstantZero
      g hCentered q M hM hQ (fun j s => K j s * L j)
      hbNonneg hMajorant j n
  refine ⟨b, hbInt, ?_⟩
  intro j n
  exact hQmajorant j n

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_localized_smooth_source_uniform_norm
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_uniform_integrable_physical_DG_envelope
