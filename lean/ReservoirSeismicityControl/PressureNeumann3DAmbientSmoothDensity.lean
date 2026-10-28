import ReservoirSeismicityControl.PressureNeumann3DCanonicalDensityReduction
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Smooth L² approximation in ambient Euclidean three-space

These are genuine (unconditional) density and approximation results
for an ambient measure finite on compact subsets of R³.  We apply
Mathlib's compactly-supported smooth approximation theorem to both
scalar pressures and 3D vector fields.

IMPORTANT: These statements are on the AMBIENT space, not yet on the
space of test functions supported inside the physical domain Ω.
Passing from compact support in R³ to compact support contained in Ω
is the next mathematical step.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped ENNReal

variable (ν : Measure pressureNeumannE3) [IsFiniteMeasureOnCompacts ν]

/-- Arbitrary ambient scalar L² functions can be approximated by globally
smooth and compactly supported scalar functions. -/
theorem pressure_neumann_3d_ambient_scalar_smooth_dense :
    Dense {f : Lp ℝ 2 ν |
      ∃ g : pressureNeumannE3 → ℝ,
        (f : pressureNeumannE3 → ℝ) =ᵐ[ν] g ∧
          HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g} := by
  exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := ℝ) (μ := ν) (p := (2 : ENNReal)) (by simp)

/-- The same actual density theorem for 3D vector fields. -/
theorem pressure_neumann_3d_ambient_vector_smooth_dense :
    Dense {f : Lp pressureNeumannE3 2 ν |
      ∃ g : pressureNeumannE3 → pressureNeumannE3,
        (f : pressureNeumannE3 → pressureNeumannE3) =ᵐ[ν] g ∧
          HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g} := by
  exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := pressureNeumannE3) (μ := ν) (p := (2 : ENNReal)) (by simp)

/-- Quantitative ambient scalar smooth approximation, for any error tolerance. -/
theorem pressure_neumann_3d_ambient_scalar_smooth_approx
    (f : pressureNeumannE3 → ℝ) (hf : MemLp f 2 ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : pressureNeumannE3 → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
        eLpNorm (f - g) 2 ν ≤ ENNReal.ofReal ε := by
  exact MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (μ := ν) (p := (2 : ENNReal)) (by simp) (by norm_num) hf hε

/-- Quantitative ambient vector-field smooth approximation. -/
theorem pressure_neumann_3d_ambient_vector_smooth_approx
    (f : pressureNeumannE3 → pressureNeumannE3) (hf : MemLp f 2 ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : pressureNeumannE3 → pressureNeumannE3,
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
        eLpNorm (f - g) 2 ν ≤ ENNReal.ofReal ε := by
  exact MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (μ := ν) (p := (2 : ENNReal)) (by simp) (by norm_num) hf hε

end ReservoirSeismicityControl
