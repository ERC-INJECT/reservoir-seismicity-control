import ReservoirSeismicityControl.PressureNeumann3DAmbientSmoothDensity

/-!
# Smooth approximation for the reservoir-restricted ambient measure

We apply the *proven* ambient smooth L² approximation theorem to
ν.restrict Ω.  This measure is supported on the reservoir, so the
approximation controls the error only within Ω.

An ambient smooth approximant need not itself have support inside Ω.
Consequently this is NOT YET density of TestFunction Ω F ⊤ in L²(Ω).
The missing operation is localization of approximants by smooth
cutoffs with compact support inside Ω, together with an L² error bound.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped ENNReal

variable (Ω : Opens pressureNeumannE3)
variable (ν : Measure pressureNeumannE3) [IsFiniteMeasureOnCompacts ν]

/-- The actual ambient smooth scalar functions are dense in L²
for the measure restricted to Ω. -/
theorem pressure_neumann_3d_restricted_ambient_scalar_dense :
    Dense {f : Lp ℝ 2 (ν.restrict (Ω : Set pressureNeumannE3)) |
      ∃ g : pressureNeumannE3 → ℝ,
        (f : pressureNeumannE3 → ℝ) =ᵐ[ν.restrict (Ω : Set pressureNeumannE3)] g ∧
          HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g} := by
  exact pressure_neumann_3d_ambient_scalar_smooth_dense
    (ν.restrict (Ω : Set pressureNeumannE3))

/-- The parallel density statement for 3D vector fields. -/
theorem pressure_neumann_3d_restricted_ambient_vector_dense :
    Dense {f : Lp pressureNeumannE3 2 (ν.restrict (Ω : Set pressureNeumannE3)) |
      ∃ g : pressureNeumannE3 → pressureNeumannE3,
        (f : pressureNeumannE3 → pressureNeumannE3) =ᵐ[ν.restrict (Ω : Set pressureNeumannE3)] g ∧
          HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g} := by
  exact pressure_neumann_3d_ambient_vector_smooth_dense
    (ν.restrict (Ω : Set pressureNeumannE3))

/-- Explicit error control for pressure approximation inside Ω. -/
theorem pressure_neumann_3d_restricted_ambient_scalar_approx
    (f : pressureNeumannE3 → ℝ)
    (hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : pressureNeumannE3 → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
        eLpNorm (f - g) 2 (ν.restrict (Ω : Set pressureNeumannE3)) ≤
          ENNReal.ofReal ε := by
  exact pressure_neumann_3d_ambient_scalar_smooth_approx
    (ν.restrict (Ω : Set pressureNeumannE3)) f hf hε

/-- Explicit error control for vector fields inside Ω. -/
theorem pressure_neumann_3d_restricted_ambient_vector_approx
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : pressureNeumannE3 → pressureNeumannE3,
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
        eLpNorm (f - g) 2 (ν.restrict (Ω : Set pressureNeumannE3)) ≤
          ENNReal.ofReal ε := by
  exact pressure_neumann_3d_ambient_vector_smooth_approx
    (ν.restrict (Ω : Set pressureNeumannE3)) f hf hε

end ReservoirSeismicityControl
