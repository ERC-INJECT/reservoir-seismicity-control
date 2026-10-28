import ReservoirSeismicityControl.PressureNeumann3DCompactLocalizationLp

/-!
# Genuine interior smooth-test approximation in L² on a restricted ambient measure

Combine the existing dense ambient smooth approximations with the
new quantitative compact localization. Every L² vector or scalar field
on the ambient three-space, measured only inside Ω, admits an arbitrarily
accurate approximation by an actual compactly supported smooth test field
with its support strictly inside Ω.

No density theorem is assumed in these proofs. This is density in the
ambient L² for ν.restrict Ω. Transport to L² of the subtype Ω is separate.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace MeasureTheory
open scoped Distributions ENNReal

variable (Ω : Opens pressureNeumannE3)
variable (ν : Measure pressureNeumannE3)
variable [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]

/-- Actual compactly supported interior smooth vector fields approximate
any L² vector field with respect to the ambient measure restricted to Ω. -/
theorem pressure_neumann_3d_restricted_interior_vector_approx
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothVectorTests Ω,
      eLpNorm (f - (φ : pressureNeumannE3 → pressureNeumannE3)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨g, hgCompact, hgSmooth, hgApprox⟩ :=
    pressure_neumann_3d_restricted_ambient_vector_approx Ω ν f hf hhalf
  obtain ⟨ψ, hψApprox⟩ :=
    pressure_neumann_3d_smooth_compact_localization_eLpNorm Ω ν hΩ
      pressureNeumannE3 g hgSmooth hgCompact
      (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  let φ : pressureNeumann3DSmoothVectorTests Ω :=
    pressureNeumann3DLocalizeVector Ω ψ g hgSmooth
  refine ⟨φ, ?_⟩
  have hφ (x : pressureNeumannE3) :
      (φ : pressureNeumannE3 → pressureNeumannE3) x = ψ x • g x :=
    pressure_neumann_3d_localize_vector_apply Ω ψ g hgSmooth x
  have hfun : (g - (φ : pressureNeumannE3 → pressureNeumannE3)) =
      (fun x => g x - ψ x • g x) := by
    funext x
    change g x - (φ : pressureNeumannE3 → pressureNeumannE3) x =
      g x - ψ x • g x
    rw [hφ x]
  have hlocal : eLpNorm (g - (φ : pressureNeumannE3 → pressureNeumannE3)) 2
      (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal (ε / 2) := by
    rw [hfun]
    exact hψApprox
  have hsum : f - (φ : pressureNeumannE3 → pressureNeumannE3) =
      (f - g) + (g - (φ : pressureNeumannE3 → pressureNeumannE3)) := by
    ext x
    simp only [Pi.sub_apply, Pi.add_apply]
    abel_nf
  rw [hsum]
  calc
    eLpNorm ((f - g) + (g - (φ : pressureNeumannE3 → pressureNeumannE3))) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤
      eLpNorm (f - g) 2 (ν.restrict (Ω : Set pressureNeumannE3)) +
      eLpNorm (g - (φ : pressureNeumannE3 → pressureNeumannE3)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) := eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add hgApprox hlocal
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

/-- The scalar-valued counterpart, for pressure fields. -/
theorem pressure_neumann_3d_restricted_interior_scalar_approx
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (f : pressureNeumannE3 → ℝ)
    (hf : MemLp f 2 (ν.restrict (Ω : Set pressureNeumannE3)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : pressureNeumann3DSmoothScalarTests Ω,
      eLpNorm (f - (φ : pressureNeumannE3 → ℝ)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨g, hgCompact, hgSmooth, hgApprox⟩ :=
    pressure_neumann_3d_restricted_ambient_scalar_approx Ω ν f hf hhalf
  obtain ⟨ψ, hψApprox⟩ :=
    pressure_neumann_3d_smooth_compact_localization_eLpNorm Ω ν hΩ
      ℝ g hgSmooth hgCompact
      (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  let φ : pressureNeumann3DSmoothScalarTests Ω :=
    pressureNeumann3DLocalizeScalar Ω ψ g hgSmooth
  refine ⟨φ, ?_⟩
  have hφ (x : pressureNeumannE3) :
      (φ : pressureNeumannE3 → ℝ) x = ψ x • g x := by
    change ψ x * g x = ψ x • g x
    simp only [smul_eq_mul]
  have hfun : (g - (φ : pressureNeumannE3 → ℝ)) =
      (fun x => g x - ψ x • g x) := by
    funext x
    change g x - (φ : pressureNeumannE3 → ℝ) x = g x - ψ x • g x
    rw [hφ x]
  have hlocal : eLpNorm (g - (φ : pressureNeumannE3 → ℝ)) 2
      (ν.restrict (Ω : Set pressureNeumannE3)) ≤ ENNReal.ofReal (ε / 2) := by
    rw [hfun]
    exact hψApprox
  have hsum : f - (φ : pressureNeumannE3 → ℝ) =
      (f - g) + (g - (φ : pressureNeumannE3 → ℝ)) := by
    ext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsum]
  calc
    eLpNorm ((f - g) + (g - (φ : pressureNeumannE3 → ℝ))) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) ≤
      eLpNorm (f - g) 2 (ν.restrict (Ω : Set pressureNeumannE3)) +
      eLpNorm (g - (φ : pressureNeumannE3 → ℝ)) 2
        (ν.restrict (Ω : Set pressureNeumannE3)) := eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add hgApprox hlocal
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end ReservoirSeismicityControl
