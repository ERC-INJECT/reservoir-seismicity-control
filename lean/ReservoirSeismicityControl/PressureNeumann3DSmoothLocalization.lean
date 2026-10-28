import ReservoirSeismicityControl.PressureNeumann3DInteriorBumpTests

/-!
# Localizing smooth ambient functions inside the physical reservoir

The product of an actual interior scalar test function and an ambient smooth
scalar/vector field is a smooth test function supported inside Ω. This is
an explicit, unconditional construction of the required support localization
operation. No assumption that the ambient field is compactly supported is
needed: the cutoff already supplies the compact support.

The next analytic step is to choose a sequence of cutoffs tending to 1 in
L²(Ω) and bound the resulting localization error. That quantitative density
step is not claimed in this file.
-/

namespace ReservoirSeismicityControl

open TopologicalSpace
open scoped Distributions

variable (Ω : Opens pressureNeumannE3)

/-- Multiply a smooth ambient scalar function by a genuine interior cutoff.
The resulting function is a compactly supported scalar test in Ω. -/
noncomputable def pressureNeumann3DLocalizeScalar
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (f : pressureNeumannE3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    pressureNeumann3DSmoothScalarTests Ω :=
  ⟨fun x => ψ x * f x,
    ψ.contDiff.mul hf,
    ψ.hasCompactSupport.mul_right,
    (tsupport_mul_subset_left (f := (ψ : pressureNeumannE3 → ℝ))
      (g := f)).trans ψ.tsupport_subset⟩

/-- The scalar localization is the expected pointwise product. -/
theorem pressure_neumann_3d_localize_scalar_apply
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (f : pressureNeumannE3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x : pressureNeumannE3) :
    pressureNeumann3DLocalizeScalar Ω ψ f hf x = ψ x * f x := rfl

/-- Multiply a smooth ambient 3D vector field by a scalar interior cutoff.
The result belongs to the actual vector test space C_c^∞(Ω; ℝ³). -/
noncomputable def pressureNeumann3DLocalizeVector
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    pressureNeumann3DSmoothVectorTests Ω :=
  ⟨fun x => ψ x • f x,
    ψ.contDiff.smul hf,
    ψ.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left (ψ : pressureNeumannE3 → ℝ) f).trans
      ψ.tsupport_subset⟩

/-- The vector localization is the expected pointwise scalar product. -/
theorem pressure_neumann_3d_localize_vector_apply
    (ψ : pressureNeumann3DSmoothScalarTests Ω)
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x : pressureNeumannE3) :
    pressureNeumann3DLocalizeVector Ω ψ f hf x = ψ x • f x := rfl

/-- Localizing at a point with a cutoff equal to one preserves the value of
any smooth ambient scalar function at that point. -/
theorem pressure_neumann_3d_exists_localization_scalar_eq_at
    (f : pressureNeumannE3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3)) :
    ∃ g : pressureNeumann3DSmoothScalarTests Ω, g x = f x := by
  obtain ⟨ψ, hψ⟩ := pressure_neumann_3d_exists_scalar_bump Ω x hx
  refine ⟨pressureNeumann3DLocalizeScalar Ω ψ f hf, ?_⟩
  rw [pressure_neumann_3d_localize_scalar_apply, hψ, one_mul]

/-- The vector-valued version of pointwise exact smooth localization. -/
theorem pressure_neumann_3d_exists_localization_vector_eq_at
    (f : pressureNeumannE3 → pressureNeumannE3)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x : pressureNeumannE3) (hx : x ∈ (Ω : Set pressureNeumannE3)) :
    ∃ g : pressureNeumann3DSmoothVectorTests Ω, g x = f x := by
  obtain ⟨ψ, hψ⟩ := pressure_neumann_3d_exists_scalar_bump Ω x hx
  refine ⟨pressureNeumann3DLocalizeVector Ω ψ f hf, ?_⟩
  rw [pressure_neumann_3d_localize_vector_apply, hψ, one_smul]

end ReservoirSeismicityControl
