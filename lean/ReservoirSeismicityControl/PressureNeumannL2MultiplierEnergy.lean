import ReservoirSeismicityControl.PressureNeumannPhysicalTensorA3Multiplier
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Block 70: symmetry and ellipticity of the spatial L² multiplier

A measurable essentially bounded pointwise operator field induces the L²
multiplier already constructed in `PressureNeumannL2TensorMultiplier`.
This file transfers pointwise symmetry and lower/upper quadratic bounds to
that actual L² multiplier by integrating pointwise Hilbert-space inequalities.

The lemmas are generic so that they can be applied to the physical
three-dimensional A3 tensor and then to the Neumann energy-form theorem.
They do not postulate new bounds on well-flux time derivatives.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

section GenericL2Energy

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pointwise symmetry passes to the actual multiplication operator on L². -/
theorem pressure_neumann_l2_multiplier_symmetric
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (hSym : ∀ᵐ x ∂μ, ∀ a b : E,
      ⟪C x a, b⟫_ℝ = ⟪a, C x b⟫_ℝ)
    (f g : Lp E 2 μ) :
    ⟪pressureNeumannL2Multiplier μ C hC M hM hBound f, g⟫_ℝ =
      ⟪f, pressureNeumannL2Multiplier μ C hC M hM hBound g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [pressure_neumann_l2_multiplier_apply_ae μ C hC M hM hBound f,
     pressure_neumann_l2_multiplier_apply_ae μ C hC M hM hBound g,
     hSym] with x hf hg hx
  rw [hf, hg]
  exact hx (f x) (g x)

/-- A pointwise uniform ellipticity inequality gives the same coercive
quadratic estimate in the actual L² inner product. -/
theorem pressure_neumann_l2_multiplier_elliptic_lower
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (c : ℝ)
    (hEll : ∀ᵐ x ∂μ, ∀ z : E,
      c * (‖z‖ * ‖z‖) ≤ ⟪C x z, z⟫_ℝ)
    (f : Lp E 2 μ) :
    c * (‖f‖ * ‖f‖) ≤
      ⟪pressureNeumannL2Multiplier μ C hC M hM hBound f, f⟫_ℝ := by
  let B := pressureNeumannL2Multiplier μ C hC M hM hBound
  have hInt : (∫ x, c * ⟪f x, f x⟫_ℝ ∂μ) ≤
      ∫ x, ⟪B f x, f x⟫_ℝ ∂μ := by
    apply integral_mono_ae
    · exact (L2.integrable_inner f f).const_mul c
    · exact L2.integrable_inner (B f) f
    · filter_upwards
        [hEll, pressure_neumann_l2_multiplier_apply_ae μ C hC M hM hBound f]
        with x hx hfx
      change c * ⟪f x, f x⟫_ℝ ≤ ⟪B f x, f x⟫_ℝ
      rw [hfx, real_inner_self_eq_norm_mul_norm]
      exact hx (f x)
  calc
    c * (‖f‖ * ‖f‖) = c * ⟪f, f⟫_ℝ := by
      rw [real_inner_self_eq_norm_mul_norm]
    _ = ∫ x, c * ⟪f x, f x⟫_ℝ ∂μ := by
      rw [L2.inner_def, integral_const_mul]
    _ ≤ ∫ x, ⟪B f x, f x⟫_ℝ ∂μ := hInt
    _ = ⟪B f, f⟫_ℝ := (L2.inner_def _ _).symm

/-- The upper quadratic bound is also preserved by the L² multiplier. -/
theorem pressure_neumann_l2_multiplier_elliptic_upper
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (b : ℝ)
    (hUpper : ∀ᵐ x ∂μ, ∀ z : E,
      ⟪C x z, z⟫_ℝ ≤ b * (‖z‖ * ‖z‖))
    (f : Lp E 2 μ) :
    ⟪pressureNeumannL2Multiplier μ C hC M hM hBound f, f⟫_ℝ ≤
      b * (‖f‖ * ‖f‖) := by
  let B := pressureNeumannL2Multiplier μ C hC M hM hBound
  have hInt : (∫ x, ⟪B f x, f x⟫_ℝ ∂μ) ≤
      ∫ x, b * ⟪f x, f x⟫_ℝ ∂μ := by
    apply integral_mono_ae
    · exact L2.integrable_inner (B f) f
    · exact (L2.integrable_inner f f).const_mul b
    · filter_upwards
        [hUpper, pressure_neumann_l2_multiplier_apply_ae μ C hC M hM hBound f]
        with x hx hfx
      change ⟪B f x, f x⟫_ℝ ≤ b * ⟪f x, f x⟫_ℝ
      rw [hfx, real_inner_self_eq_norm_mul_norm]
      exact hx (f x)
  calc
    ⟪B f, f⟫_ℝ = ∫ x, ⟪B f x, f x⟫_ℝ ∂μ := L2.inner_def _ _
    _ ≤ ∫ x, b * ⟪f x, f x⟫_ℝ ∂μ := hInt
    _ = b * ⟪f, f⟫_ℝ := by rw [L2.inner_def, integral_const_mul]
    _ = b * (‖f‖ * ‖f‖) := by rw [real_inner_self_eq_norm_mul_norm]

end GenericL2Energy

end ReservoirSeismicityControl
