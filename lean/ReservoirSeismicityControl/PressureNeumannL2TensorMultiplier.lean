import ReservoirSeismicityControl.PressureNeumannPointwiseTensorCLM
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Block 70 — bounded spatially varying coefficient multiplication on vector L²

An essentially bounded a.e.-strongly-measurable field of continuous linear
endomorphisms induces a bounded operator on Bochner L², with the same uniform
bound. This is a genuine operator, not an extra abstract form assumption.

For the physical k/(beta*eta), coefficient measurability is linked to the
measurability of all nine tensor entries. The uniform operator-norm bound is
kept explicit here. Its derivation from the positive symmetric pointwise
quadratic upper bound is a separate forthcoming step.

No assumption on the well flux time derivatives is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

section GenericMultiplier

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A measurable and essentially uniformly bounded operator field maps each
square-integrable vector field to a square-integrable vector field. -/
private theorem pressure_neumann_l2_multiplier_mem
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (f : Lp E 2 μ) :
    MemLp (fun x => C x (f x)) 2 μ := by
  have hMeas : AEStronglyMeasurable (fun x => C x (f x)) μ := by
    have hJoint : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E)).continuous
    exact hJoint.comp_aestronglyMeasurable (hC.prodMk (Lp.aestronglyMeasurable f))
  apply (Lp.memLp f).of_le_mul hMeas
  filter_upwards [hBound] with x hx
  exact ((C x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Pointwise action of an essentially bounded measurable tensor operator,
interpreted as a function from L² into L². -/
private noncomputable def pressureNeumannL2MultiplierFun
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (f : Lp E 2 μ) : Lp E 2 μ :=
  MemLp.toLp (fun x => C x (f x))
    (pressure_neumann_l2_multiplier_mem μ C hC M hBound f)

/-- The representative of the multiplier is pointwise multiplication almost everywhere.
Keeping this lemma in the bundled-function form avoids unfolding `MemLp.toLp`
in subsequent linearity and operator-norm proofs. -/
private theorem pressure_neumann_l2_multiplier_fun_ae
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (f : Lp E 2 μ) :
    (pressureNeumannL2MultiplierFun μ C hC M hBound f : Ω → E) =ᵐ[μ]
      fun x => C x (f x) := by
  exact MemLp.coeFn_toLp
    (pressure_neumann_l2_multiplier_mem μ C hC M hBound f)

/-- Spatially varying multiplication defines a bounded linear map on L². -/
noncomputable def pressureNeumannL2Multiplier
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := pressureNeumannL2MultiplierFun μ C hC M hBound
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards
          [pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound (f + g),
           pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound f,
           pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound g,
           Lp.coeFn_add f g,
           Lp.coeFn_add
             (pressureNeumannL2MultiplierFun μ C hC M hBound f)
             (pressureNeumannL2MultiplierFun μ C hC M hBound g)]
          with x hfg hf hg hsum hout
        change (pressureNeumannL2MultiplierFun μ C hC M hBound (f + g)) x =
          ((pressureNeumannL2MultiplierFun μ C hC M hBound f +
            pressureNeumannL2MultiplierFun μ C hC M hBound g) : Lp E 2 μ) x
        calc
          _ = C x ((f + g) x) := hfg
          _ = C x (f x) + C x (g x) := by rw [hsum, Pi.add_apply, map_add]
          _ = (pressureNeumannL2MultiplierFun μ C hC M hBound f) x +
              (pressureNeumannL2MultiplierFun μ C hC M hBound g) x := by
              rw [hf, hg]
          _ = _ := hout.symm
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards
          [pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound (c • f),
           pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound f,
           Lp.coeFn_smul c f,
           Lp.coeFn_smul c (pressureNeumannL2MultiplierFun μ C hC M hBound f)]
          with x hcf hf hsmul hout
        change (pressureNeumannL2MultiplierFun μ C hC M hBound (c • f)) x =
          ((c • pressureNeumannL2MultiplierFun μ C hC M hBound f) : Lp E 2 μ) x
        calc
          _ = C x ((c • f) x) := hcf
          _ = c • C x (f x) := by rw [hsmul, Pi.smul_apply, map_smul]
          _ = c • (pressureNeumannL2MultiplierFun μ C hC M hBound f) x := by rw [hf]
          _ = _ := hout.symm }
    M
    (by
      intro f
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards
        [pressure_neumann_l2_multiplier_fun_ae μ C hC M hBound f,
         hBound]
        with x hfx hCx
      change ‖(pressureNeumannL2MultiplierFun μ C hC M hBound f) x‖ ≤
        M * ‖f x‖
      rw [hfx]
      exact ((C x).le_opNorm (f x)).trans
        (mul_le_mul_of_nonneg_right hCx (norm_nonneg _)))

/-- The new bounded map agrees a.e. with pointwise multiplication. -/
theorem pressure_neumann_l2_multiplier_apply_ae
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M)
    (f : Lp E 2 μ) :
    (pressureNeumannL2Multiplier μ C hC M hM hBound f : Ω → E) =ᵐ[μ]
      fun x => C x (f x) := by
  exact MemLp.coeFn_toLp
    (pressure_neumann_l2_multiplier_mem μ C hC M hBound f)

/-- The global L² operator norm does not exceed the essential pointwise bound. -/
theorem pressure_neumann_l2_multiplier_norm_le
    (μ : Measure Ω) (C : Ω → E →L[ℝ] E)
    (hC : AEStronglyMeasurable C μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M) :
    ‖pressureNeumannL2Multiplier μ C hC M hM hBound‖ ≤ M := by
  exact LinearMap.mkContinuous_norm_le _ hM _

end GenericMultiplier

section PhysicalTensor

/-- Measurability of all nine physical tensor entries implies measurability
of the field of three-dimensional bounded coefficient endomorphisms. -/
theorem pressure_neumann_pointwise_field_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    Measurable (pressureNeumannPhysicalPointwiseCLM k eta beta) := by
  let A : Ω → Matrix (Fin 3) (Fin 3) ℝ :=
    fun x i j => pressurePhysicalTensor k eta beta x i j
  have hMatrix : Measurable A := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hTensor i j
  have hMatrixOp : Continuous
      (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
        Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A) := by
    exact LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  change Measurable (fun x : Ω =>
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (A x))
  exact hMatrixOp.measurable.comp hMatrix

/-- The ReservoirSeismicityControl coefficient now has an actual bounded L² multiplication
operator whenever the physical tensor is measurable and its operator norm
has a uniform essential bound. The latter bound is not postulated in the
PDE theorem: the next step is to prove it from the A3 ellipticity bounds. -/
noncomputable def pressureNeumannPhysicalL2TensorMultiplier
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j))
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖pressureNeumannPhysicalPointwiseCLM k eta beta x‖ ≤ M) :
    Lp (EuclideanSpace ℝ (Fin 3)) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin 3)) 2 μ :=
  pressureNeumannL2Multiplier μ
    (pressureNeumannPhysicalPointwiseCLM k eta beta)
    (pressure_neumann_pointwise_field_measurable k eta beta hTensor).aestronglyMeasurable
    M hM hBound

end PhysicalTensor

end ReservoirSeismicityControl
