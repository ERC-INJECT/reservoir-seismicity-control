import ReservoirSeismicityControl.PaperA5ProfileStability
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Stage 66: temporal continuity of regularized Neumann Volterra convolutions

For a fixed spatial vector `g = A f` and a merely integrable well rate
`q : ℝ → ℝ`, we show that the regularized causal semigroup convolution
is continuous. There is no differentiability assumption on `q`.

The key is the decomposition of the causal operator kernel into

  1_{τ ≥ 0} S(τ) g = 1_{τ ≥ 0} g + (S(max(τ,0)) g - g).

The second term, extended by zero to negative `τ`, is a continuous and
bounded `H`-valued function. The continuous convolution theorem for an
integrable scalar input and a bounded continuous vector kernel applies.
The first term becomes the ordinary continuous integral primitive.

This source proves continuity of that two-term representation. The
identification with the *actual finite-horizon forward Bochner-Duhamel
integral*, generator commutation `A∫S f q = ∫S Af q`, and the localization
of locally integrable rates to finite horizons are separate obligations.
The profile approximation and uniform limit are Stages 65 and 64.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal Convolution

section RegularizedConvolution

variable {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

/-- Causal semigroup kernel with the jump at time zero removed. Since
`Real.toNNReal τ = 0` for `τ ≤ 0`, this equals zero on negative time. -/
noncomputable def pressureA5RegularizedKernel
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (g : H) (τ : ℝ) : H :=
  S (Real.toNNReal τ) g - g

/-- The regularized kernel is strongly continuous on the whole real line. -/
theorem pressure_A5_regularized_kernel_continuous
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (g : H) :
    Continuous (pressureA5RegularizedKernel S g) := by
  unfold pressureA5RegularizedKernel
  exact (S.continuous_operator_toNNReal g).sub continuous_const

/-- Its norm is uniformly bounded by twice the source norm. -/
theorem pressure_A5_regularized_kernel_norm_le
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (g : H) (τ : ℝ) :
    ‖pressureA5RegularizedKernel S g τ‖ ≤ 2 * ‖g‖ := by
  unfold pressureA5RegularizedKernel
  calc
    ‖S (Real.toNNReal τ) g - g‖ ≤ ‖S (Real.toNNReal τ) g‖ + ‖g‖ :=
      norm_sub_le _ _
    _ ≤ ‖g‖ + ‖g‖ := add_le_add (S.norm_apply_le _ g) le_rfl
    _ = 2 * ‖g‖ := by ring

/-- The regularized kernel satisfies the boundedness hypothesis of
Mathlib's convolution-continuity theorem. -/
theorem pressure_A5_regularized_kernel_bddAbove
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (g : H) :
    BddAbove (Set.range (fun τ : ℝ => ‖pressureA5RegularizedKernel S g τ‖)) := by
  refine ⟨2 * ‖g‖, ?_⟩
  rintro y ⟨τ, rfl⟩
  exact pressure_A5_regularized_kernel_norm_le S g τ

/-- Convolution of an integrable real well rate with the regularized
strongly continuous contraction-semigroup kernel is continuous. -/
theorem pressure_A5_regularized_convolution_continuous
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (q : ℝ → ℝ) (hq : Integrable q (volume : Measure ℝ)) (g : H) :
    Continuous (fun t : ℝ =>
      (q ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (pressureA5RegularizedKernel S g)) t) := by
  exact (pressure_A5_regularized_kernel_bddAbove S g).continuous_convolution_right_of_integrable
    (ContinuousLinearMap.lsmul ℝ ℝ) hq
    (pressure_A5_regularized_kernel_continuous S g)

/-- For a globally integrable well rate, the two pieces of the causal
semigroup convolution are both continuous. This is the key temporal
regularity lemma for the smooth-profile case `g = A f`.

A physical rate that is only locally integrable is handled on each
finite observation horizon by truncating it to that interval; matching
this formula with `pressureA5ForwardDuhamel` is the next task. -/
theorem pressure_A5_regularized_volterra_continuous
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (q : ℝ → ℝ) (hq : Integrable q (volume : Measure ℝ)) (g : H) :
    Continuous (fun t : ℝ =>
      (∫ s in (0 : ℝ)..t, q s) • g +
        (q ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (pressureA5RegularizedKernel S g)) t) := by
  have hprimitive : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, q s) :=
    hq.continuous_primitive 0
  exact (hprimitive.smul continuous_const).add
    (pressure_A5_regularized_convolution_continuous S q hq g)

end RegularizedConvolution

end ReservoirSeismicityControl
