import ReservoirSeismicityControl.Paper2026.PhysicalA9FullLineW11Inputs20261025
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Tactic

/-!
# Physical A9: from global W1,1 approximation to every translated convolution input

The actual projected Neumann kernel and its rate are full-line L1 by the
previous theorem. The standard external Banach-valued W1,1 density theorem
constructs compactly supported C1 approximants with GLOBAL L1 errors for
both values and derivatives.

This module derives ALL eight previously separate convolution Bochner /
translated-error premises from that global data, using precisely the
Lebesgue reflection s -> t-s. Hence no observation-time-dependent
approximation or unproved differentiation statement is assumed.

The genuine external step is obtaining the global W1,1 density
approximants from the physical positive-lag semigroup derivative, L1 bounds
and zero trace. No Qdot is required.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 2000000

/-- Change of variables on the whole real line for the physical convolution
reflection. This is Lebesgue-measure preservation, not an assumption on
translated norms. -/
theorem paper_A9_whole_line_reflected_integral
    (f : ℝ → ℝ) (t : ℝ) :
    (∫ s : ℝ, f (t - s)) = ∫ s : ℝ, f s := by
  exact ((volume : Measure ℝ).measurePreserving_sub_left t).integral_comp
    (measurableEmbedding_subLeft t) f

/-- An integrable vector difference has an integrable reflected norm,
whose total L1 mass is exactly invariant under the reflection. -/
theorem paper_A9_whole_line_reflected_L1_error
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℝ → Lp ℝ 2 μ)
    (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ))
    (t : ℝ) :
    Integrable (fun s : ℝ => ‖f (t - s) - g (t - s)‖)
      (volume : Measure ℝ) ∧
    (∫ s : ℝ, ‖f (t - s) - g (t - s)‖) =
      ∫ s : ℝ, ‖f s - g s‖ := by
  have hDiff : Integrable (fun s : ℝ => f s - g s)
      (volume : Measure ℝ) := hf.sub hg
  constructor
  · exact (paper_A9_full_line_L1_reflected μ
      (fun s => f s - g s) hDiff t).norm
  · exact paper_A9_whole_line_reflected_integral
      (fun s : ℝ => ‖f s - g s‖) t

/-- All eight physical full-line convolution hypotheses that formerly had
to be supplied independently are now consequences of global L1 data and
global W1,1 approximation errors. The only approximation inputs are the
value/rate integrability of smooth approximants and TWO unshifted L1
error estimates, both supplied by standard W1,1 density.

The resulting conclusions exactly match the existing PASSED theorem
`paper_A9_four_terms_from_projected_W11_and_physical_SR`.
-/
theorem paper_A9_global_W11_density_disposes_of_translated_assumptions
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (q : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (q j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |q j s| ≤ M j)
    (hKernelInt : ∀ j : Fin m,
      Integrable (kernel j) (volume : Measure ℝ))
    (hRateInt : ∀ j : Fin m,
      Integrable (rate j) (volume : Measure ℝ))
    (hKnInt : ∀ (n : ℕ) (j : Fin m),
      Integrable (kn n j) (volume : Measure ℝ))
    (hKnRateInt : ∀ (n : ℕ) (j : Fin m),
      Integrable (fun s : ℝ => deriv (kn n j) s) (volume : Measure ℝ))
    (errValue errRate : Fin m → ℕ → ℝ)
    (hErrorValue : ∀ (j : Fin m) (n : ℕ),
      (∫ s : ℝ, ‖kn n j s - kernel j s‖) ≤ errValue j n)
    (hErrorRate : ∀ (j : Fin m) (n : ℕ),
      (∫ s : ℝ, ‖deriv (kn n j) s - rate j s‖) ≤ errRate j n) :
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => q j s • kernel j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      Integrable (fun s : ℝ => q j s • kn n j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (t : ℝ),
      Integrable (fun s : ℝ => q j s • rate j (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      Integrable (fun s : ℝ => q j s • deriv (kn n j) (t - s))
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      Integrable (fun s : ℝ =>
        ‖kn n j (t - s) - kernel j (t - s)‖)
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      (∫ s : ℝ, ‖kn n j (t - s) - kernel j (t - s)‖)
        ≤ errValue j n) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      Integrable (fun s : ℝ =>
        ‖deriv (kn n j) (t - s) - rate j (t - s)‖)
        (volume : Measure ℝ)) ∧
    (∀ (j : Fin m) (n : ℕ) (t : ℝ),
      (∫ s : ℝ, ‖deriv (kn n j) (t - s) - rate j (t - s)‖)
        ≤ errRate j n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (q j)
      (kernel j) (hqMeas j) (hKernelInt j) (M j) (hqBound j) t
  · intro j n t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (q j)
      (kn n j) (hqMeas j) (hKnInt n j) (M j) (hqBound j) t
  · intro j t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (q j)
      (rate j) (hqMeas j) (hRateInt j) (M j) (hqBound j) t
  · intro j n t
    exact paper_A9_bounded_flux_times_full_line_L1 μ (q j)
      (fun s => deriv (kn n j) s) (hqMeas j)
      (hKnRateInt n j) (M j) (hqBound j) t
  · intro j n t
    exact (paper_A9_whole_line_reflected_L1_error μ
      (kn n j) (kernel j) (hKnInt n j) (hKernelInt j) t).1
  · intro j n t
    calc
      (∫ s : ℝ, ‖kn n j (t - s) - kernel j (t - s)‖) =
        (∫ s : ℝ, ‖kn n j s - kernel j s‖) :=
          (paper_A9_whole_line_reflected_L1_error μ
            (kn n j) (kernel j) (hKnInt n j) (hKernelInt j) t).2
      _ ≤ errValue j n := hErrorValue j n
  · intro j n t
    exact (paper_A9_whole_line_reflected_L1_error μ
      (fun s => deriv (kn n j) s) (rate j)
      (hKnRateInt n j) (hRateInt j) t).1
  · intro j n t
    calc
      (∫ s : ℝ, ‖deriv (kn n j) (t - s) - rate j (t - s)‖) =
        (∫ s : ℝ, ‖deriv (kn n j) s - rate j s‖) :=
          (paper_A9_whole_line_reflected_L1_error μ
            (fun s => deriv (kn n j) s) (rate j)
            (hKnRateInt n j) (hRateInt j) t).2
      _ ≤ errRate j n := hErrorRate j n

#print axioms paper_A9_whole_line_reflected_integral
#print axioms paper_A9_whole_line_reflected_L1_error
#print axioms paper_A9_global_W11_density_disposes_of_translated_assumptions

end ReservoirSeismicityControl.Paper2026
