import ReservoirSeismicityControl.Paper2026.PhysicalA9W11ManuscriptApplicability20261025
import Mathlib.Tactic

/-!
# Physical A9: positive-lag projected-vector kernel, from existing Neumann results

This is the physical vector (not scalar) specialization required by A9.
It uses the ALREADY established weak-Neumann orbit differentiation and the
manuscript-cited off-diagonal envelopes.  It establishes the actual projected
kernel's positive-lag derivative, both positive-lag L¹ bounds, zero extension,
and the zero-lag limit. No reproof of the kernel, Neumann generator,
or Davies--Gaffney theory. No hypothesis on Qdot.

External analytic inputs are exactly the measurable projected orbits and
Davies--Gaffney majorants B₀ and B₁, with their positive-lag integrability
and B₀ -> 0 at zero. The full-line W¹,¹ smooth density/application to the
vector-convolution theorem is a separate standard Sobolev input.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 2000000

/-- Apply the previously verified positive-lag Neumann-orbit derivative to
its *physical far-field projection*. This is an L²-valued result, not a
scalar kernel estimate. -/
theorem paper_A9_physical_projected_vector_lag_derivative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ}
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (j : Fin m) (lag : ℝ) (hlag : 0 < lag) :
    HasDerivAt
      (fun τ => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ)))
      (-(ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag))) lag := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  change HasDerivAt
    (fun τ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ)))
    (-(P (second j lag))) lag
  have hcomp := P.hasFDerivAt.comp_hasDerivAt lag (hOrbit j lag hlag)
  change HasDerivAt
    (fun τ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ)))
    (P (-(second j lag))) lag at hcomp
  simpa only [map_neg] using hcomp

/-- The precise physical projected vector kernels and their positive-lag L¹
properties. The zero extensions ensure the correct causal support. This
turns off-diagonal *norm envelopes*, rather than derivative assumptions about
the convolution, into the analytic vector data needed for (A9).

The two measurability premises are standard consequences of positive-lag
analytic semigroup regularity; they do not assert integrability or a time
rate of the forcing. -/
theorem paper_A9_physical_vector_kernel_positive_L1_from_DG
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ}
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (B₀ B₁ : Fin m → ℝ → ℝ)
    (hB₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₀ j lag)
    (hB₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₁ j lag)
    (hDG₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))‖
        ≤ B₀ j lag)
    (hDG₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag)‖
        ≤ B₁ j lag)
    (hB₀Int : ∀ j : Fin m,
      Integrable (B₀ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₁Int : ∀ j : Fin m,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₀Zero : ∀ j : Fin m,
      Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hOrbitMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSecondMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag))
        (volume.restrict (Set.Ioi (0 : ℝ)))) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      else 0
    let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    (∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt (kernel j) (rate j lag) lag) ∧
    (∀ j : Fin m, Integrable (kernel j)
      (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∀ j : Fin m, Integrable (rate j)
      (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∀ j : Fin m, Tendsto (kernel j)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Lp ℝ 2 μ))) ∧
    (∀ (j : Fin m) (lag : ℝ), lag ≤ 0 →
      kernel j lag = 0 ∧ rate j lag = 0) := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  change
    (∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt (kernel j) (rate j lag) lag) ∧
    (∀ j : Fin m, Integrable (kernel j)
      (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∀ j : Fin m, Integrable (rate j)
      (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∀ j : Fin m, Tendsto (kernel j)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Lp ℝ 2 μ))) ∧
    (∀ (j : Fin m) (lag : ℝ), lag ≤ 0 →
      kernel j lag = 0 ∧ rate j lag = 0)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j lag hlag
    have hraw : HasDerivAt
        (fun τ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ)))
        (-(P (second j lag))) lag :=
      paper_A9_physical_projected_vector_lag_derivative μ far hfar
        V E hsep orbit second hOrbit j lag hlag
    have hlocal : (kernel j) =ᶠ[𝓝 lag]
        (fun τ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hlag] with τ hτ
      change (if 0 < τ then
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ))
          else 0) = P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j τ))
      exact if_pos hτ
    have hrate : rate j lag = -(P (second j lag)) := by
      change (if 0 < lag then -(P (second j lag)) else 0) = -(P (second j lag))
      exact if_pos hlag
    rw [hrate]
    exact hraw.congr_of_eventuallyEq hlocal
  · intro j
    let μpos : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
    have hRaw : Integrable
        (fun lag => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        μpos := by
      apply (hB₀Int j).mono' (hOrbitMeas j)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      have h := hDG₀ j lag hlag
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hB₀ j lag hlag)] using h
    have hEq : (kernel j) =ᵐ[μpos]
        (fun lag => P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      change (if 0 < lag then
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
          else 0) = P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      exact if_pos hlag
    exact hRaw.congr hEq.symm
  · intro j
    let μpos : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
    have hRaw : Integrable
        (fun lag => P (second j lag)) μpos := by
      apply (hB₁Int j).mono' (hSecondMeas j)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      have h := hDG₁ j lag hlag
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hB₁ j lag hlag)] using h
    have hEq : (rate j) =ᵐ[μpos]
        (fun lag => -(P (second j lag))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      change (if 0 < lag then -(P (second j lag)) else 0) = -(P (second j lag))
      exact if_pos hlag
    exact hRaw.neg.congr hEq.symm
  · intro j
    apply squeeze_zero_norm' ?_ (hB₀Zero j)
    filter_upwards [self_mem_nhdsWithin] with lag hlag
    have h := hDG₀ j lag hlag
    have hkernel : kernel j lag =
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)) := by
      change (if 0 < lag then
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
          else 0) = P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      exact if_pos hlag
    rw [hkernel]
    exact h
  · intro j lag hlag
    have hn : ¬ 0 < lag := not_lt.mpr hlag
    simp [kernel, rate, hn]

#print axioms paper_A9_physical_projected_vector_lag_derivative
#print axioms paper_A9_physical_vector_kernel_positive_L1_from_DG

end ReservoirSeismicityControl.Paper2026
