import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ProjectedDerivative
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Appendix A.3 / (A9): actual far projection of the truncated mild forcing

This specializes the existing L² far-indicator projection and its smooth
SR observation-weight identity to the *finite-well, positive-lag* part of
the Neumann mild pressure formula.

Truncating at lag ε > 0 avoids assuming that the unprojected operator orbit
`A exp(-lag A) B_j` has an integrable norm down to lag 0. The existing cited
analytic Neumann semigroup result supplies Bochner integrability on a
strictly positive-lag interval; it is listed as `hInt` rather than proved
again here. No derivative of the well flux Q is used.

What this does NOT prove: passage ε ↓ 0 to `P (A p(t))`, or the time
derivative and causal formula of (A9). Those are remaining physical
identification obligations, not assumptions hidden in this module.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- The physical sharp far projection commutes with a *truncated*
finite-well Neumann generator-orbit Bochner integral. -/
theorem paper_A9_physical_truncated_generator_projection
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Q : Fin n → ℝ → ℝ)
    (initial : Lp ℝ 2 μ) (t ε : ℝ)
    (hInt : Integrable
      (fun s : ℝ => ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t - ε)))) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    P (initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε),
      ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))) =
    P initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε),
      P (∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))) := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let forcing : ℝ → Lp ℝ 2 μ := fun s =>
    ∑ j : Fin n, (Q j s) •
      ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))
  have hcomm := ContinuousLinearMap.integral_comp_comm P hInt
  change P (initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s) =
      P initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), P (forcing s)
  rw [map_add, hcomm]

/-- For the actual smooth cutoff (1-ζ) times the normalized SR weight,
its pairing with the truncated mild term is *exactly* its pairing with
the projected finite-well forcing. The fact that ζ multiplies the physical
SR weight is the sole cutoff-realization premise; nothing about Q̇. -/
theorem paper_A9_physical_truncated_SR_observation
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (ζ : X → ℝ) (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Q : Fin n → ℝ → ℝ)
    (initial : Lp ℝ 2 μ) (t ε : ℝ)
    (hInt : Integrable
      (fun s : ℝ => ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (t - ε)))) :
    let w := paperSRFarDiffusionWeight μ region hregion Kγ R
      gamma10 R0star cutoff t
    let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
    ⟪w, initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε),
      ∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))⟫_ℝ =
    ⟪w, P initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε),
      P (∑ j : Fin n, (Q j s) •
        ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))⟫_ℝ := by
  let w : Lp ℝ 2 μ :=
    paperSRFarDiffusionWeight μ region hregion Kγ R gamma10 R0star cutoff t
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let forcing : ℝ → Lp ℝ 2 μ := fun s =>
    ∑ j : Fin n, (Q j s) •
      ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))
  have hfixed : P w = w :=
    paper_sr_smooth_far_projection_nonunit_set
      μ region hregion Kγ R gamma10 R0star cutoff ζ hfar hcutoff t
  have hpair :
      ⟪w, initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s⟫_ℝ =
      ⟪w, P (initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s)⟫_ℝ :=
    ReservoirSeismicityControl.paper_far_projected_inner P
      (ReservoirSeismicityControl.paper_far_lp_projection_selfAdjoint
        μ {x : X | ζ x ≠ 1} hfar)
      w _ hfixed
  have hproject :
      P (initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s) =
      P initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), P (forcing s) :=
    paper_A9_physical_truncated_generator_projection
      μ {x : X | ζ x ≠ 1} hfar V E hsep orbit Q initial t ε hInt
  change ⟪w, initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s⟫_ℝ =
    ⟪w, P initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), P (forcing s)⟫_ℝ
  calc
    _ = ⟪w, P (initial + ∫ s in Set.Ioc (0 : ℝ) (t - ε), forcing s)⟫_ℝ := hpair
    _ = _ := by rw [hproject]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_truncated_generator_projection
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_truncated_SR_observation
