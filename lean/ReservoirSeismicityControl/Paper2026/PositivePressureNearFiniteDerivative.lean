import ReservoirSeismicityControl.Paper2026.PositivePressureNearDerivative
import ReservoirSeismicityControl.Paper2026.PositivePhysicalNearValue
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: finite-dimensional pressure near-field DERIVATIVE

This module finishes the finite-output assembly for the *fixed pressure*
weights `ζ χ_(V_ui) / |V_ui|` occurring in (14) and Appendix A.3.
It specializes the previously PASSED pressure-channel derivative theorem
and sums the results in the canonical pressure output coordinates.

The observed pressure diffusion is `A (p(t))`, for the same symmetric,
unbounded Neumann generator and its explicit domain. No derivative of A p,
well flux Q, or other unmentioned regularity is assumed. The smooth-cutoff
membership and generator bounds remain explicit applicability conditions
of the paper's cited local elliptic result. The MOVING SR near term is not
claimed to be differentiable by this module.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Pressure contribution to the already verified full physical near-field
perturbation `paperPhysicalFiniteNearPsi`. In particular, `Ap` is NOT
postulated to have a time derivative. -/
noncomputable def paperPhysicalPressureNearPsi
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X) (regions : Fin u → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (hFin : ∀ i, mu (regions i) ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Ap : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
    (-⟪paperPressureNearWeight mu (regions i) (hMeas i) (hFin i) cutoff,
      Ap t⟫_ℝ)

/-- The pressure part of the A.3 near-field weak derivative, written
using the actual fixed localized pressure weights in the Neumann domain. -/
noncomputable def paperPhysicalPressureNearRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X) (regions : Fin u → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (hFin : ∀ i, mu (regions i) ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hWeightD : ∀ i, paperPressureNearWeight mu (regions i)
      (hMeas i) (hFin i) cutoff ∈ D)
    (pressureRate : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
    (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
        (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)

/-- Direct identification with the PRESSURE summand of the already
verified actual finite near-field perturbation from equation (14). -/
theorem paper_physical_near_pressure_component_eq
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X)
    (pressureRegions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pressureRegions i))
    (hpFin : ∀ i, mu (pressureRegions i) ≠ ⊤)
    (srRegions : Fin r → Set X)
    (hsMeas : ∀ i, MeasurableSet (srRegions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R : ℝ → Lp ℝ 2 mu) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Ap : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    paperPhysicalFiniteNearPsi mu pressureRegions hpMeas hpFin srRegions
      hsMeas Kgamma R gamma10 R0star cutoff Ap t =
    paperPhysicalPressureNearPsi mu pressureRegions hpMeas hpFin cutoff Ap t +
      (∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
        (-⟪paperSRNearDiffusionWeight mu (srRegions i) (hsMeas i)
          Kgamma R gamma10 R0star cutoff t, Ap t⟫_ℝ)) := by
  rfl

/-- The fixed-pressure part of the exact A.3 finite-dimensional near
observation has the stated weak/a.e. derivative and a constructive norm
bound. This consumes the previously verified one-region derivative and
Cauchy--Schwarz certificates; no new functional-analysis result is proved.
The ONLY operator-domain hypotheses concern the actual localized weights. -/
theorem paper_physical_pressure_near_finite_derivative_ae
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X) (regions : Fin u → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (hFin : ∀ i, mu (regions i) ≠ ⊤)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hSymm : ∀ a b : D,
      ⟪A a, (b : Lp ℝ 2 mu)⟫_ℝ = ⟪(a : Lp ℝ 2 mu), A b⟫_ℝ)
    (pressure pressureRate : ℝ → Lp ℝ 2 mu)
    (hpD : ∀ t, pressure t ∈ D)
    (hWeightD : ∀ i, paperPressureNearWeight mu (regions i)
      (hMeas i) (hFin i) cutoff ∈ D)
    (CAw : Fin u → ℝ) (CPt : ℝ)
    (hAw : ∀ i, ‖A ⟨paperPressureNearWeight mu (regions i)
      (hMeas i) (hFin i) cutoff, hWeightD i⟩‖ ≤ CAw i)
    (hpRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt pressure (pressureRate t) t)
    (hPt : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖pressureRate t‖ ≤ CPt) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperPhysicalPressureNearPsi (r := r) mu regions hMeas hFin cutoff
          (fun τ => A ⟨pressure τ, hpD τ⟩))
        (paperPhysicalPressureNearRate (r := r) mu regions hMeas hFin cutoff
          D A hWeightD pressureRate t) t ∧
      ‖paperPhysicalPressureNearRate (r := r) mu regions hMeas hFin cutoff
          D A hWeightD pressureRate t‖ ≤
        ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
          (CAw i * CPt) := by
  classical
  filter_upwards [hpRate, hPt] with t ht hPt'
  have hScalar (i : Fin u) :
      HasDerivAt
        (fun τ => -⟪paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, A ⟨pressure τ, hpD τ⟩⟫_ℝ)
        (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ) t :=
    paper_pressure_near_observation_hasDerivAt mu (regions i)
      (hMeas i) (hFin i) cutoff D A hSymm pressure pressureRate
      hpD (hWeightD i) t ht
  have hCoordinate (i : Fin u) :
      HasDerivAt
        (fun τ => paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, A ⟨pressure τ, hpD τ⟩⟫_ℝ))
        (paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)) t :=
    (paperPressureCoordinateEmbed (u := u) (r := r) i).hasFDerivAt.comp_hasDerivAt
      t (hScalar i)
  have hDeriv : HasDerivAt
      (paperPhysicalPressureNearPsi (r := r) mu regions hMeas hFin cutoff
        (fun τ => A ⟨pressure τ, hpD τ⟩))
      (paperPhysicalPressureNearRate (r := r) mu regions hMeas hFin cutoff
        D A hWeightD pressureRate t) t := by
    change HasDerivAt
      (fun τ => ∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
        (-⟪paperPressureNearWeight mu (regions i) (hMeas i)
          (hFin i) cutoff, A ⟨pressure τ, hpD τ⟩⟫_ℝ))
      (∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
        (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
          (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)) t
    apply HasDerivAt.fun_sum
    intro i _
    exact hCoordinate i
  have hBound : ‖paperPhysicalPressureNearRate (r := r) mu regions hMeas hFin cutoff
      D A hWeightD pressureRate t‖ ≤
        ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
          (CAw i * CPt) := by
    unfold paperPhysicalPressureNearRate
    calc
      ‖∑ i : Fin u, paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)‖
        ≤ ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i
          (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
          abs (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
            (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [Real.norm_eq_abs] using
            (paperPressureCoordinateEmbed (u := u) (r := r) i).le_opNorm
              (-⟪A ⟨paperPressureNearWeight mu (regions i) (hMeas i)
                (hFin i) cutoff, hWeightD i⟩, pressureRate t⟫_ℝ)
      _ ≤ ∑ i : Fin u, ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
          (CAw i * CPt) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact paper_pressure_near_derivative_bound mu (regions i)
            (hMeas i) (hFin i) cutoff D A (hWeightD i)
            (CAw i) CPt (hAw i) (pressureRate t) hPt'
  exact ⟨hDeriv, hBound⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_pressure_near_finite_derivative_ae

#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_near_pressure_component_eq
