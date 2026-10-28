import ReservoirSeismicityControl.PressureScalarMild
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Appendix A.1: projection of a strong diffusion evolution onto a scalar mode

Let `pressure : ℝ → H` satisfy an abstract Hilbert-space diffusion evolution
at the times under consideration. The diffusion term is an `H`-valued
function along the trajectory, not a bounded operator on all of `H`.

A continuous linear functional `test : H →L[ℝ] ℝ` plays the role of
pairing with a fixed Neumann eigenfunction. The eigenfunction identity is
stated explicitly, as is the strong vector evolution equation.

These hypotheses give the scalar modal ODE and, on a time interval, its
variation-of-constants formula from Stage 25. Deriving the strong or weak
vector evolution, the Neumann eigenbasis, and the eigenfunction testing
identity from the concrete ReservoirSeismicityControl PDE remains a separate obligation.
No derivative of any well rate is needed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- A bounded linear observation commutes with a finite sum of vector-valued
well forcings. -/
theorem pressure_tested_multiwell_forcing
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {m : ℕ} (test : H →L[ℝ] ℝ)
    (diffusion : H) (source : Fin m → H) (Q : Fin m → ℝ) :
    test (-diffusion + ∑ j : Fin m, Q j • source j) =
      -(test diffusion) + ∑ j : Fin m, Q j * test (source j) := by
  simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul]

/-- A strong vector evolution and the spectral testing identity yield
exactly the modal ODE required by the scalar integrating-factor proof.
The diffusion operator need not be bounded on the ambient Hilbert space. -/
theorem pressure_modal_ode_from_vector_evolution
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {m : ℕ} (test : H →L[ℝ] ℝ)
    (lam t : ℝ) (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (heigen : test (diffusion t) = lam * test (pressure t))
    (hvector : HasDerivAt pressure
      (-diffusion t + ∑ j : Fin m, Q j t • source j) t) :
    HasDerivAt (fun s : ℝ => test (pressure s))
      (-lam * test (pressure t) +
        ∑ j : Fin m, Q j t * test (source j)) t := by
  have hproj : HasDerivAt (fun s : ℝ => test (pressure s))
      (test (-diffusion t + ∑ j : Fin m, Q j t • source j)) t := by
    simpa only [Function.comp_def] using
      (test.hasFDerivAt.comp_hasDerivAt t hvector)
  have hright : test (-diffusion t + ∑ j : Fin m, Q j t • source j) =
      -lam * test (pressure t) +
        ∑ j : Fin m, Q j t * test (source j) := by
    rw [pressure_tested_multiwell_forcing, heigen]
    simp only [neg_mul]
  rw [hright] at hproj
  exact hproj

/-- On a fixed time interval the vector evolution implies the actual
scalar mild formula for the tested mode. This requires strong evolution
at the interior times and interval integrability of the scalar forcing,
but NOT differentiability of any input. -/
theorem pressure_modal_mild_from_vector_evolution
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {m : ℕ} (test : H →L[ℝ] ℝ)
    (lam a b : ℝ) (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn pressure (Set.Icc a b))
    (heigen : ∀ s ∈ Set.Ioo a b,
      test (diffusion s) = lam * test (pressure s))
    (hvector : ∀ s ∈ Set.Ioo a b,
      HasDerivAt pressure
        (-diffusion s + ∑ j : Fin m, Q j s • source j) s)
    (hforcing : IntervalIntegrable
      (fun s : ℝ => ∑ j : Fin m, Q j s * test (source j)) volume a b) :
    test (pressure b) =
      Real.exp (-(lam * (b - a))) * test (pressure a) +
      (∫ s in a..b,
        Real.exp (-(lam * (b - s))) *
          (∑ j : Fin m, Q j s * test (source j))) := by
  have hcontMode : ContinuousOn
      (fun s : ℝ => test (pressure s)) (Set.Icc a b) :=
    test.continuous.comp_continuousOn' hcont
  have hode : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => test (pressure z))
        (-lam * test (pressure s) +
          ∑ j : Fin m, Q j s * test (source j)) s := by
    intro s hs
    exact pressure_modal_ode_from_vector_evolution
      test lam s pressure diffusion source Q
      (heigen s hs) (hvector s hs)
  exact pressure_scalar_mild_from_ode lam a b
    (fun s : ℝ => test (pressure s))
    (fun s : ℝ => ∑ j : Fin m, Q j s * test (source j))
    hab hcontMode hode hforcing

/-- The lam-scaled mild formula matches the exponential convolution
kernel whose mass was established in Stage 24. -/
theorem pressure_modal_scaled_mild_from_vector_evolution
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {m : ℕ} (test : H →L[ℝ] ℝ)
    (lam a b : ℝ) (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn pressure (Set.Icc a b))
    (heigen : ∀ s ∈ Set.Ioo a b,
      test (diffusion s) = lam * test (pressure s))
    (hvector : ∀ s ∈ Set.Ioo a b,
      HasDerivAt pressure
        (-diffusion s + ∑ j : Fin m, Q j s • source j) s)
    (hforcing : IntervalIntegrable
      (fun s : ℝ => ∑ j : Fin m, Q j s * test (source j)) volume a b) :
    lam * test (pressure b) =
      Real.exp (-(lam * (b - a))) * (lam * test (pressure a)) +
      (∫ s in a..b,
        (lam * Real.exp (-(lam * (b - s)))) *
          (∑ j : Fin m, Q j s * test (source j))) := by
  have hcontMode : ContinuousOn
      (fun s : ℝ => test (pressure s)) (Set.Icc a b) :=
    test.continuous.comp_continuousOn' hcont
  have hode : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => test (pressure z))
        (-lam * test (pressure s) +
          ∑ j : Fin m, Q j s * test (source j)) s := by
    intro s hs
    exact pressure_modal_ode_from_vector_evolution
      test lam s pressure diffusion source Q
      (heigen s hs) (hvector s hs)
  exact pressure_scalar_scaled_mild_from_ode lam a b
    (fun s : ℝ => test (pressure s))
    (fun s : ℝ => ∑ j : Fin m, Q j s * test (source j))
    hab hcontMode hode hforcing

end ReservoirSeismicityControl
