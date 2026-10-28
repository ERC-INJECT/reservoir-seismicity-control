import ReservoirSeismicityControl.PressureStrongModalProjection
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Appendix A.1: spectral testing for a symmetric operator with an explicit domain

A Neumann diffusion operator is generally unbounded on the ambient L² space.
We therefore model its domain as a submodule `D` of a real inner-product
space `H`, and its action as a linear map `A : D →ₗ[ℝ] H`.

If `A` is symmetric on `D` and an eigenvector `e : D` satisfies
`A e = lam • e`, testing `A p` against `e` yields the spectral testing
identity needed in Stage 26. The continuous linear testing functional is
the actual inner product with `e`, not an arbitrary functional.

The subsequent modal ODE and mild formula still assume a strong vector
pressure evolution and that the diffusion term equals `A` on domain-valued
pressure states. Showing these assumptions for the concrete variable-
coefficient Neumann PDE (and for measurable/ZOH forcing) is separate work.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

/-- Symmetry of a possibly unbounded operator on its domain, together with
an eigenvector equation, supplies the spectral testing identity. The
testing map is the bounded functional `v ↦ ⟪e, v⟫_ℝ`. -/
theorem pressure_symmetric_eigen_test
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ)
    (e : D) (lam : ℝ)
    (heig : A e = lam • (e : H)) (p : D) :
    ((innerSL ℝ) (e : H)) (A p) =
      lam * ((innerSL ℝ) (e : H)) (p : H) := by
  simp only [innerSL_apply_apply]
  calc
    ⟪(e : H), A p⟫_ℝ = ⟪A p, (e : H)⟫_ℝ := real_inner_comm _ _
    _ = ⟪(p : H), A e⟫_ℝ := hSymm p e
    _ = ⟪(p : H), lam • (e : H)⟫_ℝ := by rw [heig]
    _ = lam * ⟪(p : H), (e : H)⟫_ℝ := by rw [real_inner_smul_right]
    _ = lam * ⟪(e : H), (p : H)⟫_ℝ := by rw [real_inner_comm (p : H) (e : H)]

/-- The modal ODE follows from a strong vector evolution and the
explicit-domain symmetry/eigenvector assumptions, instead of postulating
Stage 26's spectral testing identity. -/
theorem pressure_modal_ode_from_symmetric_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ)
    (e : D) (lam t : ℝ)
    (heig : A e = lam • (e : H))
    (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (hmem : pressure t ∈ D)
    (hDiffusion : diffusion t = A ⟨pressure t, hmem⟩)
    (hvector : HasDerivAt pressure
      (-diffusion t + ∑ j : Fin m, Q j t • source j) t) :
    HasDerivAt (fun s : ℝ => ((innerSL ℝ) (e : H)) (pressure s))
      (-lam * ((innerSL ℝ) (e : H)) (pressure t) +
        ∑ j : Fin m, Q j t * ((innerSL ℝ) (e : H)) (source j)) t := by
  let test : H →L[ℝ] ℝ := (innerSL ℝ) (e : H)
  have heigen : test (diffusion t) = lam * test (pressure t) := by
    rw [hDiffusion]
    exact pressure_symmetric_eigen_test D A hSymm e lam heig ⟨pressure t, hmem⟩
  exact pressure_modal_ode_from_vector_evolution
    test lam t pressure diffusion source Q heigen hvector

/-- The scalar variation-of-constants formula follows from symmetry of
`A` and its eigenvector equation on every interior time, assuming the
strong vector evolution, interval continuity and integrability. -/
theorem pressure_modal_mild_from_symmetric_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ)
    (e : D) (lam a b : ℝ)
    (heig : A e = lam • (e : H))
    (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn pressure (Set.Icc a b))
    (hDomain : ∀ s ∈ Set.Ioo a b,
      ∃ p : D, (p : H) = pressure s ∧ diffusion s = A p)
    (hvector : ∀ s ∈ Set.Ioo a b,
      HasDerivAt pressure
        (-diffusion s + ∑ j : Fin m, Q j s • source j) s)
    (hforcing : IntervalIntegrable
      (fun s : ℝ => ∑ j : Fin m,
        Q j s * ((innerSL ℝ) (e : H)) (source j)) volume a b) :
    ((innerSL ℝ) (e : H)) (pressure b) =
      Real.exp (-(lam * (b - a))) * ((innerSL ℝ) (e : H)) (pressure a) +
      (∫ s in a..b,
        Real.exp (-(lam * (b - s))) *
          (∑ j : Fin m,
            Q j s * ((innerSL ℝ) (e : H)) (source j))) := by
  let test : H →L[ℝ] ℝ := (innerSL ℝ) (e : H)
  have heigen : ∀ s ∈ Set.Ioo a b,
      test (diffusion s) = lam * test (pressure s) := by
    intro s hs
    obtain ⟨p, hp, hAp⟩ := hDomain s hs
    rw [hAp, ← hp]
    exact pressure_symmetric_eigen_test D A hSymm e lam heig p
  exact pressure_modal_mild_from_vector_evolution
    test lam a b pressure diffusion source Q
    hab hcont heigen hvector hforcing

/-- The scaled mild formula has the same exponential convolution kernel
whose exact mass was verified in Stage 24. -/
theorem pressure_modal_scaled_mild_from_symmetric_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hSymm : ∀ u v : D,
      ⟪A u, (v : H)⟫_ℝ = ⟪(u : H), A v⟫_ℝ)
    (e : D) (lam a b : ℝ)
    (heig : A e = lam • (e : H))
    (pressure diffusion : ℝ → H)
    (source : Fin m → H) (Q : Fin m → ℝ → ℝ)
    (hab : a ≤ b)
    (hcont : ContinuousOn pressure (Set.Icc a b))
    (hDomain : ∀ s ∈ Set.Ioo a b,
      ∃ p : D, (p : H) = pressure s ∧ diffusion s = A p)
    (hvector : ∀ s ∈ Set.Ioo a b,
      HasDerivAt pressure
        (-diffusion s + ∑ j : Fin m, Q j s • source j) s)
    (hforcing : IntervalIntegrable
      (fun s : ℝ => ∑ j : Fin m,
        Q j s * ((innerSL ℝ) (e : H)) (source j)) volume a b) :
    lam * ((innerSL ℝ) (e : H)) (pressure b) =
      Real.exp (-(lam * (b - a))) *
        (lam * ((innerSL ℝ) (e : H)) (pressure a)) +
      (∫ s in a..b,
        (lam * Real.exp (-(lam * (b - s)))) *
          (∑ j : Fin m,
            Q j s * ((innerSL ℝ) (e : H)) (source j))) := by
  let test : H →L[ℝ] ℝ := (innerSL ℝ) (e : H)
  have heigen : ∀ s ∈ Set.Ioo a b,
      test (diffusion s) = lam * test (pressure s) := by
    intro s hs
    obtain ⟨p, hp, hAp⟩ := hDomain s hs
    rw [hAp, ← hp]
    exact pressure_symmetric_eigen_test D A hSymm e lam heig p
  exact pressure_modal_scaled_mild_from_vector_evolution
    test lam a b pressure diffusion source Q
    hab hcont heigen hvector hforcing

end ReservoirSeismicityControl
