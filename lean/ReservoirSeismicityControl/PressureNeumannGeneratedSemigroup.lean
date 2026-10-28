import ReservoirSeismicityControl.PressureNeumannYosidaApproximations
import MarkovProcess.Semigroup.ResolventGeneration

/-!
# Block 70 — Hille–Yosida semigroup generation through a checked library

Constructs a genuine strongly continuous contraction semigroup for the
canonical Neumann resolvent, using Scott Armstrong's formalized Hille–Yosida
theorem in `MarkovProcess.Semigroup` (Apache-2.0).

The input `hDense` is the DENSE RANGE requirement of Hille–Yosida. It is
explicitly visible rather than hidden in an asserted heat semigroup.
It must ultimately be discharged from density of the physical H¹→L² inclusion
and symmetry/injectivity of the Neumann resolvent.

This module does NOT claim the domain-specific Davies–Gaffney or differentiated
heat estimates, or the physical Sobolev realization. No bound on Q derivatives
appears.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace
open MarkovProcess.Semigroup

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Supply the geometric dense-range condition separately. We do NOT assume a
pre-existing semigroup. -/
noncomputable def pressureNeumannContractiveResolvent
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam)) :
    ContractiveResolvent H where
  operator α := pressureNeumannCanonicalResolvent
    (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property
  resolvent_identity := by
    intro α β
    apply ContinuousLinearMap.ext
    intro f
    -- Use the swapped canonical identity, so the composition is R_α ∘ R_β.
    have h := pressure_neumann_canonical_resolvent_identity
      (β : ℝ) (α : ℝ) j B₁ E hB₁ hForm₁ hE β.property α.property f
    change
      pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f -
          pressureNeumannCanonicalResolvent (β : ℝ) j B₁ E hB₁ hForm₁ hE β.property f =
        ((β : ℝ) - (α : ℝ)) •
          pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property
            (pressureNeumannCanonicalResolvent (β : ℝ) j B₁ E hB₁ hForm₁ hE β.property f)
    calc
      _ = -(pressureNeumannCanonicalResolvent (β : ℝ) j B₁ E hB₁ hForm₁ hE β.property f -
            pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f) := by
          abel
      _ = -(((α : ℝ) - (β : ℝ)) •
            pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property
              (pressureNeumannCanonicalResolvent (β : ℝ) j B₁ E hB₁ hForm₁ hE β.property f)) := by
          rw [h]
      _ = _ := by module
  opNorm_le_inv := by
    intro α
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr α.property.le)
    intro f
    have h := pressure_neumann_canonical_resolvent_bound
      (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f
    change (α : ℝ) *
      ‖pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f‖
        ≤ ‖f‖ at h
    have hm :
      ‖pressureNeumannCanonicalResolvent (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f‖ *
        (α : ℝ) ≤ ‖f‖ := by simpa only [mul_comm] using h
    have hd := (le_div_iff₀ α.property).2 hm
    change ‖pressureNeumannCanonicalResolvent
      (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property f‖ ≤ (α : ℝ)⁻¹ * ‖f‖
    simpa only [div_eq_mul_inv, mul_comm] using hd
  denseRange α := hDense (α : ℝ) α.property

/-- A real C₀ contraction semigroup generated *from the constructed canonical
Neumann resolvent*, conditional only on its dense-range criterion. -/
noncomputable def pressureNeumannGeneratedSemigroup
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam)) :
    StronglyContinuousContractionSemigroup H :=
  (pressureNeumannContractiveResolvent j B₁ E hB₁ hForm₁ hE hDense).generatedSemigroup

/-- The generator domain is precisely the range of the canonical resolvent.
Thus the semigroup generator is tied to the SAME unbounded Neumann graph. -/
theorem pressure_neumann_generated_domain_eq_range
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam))
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    ((pressureNeumannGeneratedSemigroup j B₁ E hB₁ hForm₁ hE hDense).generatorDomain : Set H) =
      Set.range (pressureNeumannCanonicalResolvent (μ : ℝ) j B₁ E hB₁ hForm₁ hE μ.property) := by
  exact (pressureNeumannContractiveResolvent
    j B₁ E hB₁ hForm₁ hE hDense).generatorDomain_eq_range μ

/-- Identification of the semigroup generator on every resolvent image:
L(R_μ f)= μ R_μ f − f, so the *positive* Neumann operator is A=−L. -/
theorem pressure_neumann_generated_generator_on_resolvent
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam))
    (μ : MarkovProcess.Semigroup.PositiveShift) (f : H) :
    (pressureNeumannGeneratedSemigroup j B₁ E hB₁ hForm₁ hE hDense).generator
      ⟨pressureNeumannCanonicalResolvent (μ : ℝ) j B₁ E hB₁ hForm₁ hE μ.property f,
        (pressureNeumannContractiveResolvent
          j B₁ E hB₁ hForm₁ hE hDense).operator_mem_generatorDomain μ f⟩ =
      (μ : ℝ) • pressureNeumannCanonicalResolvent
        (μ : ℝ) j B₁ E hB₁ hForm₁ hE μ.property f - f := by
  exact (pressureNeumannContractiveResolvent
    j B₁ E hB₁ hForm₁ hE hDense).generator_operator_apply μ f

end ReservoirSeismicityControl
