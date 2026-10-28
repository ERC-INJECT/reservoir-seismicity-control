import ReservoirSeismicityControl.PaperA5WeakGeneratorIdentification
import Mathlib.Tactic

/-!
# Stage 76 — canonical weak Neumann realization on the image of the energy embedding

Stage 75 required an energy-preserving equivalence between a form Hilbert
space U and a represented L² test subspace V.  For the canonical realization
V := range j, that equivalence is constructed directly from injectivity of j.
The weak form is transported from Eform, so its energy correspondence is a
proved identity, not an independent assumption.

The resulting weak operator has the same domain as, and is the negative of,
the generator of the coercive-form semigroup.  No derivative of well rates
is assumed.  Identifying a desired concrete 3D Sobolev space with this image
and checking the physical tensor form are separate geometric obligations.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

section CanonicalWeakRange

variable {U H : Type*}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The form Hilbert space is canonically isomorphic to its image in L²
when the form embedding is injective. -/
noncomputable def pressureA5CanonicalFormRangeEquiv
    (j : U →L[ℝ] H) (hjinj : Function.Injective j) :
    U ≃ₗ[ℝ] LinearMap.range j.toLinearMap :=
  LinearEquiv.ofInjective j.toLinearMap hjinj

/-- The canonical equivalence preserves the ambient L² carrier. -/
theorem pressure_A5_canonical_form_range_carrier
    (j : U →L[ℝ] H) (hjinj : Function.Injective j) (x : U) :
    ((pressureA5CanonicalFormRangeEquiv j hjinj x :
       LinearMap.range j.toLinearMap) : H) = j x := by
  rfl

/-- Transport the original form energy to the actual image of j.
The two maps are algebraically linear, not asserted to be bounded with
respect to the weaker ambient L² topology. -/
noncomputable def pressureA5CanonicalRangeEnergy
    (j : U →L[ℝ] H) (Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hjinj : Function.Injective j) :
    (LinearMap.range j.toLinearMap) →ₗ[ℝ]
       (LinearMap.range j.toLinearMap) →ₗ[ℝ] ℝ := by
  let e := pressureA5CanonicalFormRangeEquiv j hjinj
  exact {
    toFun := fun v => (Eform (e.symm v)).toLinearMap.comp e.symm.toLinearMap
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro c x
      ext z
      simp
  }

/-- The transported weak energy agrees pointwise with the original form. -/
theorem pressure_A5_canonical_range_energy_eq
    (j : U →L[ℝ] H) (Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hjinj : Function.Injective j) (x y : U) :
    pressureA5CanonicalRangeEnergy j Eform hjinj
      (pressureA5CanonicalFormRangeEquiv j hjinj x)
      (pressureA5CanonicalFormRangeEquiv j hjinj y) = Eform x y := by
  change Eform
    ((pressureA5CanonicalFormRangeEquiv j hjinj).symm
       (pressureA5CanonicalFormRangeEquiv j hjinj x))
    ((pressureA5CanonicalFormRangeEquiv j hjinj).symm
       (pressureA5CanonicalFormRangeEquiv j hjinj y)) = Eform x y
  simp

/-- The image of the dense form embedding separates L² points. -/
theorem pressure_A5_canonical_range_separates
    (j : U →L[ℝ] H) (hjinj : Function.Injective j)
    (hjDense : DenseRange j) :
    ∀ g : H,
      (∀ v : LinearMap.range j.toLinearMap, ⟪g, (v : H)⟫_ℝ = 0) → g = 0 := by
  exact pressure_A5_dense_form_image_separates j hjDense
    (LinearMap.range j.toLinearMap)
    (pressureA5CanonicalFormRangeEquiv j hjinj)
    (pressure_A5_canonical_form_range_carrier j hjinj)

/-- The canonical transported weak Neumann operator is the negative
semigroup generator, without an operator-identification axiom or an
unproved form-space equivalence. -/
theorem pressure_A5_canonical_range_operator_eq_neg_generator
    (j : U →L[ℝ] H)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (x : pressureWeakNeumannDomain
      (LinearMap.range j.toLinearMap)
      (pressureA5CanonicalRangeEnergy j Eform hjinj))
    (hx : (((x : LinearMap.range j.toLinearMap) : H)) ∈
      (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain) :
    pressureWeakNeumannOperator
      (LinearMap.range j.toLinearMap)
      (pressureA5CanonicalRangeEnergy j Eform hjinj)
      (pressure_A5_canonical_range_separates j hjinj hjDense) x =
      -(pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator
        ⟨(((x : LinearMap.range j.toLinearMap) : H)), hx⟩ := by
  exact pressure_A5_dense_form_weak_operator_eq_neg_generator
    j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    (LinearMap.range j.toLinearMap)
    (pressureA5CanonicalRangeEnergy j Eform hjinj)
    (pressure_A5_canonical_range_separates j hjinj hjDense)
    (pressureA5CanonicalFormRangeEquiv j hjinj)
    (pressure_A5_canonical_form_range_carrier j hjinj)
    (pressure_A5_canonical_range_energy_eq j Eform hjinj) x hx

/-- The canonically constructed weak Neumann operator has exactly the
same ambient domain as the generator of the constructed semigroup. -/
theorem pressure_A5_canonical_range_domain_iff_generator_domain
    (j : U →L[ℝ] H)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (u : H) :
    (∃ x : pressureWeakNeumannDomain
      (LinearMap.range j.toLinearMap)
      (pressureA5CanonicalRangeEnergy j Eform hjinj),
        (((x : LinearMap.range j.toLinearMap) : H)) = u) ↔
      u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain := by
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
  have hMatched : ∀ u g : H,
      (∃ z : LinearMap.range j.toLinearMap, (z : H) = u ∧
        ∀ v : LinearMap.range j.toLinearMap,
          pressureA5CanonicalRangeEnergy j Eform hjinj z v =
            ⟪g, (v : H)⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -g := by
    intro u g
    exact (pressure_A5_weak_graph_equiv_of_energy_equiv
      j Eform (LinearMap.range j.toLinearMap)
      (pressureA5CanonicalRangeEnergy j Eform hjinj)
      (pressureA5CanonicalFormRangeEquiv j hjinj)
      (pressure_A5_canonical_form_range_carrier j hjinj)
      (pressure_A5_canonical_range_energy_eq j Eform hjinj) u g).trans
      (pressure_neumann_dense_generator_weak_iff
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense u g)
  exact pressure_A5_weak_operator_domain_iff_generator_domain
    S (LinearMap.range j.toLinearMap)
    (pressureA5CanonicalRangeEnergy j Eform hjinj)
    (pressure_A5_canonical_range_separates j hjinj hjDense)
    hMatched u

end CanonicalWeakRange
end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_canonical_form_range_carrier
#print axioms ReservoirSeismicityControl.pressure_A5_canonical_range_energy_eq
#print axioms ReservoirSeismicityControl.pressure_A5_canonical_range_separates
#print axioms ReservoirSeismicityControl.pressure_A5_canonical_range_operator_eq_neg_generator
#print axioms ReservoirSeismicityControl.pressure_A5_canonical_range_domain_iff_generator_domain
