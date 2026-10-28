import ReservoirSeismicityControl.Paper2026.PhysicalA10CanonicalWeakRangeOperator20261027
import ReservoirSeismicityControl.PaperA5CanonicalWeakRange
import Mathlib.Tactic

/-!
# A10/A5 exact canonical operator identification

For the already-constructed coercive Neumann form, the ambient L² operator
obtained from the canonical weak range has exactly the same domain as the
Neumann semigroup generator, and acts as its negative. This is a direct
connection between the passing A5 canonical-form result and the passing
A10 ambient-domain construction; it does not introduce operator equality,
symmetry, or pressure identification as a new assumption.

This does not supply the separate local cutoff-to-Neumann H² estimate.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

section CanonicalA10Generator

variable {U H : Type*}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exact equality of the *actual submodules* of ambient pressure L²:
there is no separate choice of a strong Neumann operator domain. -/
theorem pressure_A10_canonical_weak_domain_eq_generator_domain
    (j : U →L[ℝ] H)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    pressureA10WeakDomain
        (LinearMap.range j.toLinearMap)
        (pressureA5CanonicalRangeEnergy j Eform hjinj) =
      (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain := by
  ext u
  simpa [pressureA10WeakDomain, pressureA10WeakCarrier]
    using (pressure_A5_canonical_range_domain_iff_generator_domain
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense u)

/-- On its represented ambient domain, the canonical A10 operator agrees
pointwise with the positive operator `-S.generator` of the *same* A5
semigroup; hence the A10 operator-identification condition is a theorem. -/
theorem pressure_A10_canonical_weak_operator_eq_neg_generator
    (j : U →L[ℝ] H)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (a : pressureA10WeakDomain
      (LinearMap.range j.toLinearMap)
      (pressureA5CanonicalRangeEnergy j Eform hjinj)) :
    ∃ ha : (a : H) ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain,
      pressureA10WeakOperator
          (LinearMap.range j.toLinearMap)
          (pressureA5CanonicalRangeEnergy j Eform hjinj)
          (pressure_A5_canonical_range_separates j hjinj hjDense) a =
        -(pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator ⟨a, ha⟩ := by
  have hDomain := pressure_A10_canonical_weak_domain_eq_generator_domain
    j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
  have ha : (a : H) ∈
      (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain := by
    rw [← hDomain]
    exact a.property
  refine ⟨ha, ?_⟩
  let V := LinearMap.range j.toLinearMap
  let Ew := pressureA5CanonicalRangeEnergy j Eform hjinj
  let hsep := pressure_A5_canonical_range_separates j hjinj hjDense
  let e := pressureA10WeakCarrierEquiv V Ew
  let x : pressureWeakNeumannDomain V Ew := e.symm a
  have hCoe : (((x : V) : H)) = (a : H) := by
    calc
      (((x : V) : H)) = ((e x : pressureA10WeakDomain V Ew) : H) :=
        (pressure_a10_weak_carrier_coe V Ew x).symm
      _ = (a : H) := congrArg Subtype.val (e.apply_symm_apply a)
  have hx : (((x : V) : H)) ∈
      (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain := by
    rw [hCoe]
    exact ha
  have hA : pressureA10WeakOperator V Ew hsep a =
      pressureWeakNeumannOperator V Ew hsep x := by
    calc
      pressureA10WeakOperator V Ew hsep a =
          pressureA10WeakOperator V Ew hsep (e x) := by
            rw [e.apply_symm_apply]
      _ = pressureWeakNeumannOperator V Ew hsep x :=
        pressure_a10_weak_operator_on_carrier V Ew hsep x
  have hG : pressureWeakNeumannOperator V Ew hsep x =
      -(pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator
          ⟨(((x : V) : H)), hx⟩ :=
    pressure_A5_canonical_range_operator_eq_neg_generator
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense x hx
  have hSame :
      (⟨(((x : V) : H)), hx⟩ :
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain) =
      ⟨(a : H), ha⟩ := Subtype.ext hCoe
  change pressureA10WeakOperator V Ew hsep a = _
  rw [hA, hG, hSame]

end CanonicalA10Generator

#print axioms ReservoirSeismicityControl.pressure_A10_canonical_weak_domain_eq_generator_domain
#print axioms ReservoirSeismicityControl.pressure_A10_canonical_weak_operator_eq_neg_generator

end ReservoirSeismicityControl
