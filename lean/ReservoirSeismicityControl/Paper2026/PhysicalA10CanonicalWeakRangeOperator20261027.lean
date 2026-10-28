import ReservoirSeismicityControl.PaperA5CanonicalWeakRange
import Mathlib.Tactic

/-!
# A10: the weak Neumann realization as an actual L²-domain operator

The A10 terminal theorem asks for a submodule `D` of pressure L², a linear
operator `A : D →ₗ[ℝ] L²`, symmetry of A, and equalities identifying the
weak-Neumann pressure and operator with the selected strong realization.
For the **canonical** choice of A from the already constructed weak-Neumann
form, these identifications are consequences, not independent assumptions.

The weak domain is a submodule of the form-test subspace `V`, so we transport
it *injectively* to the ambient L² space and transport its operator by a
linear equivalence. This contains no new spatial regularity hypothesis and
uses no cutoff-lift theorem. The subsequent physical A10 application must
choose the same canonical `V` and `E` as in A5/A9; that step is separate.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

section CanonicalA10WeakRange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The represented weak-Neumann domain embedded in the pressure Hilbert space. -/
noncomputable def pressureA10WeakCarrier :
    pressureWeakNeumannDomain V E →ₗ[ℝ] H :=
  V.subtype.comp (pressureWeakNeumannDomain V E).subtype

/-- The operator domain as a genuine submodule of ambient pressure L². -/
noncomputable abbrev pressureA10WeakDomain : Submodule ℝ H :=
  LinearMap.range (pressureA10WeakCarrier V E)

/-- There is exactly one weak-domain representative of each ambient state in
this range; the equivalence does not assert continuity in the L² norm. -/
noncomputable def pressureA10WeakCarrierEquiv :
    pressureWeakNeumannDomain V E ≃ₗ[ℝ] pressureA10WeakDomain V E :=
  LinearEquiv.ofInjective (pressureA10WeakCarrier V E) (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab)

/-- The canonical A10 domain's ambient value agrees with its weak state. -/
theorem pressure_a10_weak_carrier_coe
    (x : pressureWeakNeumannDomain V E) :
    (((pressureA10WeakCarrierEquiv V E x : pressureA10WeakDomain V E) : H)) =
      (((x : V) : H)) := by
  rfl

/-- Transport the already verified weak Neumann operator to the required
A10 interface `D →ₗ[ℝ] H`, without introducing a new operator. -/
noncomputable def pressureA10WeakOperator
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0) :
    pressureA10WeakDomain V E →ₗ[ℝ] H :=
  (pressureWeakNeumannOperator V E hsep).comp
    (pressureA10WeakCarrierEquiv V E).symm.toLinearMap

/-- Every weak-domain state is acted on by exactly the same operator after
transport to ambient pressure L². -/
theorem pressure_a10_weak_operator_on_carrier
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (x : pressureWeakNeumannDomain V E) :
    pressureA10WeakOperator V E hsep (pressureA10WeakCarrierEquiv V E x) =
      pressureWeakNeumannOperator V E hsep x := by
  change pressureWeakNeumannOperator V E hsep
    ((pressureA10WeakCarrierEquiv V E).symm
      ((pressureA10WeakCarrierEquiv V E) x)) =
    pressureWeakNeumannOperator V E hsep x
  rw [LinearEquiv.symm_apply_apply]

/-- Symmetry is inherited from the physical weak energy, rather than
assumed as `hPressureSymm` in the terminal A10 certificate. -/
theorem pressure_a10_weak_operator_symmetric
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ x y : V, E x y = E y x)
    (a b : pressureA10WeakDomain V E) :
    ⟪pressureA10WeakOperator V E hsep a, (b : H)⟫_ℝ =
      ⟪(a : H), pressureA10WeakOperator V E hsep b⟫_ℝ := by
  let e := pressureA10WeakCarrierEquiv V E
  let x := e.symm a
  let y := e.symm b
  have hax : e x = a := e.apply_symm_apply a
  have hby : e y = b := e.apply_symm_apply b
  have ha : (a : H) = (((x : V) : H)) := by
    rw [← hax]
    exact pressure_a10_weak_carrier_coe V E x
  have hb : (b : H) = (((y : V) : H)) := by
    rw [← hby]
    exact pressure_a10_weak_carrier_coe V E y
  have hAa : pressureA10WeakOperator V E hsep a =
      pressureWeakNeumannOperator V E hsep x := by
    rw [← hax]
    exact pressure_a10_weak_operator_on_carrier V E hsep x
  have hAb : pressureA10WeakOperator V E hsep b =
      pressureWeakNeumannOperator V E hsep y := by
    rw [← hby]
    exact pressure_a10_weak_operator_on_carrier V E hsep y
  rw [hAa, hAb, ha, hb]
  exact pressure_weak_neumann_operator_symmetric V E hsep hEsym x y

/-- The A10 pressure-domain membership is automatic for a canonical weak
pressure path, with no independent `hPressureD` assumption. -/
theorem pressure_a10_weak_path_domain
    (p : ℝ → pressureWeakNeumannDomain V E) (t : ℝ) :
    (((p t : V) : H)) ∈ pressureA10WeakDomain V E := by
  change (((p t : V) : H)) ∈ LinearMap.range (pressureA10WeakCarrier V E)
  exact LinearMap.mem_range_self (pressureA10WeakCarrier V E) (p t)

/-- The two A10 physical-identification hypotheses (`hSamePressure` and
`hSameGenerator`) hold identically for the canonical weak realization. -/
theorem pressure_a10_weak_path_operator_identification
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (p : ℝ → pressureWeakNeumannDomain V E) (t : ℝ) :
    pressureWeakNeumannOperator V E hsep (p t) =
      pressureA10WeakOperator V E hsep
        ⟨(((p t : V) : H)), pressure_a10_weak_path_domain V E p t⟩ := by
  have he : (⟨(((p t : V) : H)), pressure_a10_weak_path_domain V E p t⟩ :
      pressureA10WeakDomain V E) = pressureA10WeakCarrierEquiv V E (p t) := by
    apply Subtype.ext
    exact (pressure_a10_weak_carrier_coe V E (p t)).symm
  rw [he, pressure_a10_weak_operator_on_carrier]

/-- Nonnegativity is likewise inherited from the physical energy. -/
theorem pressure_a10_weak_operator_nonnegative
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEpos : ∀ x : V, 0 ≤ E x x)
    (a : pressureA10WeakDomain V E) :
    0 ≤ ⟪pressureA10WeakOperator V E hsep a, (a : H)⟫_ℝ := by
  let e := pressureA10WeakCarrierEquiv V E
  let x := e.symm a
  have hax : e x = a := e.apply_symm_apply a
  have ha : (a : H) = (((x : V) : H)) := by
    rw [← hax]
    exact pressure_a10_weak_carrier_coe V E x
  have hAa : pressureA10WeakOperator V E hsep a =
      pressureWeakNeumannOperator V E hsep x := by
    rw [← hax]
    exact pressure_a10_weak_operator_on_carrier V E hsep x
  rw [hAa, ha]
  exact pressure_weak_neumann_operator_nonneg V E hsep hEpos x

end CanonicalA10WeakRange

#print axioms ReservoirSeismicityControl.pressure_a10_weak_operator_symmetric
#print axioms ReservoirSeismicityControl.pressure_a10_weak_path_domain
#print axioms ReservoirSeismicityControl.pressure_a10_weak_path_operator_identification
#print axioms ReservoirSeismicityControl.pressure_a10_weak_operator_nonnegative

end ReservoirSeismicityControl
