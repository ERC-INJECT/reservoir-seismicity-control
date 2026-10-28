import ReservoirSeismicityControl.PressureAnisotropicNeumann
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stage 30: the weak Neumann operator domain by representability

Let `V` be the chosen Sobolev test space, viewed as a real vector subspace of
`H = L²` (usually the mean-zero subspace). Let `E` be the bilinear diffusion
energy on `V`.

The operator domain is the subset of `u : V` for which the map
`v ↦ E u v` has an `H`-representer. The weak operator is defined to be that
representer. Thus its Green identity is *proved by construction*, not
postulated as an independent axiom.

The test space is assumed to separate the points of H. This holds when V
is dense in H; its proof for the actual Sobolev Neumann space is future work.
The bilinear map E and its connection to the variable-coefficient gradient
integral are not yet constructed here.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

/-- Domain of the operator associated with a weak bilinear form: those
Sobolev test functions whose weak form has an L² representer. -/
def pressureWeakNeumannDomain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Submodule ℝ V where
  carrier := {u | ∃ f : H, ∀ v : V, E u v = ⟪f, (v : H)⟫_ℝ}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro v
    simp
  add_mem' := by
    intro u v hu hv
    obtain ⟨f, hf⟩ := hu
    obtain ⟨g, hg⟩ := hv
    refine ⟨f + g, ?_⟩
    intro w
    simp [hf, hg, inner_add_left]
  smul_mem' := by
    intro c u hu
    obtain ⟨f, hf⟩ := hu
    refine ⟨c • f, ?_⟩
    intro v
    simp [hf, real_inner_smul_left]

/-- Choose a representing L² vector for a member of the weak operator domain.
The next theorem proves that it satisfies the weak Green identity. -/
noncomputable def pressureWeakNeumannRepresenter
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : pressureWeakNeumannDomain V E) : H :=
  Classical.choose u.property

/-- The Green identity holds for the chosen representer by definition. -/
theorem pressure_weak_neumann_representer_green
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : pressureWeakNeumannDomain V E) (v : V) :
    ⟪pressureWeakNeumannRepresenter V E u, (v : H)⟫_ℝ = E (u : V) v := by
  exact (Classical.choose_spec u.property v).symm

/-- A separating test space determines a unique representer. This condition
follows from density in H, and avoids any false boundedness assertion for A. -/
theorem pressure_weak_neumann_representer_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (u : pressureWeakNeumannDomain V E) (f : H)
    (hf : ∀ v : V, E (u : V) v = ⟪f, (v : H)⟫_ℝ) :
    pressureWeakNeumannRepresenter V E u = f := by
  apply sub_eq_zero.mp
  apply hsep
  intro v
  rw [inner_sub_left, pressure_weak_neumann_representer_green]
  rw [hf]
  ring

/-- The representer is linear on its (generally proper) unbounded-operator
 domain. The domain is a submodule of the Sobolev test space, not all of H. -/
noncomputable def pressureWeakNeumannOperator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0) :
    pressureWeakNeumannDomain V E →ₗ[ℝ] H where
  toFun := pressureWeakNeumannRepresenter V E
  map_add' := by
    intro u v
    have hzero :
        pressureWeakNeumannRepresenter V E (u + v) -
          (pressureWeakNeumannRepresenter V E u +
            pressureWeakNeumannRepresenter V E v) = 0 := by
      apply hsep
      intro w
      have hlin : E ((u + v : pressureWeakNeumannDomain V E) : V) w =
          E (u : V) w + E (v : V) w := by
        change E ((u : V) + (v : V)) w =
          E (u : V) w + E (v : V) w
        simp
      calc
        ⟪pressureWeakNeumannRepresenter V E (u + v) -
            (pressureWeakNeumannRepresenter V E u +
              pressureWeakNeumannRepresenter V E v), (w : H)⟫_ℝ
            = ⟪pressureWeakNeumannRepresenter V E (u + v), (w : H)⟫_ℝ -
              (⟪pressureWeakNeumannRepresenter V E u, (w : H)⟫_ℝ +
                ⟪pressureWeakNeumannRepresenter V E v, (w : H)⟫_ℝ) := by
              rw [inner_sub_left, inner_add_left]
        _ = E ((u + v : pressureWeakNeumannDomain V E) : V) w -
              (E (u : V) w + E (v : V) w) := by
              rw [pressure_weak_neumann_representer_green,
                pressure_weak_neumann_representer_green,
                pressure_weak_neumann_representer_green]
        _ = 0 := sub_eq_zero.mpr hlin
    exact sub_eq_zero.mp hzero
  map_smul' := by
    intro c u
    have hzero :
        pressureWeakNeumannRepresenter V E (c • u) -
          c • pressureWeakNeumannRepresenter V E u = 0 := by
      apply hsep
      intro w
      have hlin : E ((c • u : pressureWeakNeumannDomain V E) : V) w =
          c * E (u : V) w := by
        change E (c • (u : V)) w = c * E (u : V) w
        simp
      calc
        ⟪pressureWeakNeumannRepresenter V E (c • u) -
            c • pressureWeakNeumannRepresenter V E u, (w : H)⟫_ℝ
            = ⟪pressureWeakNeumannRepresenter V E (c • u), (w : H)⟫_ℝ -
              c * ⟪pressureWeakNeumannRepresenter V E u, (w : H)⟫_ℝ := by
              rw [inner_sub_left, real_inner_smul_left]
        _ = E ((c • u : pressureWeakNeumannDomain V E) : V) w -
              c * E (u : V) w := by
              rw [pressure_weak_neumann_representer_green,
                pressure_weak_neumann_representer_green]
        _ = 0 := sub_eq_zero.mpr hlin
    exact sub_eq_zero.mp hzero

/-- The Green identity for the constructed weak Neumann operator. -/
theorem pressure_weak_neumann_operator_green
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (u : pressureWeakNeumannDomain V E) (v : V) :
    ⟪pressureWeakNeumannOperator V E hsep u, (v : H)⟫_ℝ =
      E (u : V) v := by
  exact pressure_weak_neumann_representer_green V E u v

/-- If the weak form is symmetric, the resulting unbounded operator is
symmetric, without assuming a separate operator Green identity. -/
theorem pressure_weak_neumann_operator_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (u v : pressureWeakNeumannDomain V E) :
    ⟪pressureWeakNeumannOperator V E hsep u, ((v : V) : H)⟫_ℝ =
      ⟪((u : V) : H), pressureWeakNeumannOperator V E hsep v⟫_ℝ := by
  calc
    ⟪pressureWeakNeumannOperator V E hsep u, ((v : V) : H)⟫_ℝ =
        E (u : V) (v : V) := pressure_weak_neumann_operator_green V E hsep u (v : V)
    _ = E (v : V) (u : V) := hEsym (u : V) (v : V)
    _ = ⟪pressureWeakNeumannOperator V E hsep v, ((u : V) : H)⟫_ℝ :=
      (pressure_weak_neumann_operator_green V E hsep v (u : V)).symm
    _ = ⟪((u : V) : H), pressureWeakNeumannOperator V E hsep v⟫_ℝ :=
      real_inner_comm _ _

/-- Positivity of the energy form transfers to the constructed operator. -/
theorem pressure_weak_neumann_operator_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : H, (∀ v : V, ⟪f, (v : H)⟫_ℝ = 0) → f = 0)
    (hEpos : ∀ u : V, 0 ≤ E u u)
    (u : pressureWeakNeumannDomain V E) :
    0 ≤ ⟪pressureWeakNeumannOperator V E hsep u, ((u : V) : H)⟫_ℝ := by
  rw [pressure_weak_neumann_operator_green V E hsep u (u : V)]
  exact hEpos (u : V)

end ReservoirSeismicityControl
