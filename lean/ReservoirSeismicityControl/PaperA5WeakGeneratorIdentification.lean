import ReservoirSeismicityControl.PaperA5PhysicalMovingNearBridge
import ReservoirSeismicityControl.PressureNeumannGeneratorWeakIdentity
import Mathlib.Tactic

/-!
# Stage 75 — Neumann weak operator / semigroup generator identification

Stage 74 left `hOperatorIdent` as a physical-realization assumption.
Here it follows from the *weak energy graph correspondence*. More strongly,
for a dense coercive form realization, the graph correspondence is supplied
by the previously verified theorem `pressure_neumann_dense_generator_weak_iff`.

The only extra bridge between the two presentations is an energy-preserving
linear equivalence between the form Hilbert space and its ambient-L² image.
This is a concrete identification to make for the 3D Sobolev realization,
not an axiom asserting equality of the unbounded operators.

Sign convention: the weak Neumann operator is positive, the semigroup
generator is its negative. No derivative of well fluxes is assumed.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

section WeakEnergyGraph

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An exact weak energy graph determines the weak operator as minus the
semigroup generator, for any element already known to lie in both domains.
In particular, this proves Stage 74's `hOperatorIdent` conclusion rather
than taking that equality as an independent hypothesis. -/
theorem pressure_A5_weak_operator_eq_neg_generator_of_graph
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ g : H, (∀ v : V, ⟪g, (v : H)⟫_ℝ = 0) → g = 0)
    (hWeakGraph : ∀ u g : H,
      (∃ x : V, (x : H) = u ∧
        ∀ v : V, E x v = ⟪g, (v : H)⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -g)
    (x : pressureWeakNeumannDomain V E)
    (hx : (((x : V) : H)) ∈ S.generatorDomain) :
    pressureWeakNeumannOperator V E hsep x =
      -S.generator ⟨(((x : V) : H)), hx⟩ := by
  have hGreen : ∀ v : V, E (x : V) v =
      ⟪pressureWeakNeumannOperator V E hsep x, (v : H)⟫_ℝ := by
    intro v
    exact (pressure_weak_neumann_operator_green V E hsep x v).symm
  obtain ⟨hy, hGenerator⟩ :=
    (hWeakGraph (((x : V) : H))
      (pressureWeakNeumannOperator V E hsep x)).mp
      ⟨(x : V), rfl, hGreen⟩
  have hSubtype :
      (⟨(((x : V) : H)), hy⟩ : S.generatorDomain) =
      ⟨(((x : V) : H)), hx⟩ := Subtype.ext rfl
  rw [hSubtype] at hGenerator
  have hNeg := congrArg Neg.neg hGenerator
  simpa only [neg_neg] using hNeg.symm

/-- In fact the complete operator domains coincide as subsets of the
ambient L² space, whenever the weak form and generator graphs coincide. -/
theorem pressure_A5_weak_operator_domain_iff_generator_domain
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ g : H, (∀ v : V, ⟪g, (v : H)⟫_ℝ = 0) → g = 0)
    (hWeakGraph : ∀ u g : H,
      (∃ x : V, (x : H) = u ∧
        ∀ v : V, E x v = ⟪g, (v : H)⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -g)
    (u : H) :
    (∃ x : pressureWeakNeumannDomain V E, (((x : V) : H)) = u) ↔
      u ∈ S.generatorDomain := by
  constructor
  · rintro ⟨x, hx⟩
    have hGreen : ∀ v : V, E (x : V) v =
        ⟪pressureWeakNeumannOperator V E hsep x, (v : H)⟫_ℝ := by
      intro v
      exact (pressure_weak_neumann_operator_green V E hsep x v).symm
    exact ((hWeakGraph u (pressureWeakNeumannOperator V E hsep x)).mp
      ⟨(x : V), hx, hGreen⟩).1
  · intro hu
    obtain ⟨x, hx, hEnergy⟩ :=
      (hWeakGraph u (-S.generator ⟨u, hu⟩)).mpr
        ⟨hu, by simp⟩
    exact ⟨⟨x, ⟨-S.generator ⟨u, hu⟩, hEnergy⟩⟩, hx⟩

end WeakEnergyGraph

section DenseFormIdentification

variable {U H : Type*}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Match the abstract energy form `Eform` on a completed Hilbert form space
`U` with a weak form `Eweak` on its represented ambient-L² test subspace.
The compatibility maps identify the *form presentations*, not their
(unbounded) operators. -/
theorem pressure_A5_weak_graph_equiv_of_energy_equiv
    (j : U →L[ℝ] H) (Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (V : Submodule ℝ H) (Eweak : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (e : U ≃ₗ[ℝ] V)
    (hCarrier : ∀ x : U, ((e x : V) : H) = j x)
    (hEnergy : ∀ x y : U, Eweak (e x) (e y) = Eform x y)
    (u g : H) :
    (∃ x : V, (x : H) = u ∧
      ∀ v : V, Eweak x v = ⟪g, (v : H)⟫_ℝ) ↔
    (∃ y : U, j y = u ∧
      ∀ z : U, Eform y z = ⟪g, j z⟫_ℝ) := by
  constructor
  · rintro ⟨x, hx, hEx⟩
    refine ⟨e.symm x, ?_, ?_⟩
    · calc
        j (e.symm x) = ((e (e.symm x) : V) : H) :=
          (hCarrier (e.symm x)).symm
        _ = (x : H) := by rw [e.apply_symm_apply]
        _ = u := hx
    · intro z
      calc
        Eform (e.symm x) z = Eweak (e (e.symm x)) (e z) :=
          (hEnergy (e.symm x) z).symm
        _ = Eweak x (e z) := by rw [e.apply_symm_apply]
        _ = ⟪g, ((e z : V) : H)⟫_ℝ := hEx (e z)
        _ = ⟪g, j z⟫_ℝ := by rw [hCarrier]
  · rintro ⟨y, hy, hEy⟩
    refine ⟨e y, ?_, ?_⟩
    · exact (hCarrier y).trans hy
    · intro x
      calc
        Eweak (e y) x = Eweak (e y) (e (e.symm x)) := by
          rw [e.apply_symm_apply]
        _ = Eform y (e.symm x) := hEnergy y (e.symm x)
        _ = ⟪g, j (e.symm x)⟫_ℝ := hEy (e.symm x)
        _ = ⟪g, ((e (e.symm x) : V) : H)⟫_ℝ := by
          rw [hCarrier]
        _ = ⟪g, (x : H)⟫_ℝ := by rw [e.apply_symm_apply]

/-- Density of the completed form embedding automatically gives the
separating condition for the weak operator on its represented L² test space.
Thus this hypothesis is *not* an additional physical assumption. -/
theorem pressure_A5_dense_form_image_separates
    (j : U →L[ℝ] H) (hjDense : DenseRange j)
    (V : Submodule ℝ H) (e : U ≃ₗ[ℝ] V)
    (hCarrier : ∀ x : U, ((e x : V) : H) = j x) :
    ∀ g : H, (∀ v : V, ⟪g, (v : H)⟫_ℝ = 0) → g = 0 := by
  intro g hg
  apply hjDense.eq_zero_of_inner_left ℝ
  intro z
  rw [← hCarrier z]
  exact hg (e z)

/-- For the *constructed* dense-form Neumann semigroup, the ambient weak
operator agrees with minus its generator. This theorem obtains the graph
correspondence from the previously verified dense-form Neumann theorem,
so does not assume either the graph correspondence or the operator equality.
Only the concrete identification of the two form presentations remains. -/
theorem pressure_A5_dense_form_weak_operator_eq_neg_generator
    (j : U →L[ℝ] H)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (V : Submodule ℝ H) (Eweak : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ g : H, (∀ v : V, ⟪g, (v : H)⟫_ℝ = 0) → g = 0)
    (e : U ≃ₗ[ℝ] V)
    (hCarrier : ∀ x : U, ((e x : V) : H) = j x)
    (hEnergy : ∀ x y : U, Eweak (e x) (e y) = Eform x y)
    (x : pressureWeakNeumannDomain V Eweak)
    (hx : (((x : V) : H)) ∈
      (pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generatorDomain) :
    pressureWeakNeumannOperator V Eweak hsep x =
      -(pressureNeumannGeneratedSemigroupOfDenseEmbedding
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense).generator
        ⟨(((x : V) : H)), hx⟩ := by
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
  have hMatched : ∀ u g : H,
      (∃ z : V, (z : H) = u ∧
        ∀ v : V, Eweak z v = ⟪g, (v : H)⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -g := by
    intro u g
    exact (pressure_A5_weak_graph_equiv_of_energy_equiv
      j Eform V Eweak e hCarrier hEnergy u g).trans
      (pressure_neumann_dense_generator_weak_iff
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense u g)
  exact pressure_A5_weak_operator_eq_neg_generator_of_graph
    S V Eweak hsep hMatched x hx

end DenseFormIdentification
end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_weak_operator_eq_neg_generator_of_graph
#print axioms ReservoirSeismicityControl.pressure_A5_weak_operator_domain_iff_generator_domain
#print axioms ReservoirSeismicityControl.pressure_A5_weak_graph_equiv_of_energy_equiv
#print axioms ReservoirSeismicityControl.pressure_A5_dense_form_image_separates
#print axioms ReservoirSeismicityControl.pressure_A5_dense_form_weak_operator_eq_neg_generator
