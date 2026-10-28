import ReservoirSeismicityControl.PressureNeumannClosedGradientOperator
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Block 70 — bounded coefficient operators induce Neumann energy forms

This file constructs the continuous bilinear diffusion energy from a bounded
operator `C : K →L[ℝ] K` acting on the completed gradient Hilbert space.
Thus neither the energy form `E`, the unit-shift form `B₁`, nor their
boundedness is assumed independently.

The coefficient operator is assumed symmetric and uniformly elliptic, as
appropriate for a spatially varying symmetric anisotropic permeability tensor.
Identifying `C` with multiplication by k(x)/(beta*eta(x)) on the actual
vector-field L²(Ω) is a separate, not-yet-proved realization step.

Together with the already-verified integration-by-parts and scalar/vector test
densities, the result gives a C₀ contraction semigroup with its exact weak
Neumann generator. No derivative bounds on well fluxes are imposed.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {V K : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The automatically bounded bilinear form (u,v) ↦ ⟪C (A u), A v⟫,
where A and C are continuous linear operators. -/
noncomputable def pressureNeumannBoundedCoefficientForm
    (A : V →L[ℝ] K) (C : K →L[ℝ] K) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ V K ℝ)) A).comp
    ((innerSL ℝ).comp (C.comp A))

@[simp]
theorem pressure_neumann_bounded_coefficient_form_apply
    (A : V →L[ℝ] K) (C : K →L[ℝ] K) (u v : V) :
    pressureNeumannBoundedCoefficientForm A C u v = ⟪C (A u), A v⟫_ℝ := by
  rfl

/-- Symmetry of the coefficient operator passes to its energy form. -/
theorem pressure_neumann_bounded_coefficient_form_symmetric
    (A : V →L[ℝ] K) (C : K →L[ℝ] K)
    (hSym : ∀ x y : K, ⟪C x, y⟫_ℝ = ⟪x, C y⟫_ℝ)
    (u v : V) :
    pressureNeumannBoundedCoefficientForm A C u v =
      pressureNeumannBoundedCoefficientForm A C v u := by
  simp only [pressure_neumann_bounded_coefficient_form_apply]
  calc
    ⟪C (A u), A v⟫_ℝ = ⟪A u, C (A v)⟫_ℝ := hSym (A u) (A v)
    _ = ⟪C (A v), A u⟫_ℝ := real_inner_comm _ _

/-- Uniform positive lower bound on C implies nonnegative energy. -/
theorem pressure_neumann_bounded_coefficient_form_nonneg
    (A : V →L[ℝ] K) (C : K →L[ℝ] K)
    (c : ℝ) (hc : 0 < c)
    (hEll : ∀ z : K, c * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ)
    (u : V) :
    0 ≤ pressureNeumannBoundedCoefficientForm A C u u := by
  rw [pressure_neumann_bounded_coefficient_form_apply]
  exact (mul_nonneg hc.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
    (hEll (A u))

section GraphForm

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [CompleteSpace K]

/-- The graph-domain diffusion energy, constructed rather than postulated. -/
noncomputable def pressureNeumannGraphCoefficientEnergy
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (C : K →L[ℝ] K) :
    pressureNeumannGraphHilbertDomain D G →L[ℝ]
      pressureNeumannGraphHilbertDomain D G →L[ℝ] ℝ :=
  pressureNeumannBoundedCoefficientForm
    (pressureNeumannGraphHilbertGradient D G) C

/-- The unit Neumann form is automatically continuous and is exactly
⟪j u,j v⟫ + ⟪C Gu,Gv⟫. -/
noncomputable def pressureNeumannGraphCoefficientUnitForm
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (C : K →L[ℝ] K) :
    pressureNeumannGraphHilbertDomain D G →L[ℝ]
      pressureNeumannGraphHilbertDomain D G →L[ℝ] ℝ :=
  pressureNeumannBoundedCoefficientForm
      (pressureNeumannGraphHilbertEmbedding D G) (ContinuousLinearMap.id ℝ H) +
    pressureNeumannGraphCoefficientEnergy D G C

/-- The unit form contains no independently assumed weak-form identity. -/
theorem pressure_neumann_graph_coefficient_unit_form_apply
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (C : K →L[ℝ] K)
    (u v : pressureNeumannGraphHilbertDomain D G) :
    pressureNeumannGraphCoefficientUnitForm D G C u v =
      ⟪pressureNeumannGraphHilbertEmbedding D G u,
         pressureNeumannGraphHilbertEmbedding D G v⟫_ℝ +
      pressureNeumannGraphCoefficientEnergy D G C u v := by
  simp [pressureNeumannGraphCoefficientUnitForm,
    pressureNeumannGraphCoefficientEnergy]

/-- Uniform ellipticity and the exact graph norm imply coercivity of the
constructed unit-shift form. There is no independent coercivity assumption. -/
theorem pressure_neumann_graph_coefficient_unit_form_coercive
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K) (C : K →L[ℝ] K)
    (c : ℝ) (hc : 0 < c)
    (hEll : ∀ z : K, c * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ) :
    IsCoercive (pressureNeumannGraphCoefficientUnitForm D G C) := by
  let j := pressureNeumannGraphHilbertEmbedding D G
  let g := pressureNeumannGraphHilbertGradient D G
  let a : ℝ := min 1 c
  have ha : 0 < a := lt_min one_pos hc
  refine ⟨a, ha, ?_⟩
  intro u
  have hJ : 0 ≤ ‖j u‖ * ‖j u‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hG : 0 ≤ ‖g u‖ * ‖g u‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hjBound : a * (‖j u‖ * ‖j u‖) ≤ ‖j u‖ * ‖j u‖ := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) c) hJ)
  have hgBound : a * (‖g u‖ * ‖g u‖) ≤ c * (‖g u‖ * ‖g u‖) :=
    mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) c) hG
  change a * ‖u‖ * ‖u‖ ≤
    ⟪j u, j u⟫_ℝ + ⟪C (g u), g u⟫_ℝ
  rw [real_inner_self_eq_norm_mul_norm]
  calc
    a * ‖u‖ * ‖u‖ = a * (‖u‖ * ‖u‖) := by ring
    _ = a * (‖j u‖ * ‖j u‖ + ‖g u‖ * ‖g u‖) := by
      rw [pressure_neumann_graph_norm_sq D G u]
    _ = a * (‖j u‖ * ‖j u‖) + a * (‖g u‖ * ‖g u‖) := mul_add _ _ _
    _ ≤ ‖j u‖ * ‖j u‖ + c * (‖g u‖ * ‖g u‖) :=
      add_le_add hjBound hgBound
    _ ≤ ‖j u‖ * ‖j u‖ + ⟪C (g u), g u⟫_ℝ :=
      add_le_add le_rfl (hEll (g u))

/-- Main coefficient-operator theorem. All bilinear forms are CONSTRUCTED
from the bounded tensor operator and graph coordinate maps. Completeness,
embedding injectivity and dense range, symmetry, positivity and unit-form
coercivity are consequences of the preceding lemmas and of integration by parts.

Remaining physical step: realize H and K as the actual scalar/vector L²
spaces, prove the distributional-gradient integration-by-parts identity,
and build C as the bounded multiplication operator induced by k/(beta*eta). -/
theorem pressure_neumann_graph_coefficient_semigroup_exists_of_IBP
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K))
    (hDDense : DenseRange (D.subtype : D → H))
    (C : K →L[ℝ] K)
    (c : ℝ) (hc : 0 < c)
    (hEll : ∀ z : K, c * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ)
    (hSym : ∀ z w : K, ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H,
      ∀ u f : H,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          pressureNeumannGraphHilbertEmbedding D G x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
                ⟪f, pressureNeumannGraphHilbertEmbedding D G v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f := by
  let j := pressureNeumannGraphHilbertEmbedding D G
  let g := pressureNeumannGraphHilbertGradient D G
  let E := pressureNeumannGraphCoefficientEnergy D G C
  let B₁ := pressureNeumannGraphCoefficientUnitForm D G C
  have hForm₁ : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B₁ x y = ⟪j x, j y⟫_ℝ + E x y := by
    intro x y
    exact pressure_neumann_graph_coefficient_unit_form_apply D G C x y
  have hE : ∀ x : pressureNeumannGraphHilbertDomain D G, 0 ≤ E x x := by
    intro x
    exact pressure_neumann_bounded_coefficient_form_nonneg g C c hc hEll x
  have hSymE : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      E x y = E y x :=
    pressure_neumann_bounded_coefficient_form_symmetric g C hSym
  have hSymB : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B₁ x y = B₁ y x := by
    intro x y
    calc
      B₁ x y = ⟪j x, j y⟫_ℝ + E x y := hForm₁ x y
      _ = ⟪j y, j x⟫_ℝ + E y x := by rw [real_inner_comm (j x) (j y), hSymE x y]
      _ = B₁ y x := (hForm₁ y x).symm
  have hB₁ : IsCoercive B₁ :=
    pressure_neumann_graph_coefficient_unit_form_coercive D G C c hc hEll
  have hEmbed : Function.Injective j ∧ DenseRange j :=
    pressure_neumann_graph_embedding_injective_and_dense
      D G T delta hIBP hTDense hDDense
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ E hB₁ hForm₁ hE hSymB hEmbed.1 hEmbed.2
  refine ⟨S, ?_⟩
  intro u f
  change
    (∃ x : pressureNeumannGraphHilbertDomain D G, j x = u ∧
      ∀ v : pressureNeumannGraphHilbertDomain D G,
        E x v = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSymB hEmbed.1 hEmbed.2).generatorDomain,
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hE hSymB hEmbed.1 hEmbed.2).generator ⟨u, hu⟩ = -f
  exact pressure_neumann_dense_generator_weak_iff
    j B₁ E hB₁ hForm₁ hE hSymB hEmbed.1 hEmbed.2 u f

end GraphForm

end ReservoirSeismicityControl
