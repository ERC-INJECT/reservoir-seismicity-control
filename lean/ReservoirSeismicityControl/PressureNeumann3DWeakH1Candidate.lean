import ReservoirSeismicityControl.PressureNeumann3DDistributionalTests

/-!
# Block 74: the weak H¹ candidate on a three-dimensional reservoir

This constructs a *concrete L²-based candidate* for H¹(Ω), starting from
vector test fields and their L² negative divergences. A pressure belongs to
the candidate precisely when some L² vector field satisfies the distributional
integration-by-parts identity against the chosen test fields.

When the L² image of the vector tests is dense, the vector field is unique;
therefore the candidate has a well-defined linear weak gradient. No density
of any scalar Neumann core is assumed, and no well-flux derivatives are used.

IMPORTANT: this is NOT YET a proof that the candidate equals the standard
Sobolev space H¹(Ω). The remaining concrete obligations are to instantiate
Φ with C_c^∞(Ω; ℝ³), construct its L² embedding and negative divergence,
prove density of the embedding, and show that the resulting weak-derivative
notion agrees with the usual Sobolev definition on a Lipschitz Ω.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))} (μ : Measure Ω)
variable {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]

/-- Projection of a distributional graph pair onto scalar L² pressure. -/
noncomputable def pressureNeumann3DWeakPressureProjection
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    pressureNeumann3DTestGraph μ embed negDiv →L[ℝ]
      pressureNeumann3DScalarL2 Ω μ :=
  (WithLp.fstL 2 ℝ _ _).comp
    (pressureNeumann3DTestGraph μ embed negDiv).subtypeL

/-- Projection of a distributional graph pair onto its L² weak gradient. -/
noncomputable def pressureNeumann3DWeakGradientProjection
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    pressureNeumann3DTestGraph μ embed negDiv →L[ℝ]
      pressureNeumann3DVectorL2 Ω μ :=
  (WithLp.sndL 2 ℝ _ _).comp
    (pressureNeumann3DTestGraph μ embed negDiv).subtypeL

/-- L² pressures with an L² distributional gradient relative to the tests. -/
noncomputable def pressureNeumann3DWeakH1Candidate
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ) :
    Submodule ℝ (pressureNeumann3DScalarL2 Ω μ) :=
  LinearMap.range
    (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap

/-- Dense L² test fields imply that the pressure projection is injective
on the distributional graph. -/
theorem pressure_neumann_3d_weak_pressure_projection_injective
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ)) :
    Function.Injective
      (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap := by
  intro z w hp
  have hfirst :
      (WithLp.fstL 2 ℝ _ _) z.val =
        (WithLp.fstL 2 ℝ _ _) w.val := by
    simpa [pressureNeumann3DWeakPressureProjection] using hp
  have hsecond :=
    pressure_neumann_3d_test_gradient_unique μ embed negDiv hDense
      z.val w.val z.property w.property hfirst
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · simpa using hfirst
  · simpa using hsecond

/-- The unique L² distributional gradient, defined on the whole candidate
weak-H¹ domain. -/
noncomputable def pressureNeumann3DWeakGradient
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ)) :
    pressureNeumann3DWeakH1Candidate μ embed negDiv →ₗ[ℝ]
      pressureNeumann3DVectorL2 Ω μ :=
  (pressureNeumann3DWeakGradientProjection μ embed negDiv).toLinearMap.comp
    ((LinearEquiv.ofInjective
      (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap
      (pressure_neumann_3d_weak_pressure_projection_injective
        μ embed negDiv hDense)).symm.toLinearMap)

/-- The candidate weak gradient is the gradient of each admissible graph pair. -/
theorem pressure_neumann_3d_weak_gradient_on_graph
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (z : pressureNeumann3DTestGraph μ embed negDiv) :
    pressureNeumann3DWeakGradient μ embed negDiv hDense
      ⟨pressureNeumann3DWeakPressureProjection μ embed negDiv z,
        LinearMap.mem_range_self
          (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap z⟩ =
      pressureNeumann3DWeakGradientProjection μ embed negDiv z := by
  let e := LinearEquiv.ofInjective
    (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap
    (pressure_neumann_3d_weak_pressure_projection_injective
      μ embed negDiv hDense)
  change pressureNeumann3DWeakGradientProjection μ embed negDiv
    (e.symm (e z)) = pressureNeumann3DWeakGradientProjection μ embed negDiv z
  rw [e.symm_apply_apply]

/-- On the whole weak-H¹ candidate, the gradient satisfies the
3D distributional integration-by-parts identity for every test field. -/
theorem pressure_neumann_3d_weak_gradient_ibp
    (embed : Φ →ₗ[ℝ] pressureNeumann3DVectorL2 Ω μ)
    (negDiv : Φ →ₗ[ℝ] pressureNeumann3DScalarL2 Ω μ)
    (hDense : DenseRange (embed : Φ → pressureNeumann3DVectorL2 Ω μ))
    (φ : Φ) (u : pressureNeumann3DWeakH1Candidate μ embed negDiv) :
    ⟪embed φ, pressureNeumann3DWeakGradient μ embed negDiv hDense u⟫_ℝ =
      ⟪negDiv φ, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ := by
  let e := LinearEquiv.ofInjective
    (pressureNeumann3DWeakPressureProjection μ embed negDiv).toLinearMap
    (pressure_neumann_3d_weak_pressure_projection_injective
      μ embed negDiv hDense)
  let z : pressureNeumann3DTestGraph μ embed negDiv := e.symm u
  have hp : pressureNeumann3DWeakPressureProjection μ embed negDiv z =
      (u : pressureNeumann3DScalarL2 Ω μ) := by
    have he : e z = u := e.apply_symm_apply u
    exact congrArg Subtype.val he
  have h := (pressure_neumann_3d_test_graph_mem_iff μ embed negDiv
    z.val).mp z.property φ
  change ⟪embed φ, pressureNeumann3DWeakGradientProjection μ embed negDiv z⟫_ℝ =
    ⟪negDiv φ, pressureNeumann3DWeakPressureProjection μ embed negDiv z⟫_ℝ at h
  change ⟪embed φ, pressureNeumann3DWeakGradientProjection μ embed negDiv (e.symm u)⟫_ℝ =
    ⟪negDiv φ, (u : pressureNeumann3DScalarL2 Ω μ)⟫_ℝ
  rw [← hp]
  exact h

end ReservoirSeismicityControl
