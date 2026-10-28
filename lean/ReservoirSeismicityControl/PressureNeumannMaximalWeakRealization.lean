import ReservoirSeismicityControl.PressureNeumannWeakGradientCoreDensity

/-!
# Block 72: maximal weak-gradient realization without a core-density assumption

The maximal weak graph already carries a closed gradient operator whenever its
vector test fields are dense in the ambient vector L² space. This file realizes
that operator on the pressure projection of the maximal graph.

Unlike identifying the completion of an independently chosen scalar core with
the maximal weak graph, this construction needs NO approximation hypothesis:
it uses the maximal graph itself as the graph domain.

It remains to instantiate the test fields and their negative divergence on a
concrete Lipschitz region and to prove the resulting pressure domain is H¹.
No derivatives of the well rates are assumed.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Pressure projection from the maximal distributional-gradient graph. -/
noncomputable def pressureNeumannWeakPressureProjection
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) :
    pressureNeumannWeakIBPGraph T delta →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H K).comp (pressureNeumannWeakIBPGraph T delta).subtypeL

/-- Gradient projection from the maximal distributional-gradient graph. -/
noncomputable def pressureNeumannWeakGradientProjection
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) :
    pressureNeumannWeakIBPGraph T delta →L[ℝ] K :=
  (WithLp.sndL 2 ℝ H K).comp (pressureNeumannWeakIBPGraph T delta).subtypeL

/-- The maximal weak-gradient pressure domain, as a submodule of scalar L². -/
noncomputable def pressureNeumannMaximalWeakPressureDomain
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H) : Submodule ℝ H :=
  LinearMap.range (pressureNeumannWeakPressureProjection T delta).toLinearMap

/-- On the maximal weak pressure domain, the weak gradient is unique.
Uniqueness relies on the density of vector test fields. -/
noncomputable def pressureNeumannMaximalWeakGradient
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K)) :
    pressureNeumannMaximalWeakPressureDomain T delta →ₗ[ℝ] K :=
  (pressureNeumannWeakGradientProjection T delta).toLinearMap.comp
    ((LinearEquiv.ofInjective
      (pressureNeumannWeakPressureProjection T delta).toLinearMap
      (pressure_neumann_weak_ibp_pressure_projection_injective T delta hTDense)).symm.toLinearMap)

/-- The maximal weak gradient reproduces the gradient component of every
point of the maximal graph. -/
theorem pressure_neumann_maximal_weak_gradient_on_graph
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K))
    (z : pressureNeumannWeakIBPGraph T delta) :
    pressureNeumannMaximalWeakGradient T delta hTDense
      ⟨pressureNeumannWeakPressureProjection T delta z,
        LinearMap.mem_range_self
          (pressureNeumannWeakPressureProjection T delta).toLinearMap z⟩ =
      pressureNeumannWeakGradientProjection T delta z := by
  let e := LinearEquiv.ofInjective
    (pressureNeumannWeakPressureProjection T delta).toLinearMap
    (pressure_neumann_weak_ibp_pressure_projection_injective T delta hTDense)
  change pressureNeumannWeakGradientProjection T delta
    (e.symm (e z)) = pressureNeumannWeakGradientProjection T delta z
  rw [e.symm_apply_apply]

/-- The original integration-by-parts relation now holds on the *whole*
maximal weak pressure domain, without assuming scalar-core density. -/
theorem pressure_neumann_maximal_weak_gradient_ibp
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K))
    (phi : T) (u : pressureNeumannMaximalWeakPressureDomain T delta) :
    ⟪(phi : K), pressureNeumannMaximalWeakGradient T delta hTDense u⟫_ℝ =
      ⟪delta phi, (u : H)⟫_ℝ := by
  let e := LinearEquiv.ofInjective
    (pressureNeumannWeakPressureProjection T delta).toLinearMap
    (pressure_neumann_weak_ibp_pressure_projection_injective T delta hTDense)
  let z : pressureNeumannWeakIBPGraph T delta := e.symm u
  have hp : pressureNeumannWeakPressureProjection T delta z = (u : H) := by
    have he : e z = u := e.apply_symm_apply u
    exact congrArg Subtype.val he
  have h := (pressure_neumann_weak_ibp_graph_mem_iff T delta
    (z : WithLp 2 (H × K))).mp z.property phi
  change ⟪(phi : K), pressureNeumannWeakGradientProjection T delta z⟫_ℝ =
    ⟪delta phi, pressureNeumannWeakPressureProjection T delta z⟫_ℝ at h
  change ⟪(phi : K), pressureNeumannWeakGradientProjection T delta (e.symm u)⟫_ℝ =
    ⟪delta phi, (u : H)⟫_ℝ
  rw [← hp]
  exact h

/-- On the maximal weak domain, the graph closure construction is exact.
There is no graph-core approximation assumption here because the test domain
is the entire maximal weak pressure domain itself. -/
theorem pressure_neumann_full_weak_domain_graph_eq
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hTDense : DenseRange (T.subtype : T → K)) :
    pressureNeumannGraphHilbertDomain
      (pressureNeumannMaximalWeakPressureDomain T delta)
      (pressureNeumannMaximalWeakGradient T delta hTDense) =
    pressureNeumannWeakIBPGraph T delta := by
  let D := pressureNeumannMaximalWeakPressureDomain T delta
  let G := pressureNeumannMaximalWeakGradient T delta hTDense
  apply le_antisymm
  · exact pressure_neumann_graph_le_weak_ibp_graph D G T delta
      (pressure_neumann_maximal_weak_gradient_ibp T delta hTDense)
  · intro z hz
    let x : pressureNeumannWeakIBPGraph T delta := ⟨z, hz⟩
    let u : D :=
      ⟨pressureNeumannWeakPressureProjection T delta x,
        LinearMap.mem_range_self
          (pressureNeumannWeakPressureProjection T delta).toLinearMap x⟩
    have hpair : pressureNeumannTestGraphMap D G u = z := by
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ H K).injective
      apply Prod.ext
      · change (u : H) = (WithLp.fstL 2 ℝ H K) z
        rfl
      · change G u = (WithLp.sndL 2 ℝ H K) z
        exact pressure_neumann_maximal_weak_gradient_on_graph T delta hTDense x
    apply (Submodule.le_topologicalClosure _)
    exact ⟨u, hpair⟩

end ReservoirSeismicityControl
