import ReservoirSeismicityControl.PressureNeumannPhysicalSemigroupBridge

/-!
# Block 70 — derive weak Neumann coercivity from A3 and the Sobolev graph norm

The preceding physical semigroup theorem assumed `IsCoercive B₁`.
This file proves that property directly from the anisotropic ellipticity
lower bound and the graph-norm estimate for the chosen complete form domain.

In the physical H¹ realization the estimate `hGraphNorm` is the standard
H¹ norm relation (with equality for the usual squared graph norm).
This module does NOT yet construct the H¹ space or its weak gradient;
`hGraphNorm`, diagonal gradient integrability and boundedness of the
continuous physical bilinear form must still be discharged there.

No time regularity of well fluxes is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- The squared spatial-gradient seminorm, evaluated in the measure μ. -/
noncomputable def pressurePhysicalThreeDGradientSq
    {V Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (gradient : V → Ω → Fin 3 → ℝ) (u : V) : ℝ :=
  ∫ x, ∑ i : Fin 3, (gradient u x i) ^ 2 ∂μ

/-- The physical ellipticity lower bound also holds after integration.
Unlike `integral_nonneg`, this requires integrability of both sides;
these are explicit hypotheses, rather than hidden in an undefined Bochner integral. -/
theorem pressure_physical_threeD_energy_integrated_lower
    {V Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (hGradInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, (gradient u x i) ^ 2) μ)
    (hEnergyInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient u x j) μ)
    (u : V) :
    (km / (beta * etaM)) * pressurePhysicalThreeDGradientSq μ gradient u ≤
      pressurePhysicalThreeDEnergy μ k eta beta gradient u u := by
  have hlower := pressure_physical_tensor_elliptic_lower_ae
    μ k eta beta km etam etaM hbeta hkm hetam hetaLo hetaHi hkLo
  have hpoint : ∀ᵐ x ∂μ,
      (km / (beta * etaM)) * (∑ i : Fin 3, (gradient u x i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient u x j := by
    filter_upwards [hlower] with x hx
    exact hx (gradient u x)
  unfold pressurePhysicalThreeDGradientSq pressurePhysicalThreeDEnergy
  calc
    (km / (beta * etaM)) * (∫ x, ∑ i : Fin 3, (gradient u x i) ^ 2 ∂μ) =
        ∫ x, (km / (beta * etaM)) *
          (∑ i : Fin 3, (gradient u x i) ^ 2) ∂μ :=
      (integral_const_mul (km / (beta * etaM)) _).symm
    _ ≤ ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient u x j ∂μ :=
      integral_mono_ae ((hGradInt u).const_mul _) (hEnergyInt u) hpoint

/-- The gradient seminorm is nonnegative even before a concrete H¹
representation is constructed. -/
theorem pressure_physical_gradientSq_nonneg
    {V Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (gradient : V → Ω → Fin 3 → ℝ) (u : V) :
    0 ≤ pressurePhysicalThreeDGradientSq μ gradient u := by
  unfold pressurePhysicalThreeDGradientSq
  apply integral_nonneg
  intro x
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (gradient u x i))

/-- Coercivity of the unit-shift form is a consequence of A3 and the
H¹ graph-norm inequality. The explicit coercivity constant is
`min 1 (km/(beta*etaM))` and is strictly positive.

This removes `IsCoercive B₁` as an independent hypothesis.
The H¹ graph-norm property itself must be established for the eventual
physical realization, not postulated as a new reservoir assumption. -/
theorem pressure_physical_unit_form_coercive_of_graph_norm
    {V H Ω : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hGraphNorm : ∀ u : V,
      ‖u‖ * ‖u‖ ≤ ‖j u‖ * ‖j u‖ + pressurePhysicalThreeDGradientSq μ gradient u)
    (hGradInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, (gradient u x i) ^ 2) μ)
    (hEnergyInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, ∑ l : Fin 3,
        gradient u x i * pressurePhysicalTensor k eta beta x i l * gradient u x l) μ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaM : 0 < etaM)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ l : Fin 3, g i * k x i l * g l) :
    IsCoercive B₁ := by
  let c : ℝ := km / (beta * etaM)
  let a : ℝ := min 1 c
  have hc : 0 < c :=
    pressure_physical_gap_coefficient_pos beta km etaM hbeta hkm hetaM
  have ha : 0 < a := lt_min one_pos hc
  refine ⟨a, ha, ?_⟩
  intro u
  have hG : 0 ≤ pressurePhysicalThreeDGradientSq μ gradient u :=
    pressure_physical_gradientSq_nonneg μ gradient u
  have hU : 0 ≤ ‖j u‖ * ‖j u‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have henergyLower : c * pressurePhysicalThreeDGradientSq μ gradient u ≤ E u u := by
    rw [hEnergy u u]
    exact pressure_physical_threeD_energy_integrated_lower μ k eta beta km etam etaM
      gradient hbeta hkm hetam hetaLo hetaHi hkLo hGradInt hEnergyInt u
  have hNorm := mul_le_mul_of_nonneg_left (hGraphNorm u) ha.le
  have hL2 := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) c) hU
  have hGrad := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) c) hG
  change a * ‖u‖ * ‖u‖ ≤ B₁ u u
  calc
    a * ‖u‖ * ‖u‖ = a * (‖u‖ * ‖u‖) := by ring
    _ ≤ a * (‖j u‖ * ‖j u‖ + pressurePhysicalThreeDGradientSq μ gradient u) := hNorm
    _ = a * (‖j u‖ * ‖j u‖) + a * pressurePhysicalThreeDGradientSq μ gradient u :=
      mul_add _ _ _
    _ ≤ ‖j u‖ * ‖j u‖ + E u u :=
      add_le_add (by simpa only [one_mul] using hL2) (hGrad.trans henergyLower)
    _ = B₁ u u := by rw [hForm₁ u u, real_inner_self_eq_norm_mul_norm]

/-- Physical contraction semigroup with coercivity derived from ellipticity
and graph-norm control, rather than assumed. The remaining hypotheses are
the completion and dense embedding of the physical H¹ form domain and the
continuous form realization, whose proofs are not yet included. -/
theorem pressure_physical_neumann_semigroup_exists_of_graph_norm
    {V H Ω : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hGraphNorm : ∀ u : V,
      ‖u‖ * ‖u‖ ≤ ‖j u‖ * ‖j u‖ + pressurePhysicalThreeDGradientSq μ gradient u)
    (hGradInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, (gradient u x i) ^ 2) μ)
    (hEnergyInt : ∀ u : V, Integrable
      (fun x => ∑ i : Fin 3, ∑ l : Fin 3,
        gradient u x i * pressurePhysicalTensor k eta beta x i l * gradient u x l) μ)
    (hjinj : Function.Injective j) (hjDense : DenseRange j)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaM : 0 < etaM)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ l : Fin 3, g i * k x i l * g l)
    (hsym : ∀ᵐ x ∂μ, ∀ i l : Fin 3, k x i l = k x l i) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H,
      ∀ u f : H,
        (∃ x : V, j x = u ∧ ∀ v : V,
          pressurePhysicalThreeDEnergy μ k eta beta gradient x v = ⟪f, j v⟫_ℝ) ↔
          ∃ hu : u ∈ S.generatorDomain,
            S.generator ⟨u, hu⟩ = -f := by
  have hB : IsCoercive B₁ :=
    pressure_physical_unit_form_coercive_of_graph_norm
      μ k eta beta km etam etaM gradient j B₁ E hForm₁ hEnergy
      hGraphNorm hGradInt hEnergyInt hbeta hkm hetam hetaM hetaLo hetaHi hkLo
  exact pressure_physical_neumann_semigroup_exists
    μ k eta beta km etam etaM gradient j B₁ E hB hForm₁ hEnergy
      hjinj hjDense hbeta hkm hetam hetaM hetaLo hetaHi hkLo hsym

end ReservoirSeismicityControl
