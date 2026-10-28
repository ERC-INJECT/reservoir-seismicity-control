import ReservoirSeismicityControl.PressureNeumannGeneratorWeakIdentity
import ReservoirSeismicityControl.PressurePhysicalCoefficient

/-!
# Block 70: connect the physical anisotropic tensor to the generated Neumann semigroup

The physical tensor is a(x) = k(x)/(beta*eta(x)), with three spatial
components. This file derives symmetry and nonnegativity of its integral
energy from the almost-everywhere coefficients of Assumption A3, then
connects such an energy to the already constructed Neumann semigroup.

IMPORTANT: The complete Hilbert form domain V, its bounded dense embedding
j : V → H, and the continuous bilinear realization E of this integral energy
are supplied explicitly. In particular, this file does *not* construct
H¹(Ω), its weak gradient, or continuous forms on H¹. Those remain open
physical-realization obligations. It also does not prove differentiated
Davies–Gaffney bounds, or assume time derivatives of well fluxes.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- The manuscript's three-dimensional anisotropic diffusion energy,
with a still-abstract Hilbert form space `V` and its gradient. -/
noncomputable def pressurePhysicalThreeDEnergy
    {V Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ) (u v : V) : ℝ :=
  ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
    gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient v x j ∂μ

/-- Almost-everywhere symmetry of permeability implies symmetry of the
*integrated* three-dimensional physical diffusion energy. -/
theorem pressure_physical_threeD_energy_symmetric
    {V Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j : Fin 3, k x i j = k x j i)
    (u v : V) :
    pressurePhysicalThreeDEnergy μ k eta beta gradient u v =
      pressurePhysicalThreeDEnergy μ k eta beta gradient v u := by
  unfold pressurePhysicalThreeDEnergy
  apply integral_congr_ae
  filter_upwards [pressure_physical_tensor_symmetric_ae μ k eta beta hsym] with x hx
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
      gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient v x j) =
        ∑ j : Fin 3, ∑ i : Fin 3,
          gradient u x i * pressurePhysicalTensor k eta beta x i j * gradient v x j :=
      Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
          gradient v x j * pressurePhysicalTensor k eta beta x j i * gradient u x i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i j]
      ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          gradient v x i * pressurePhysicalTensor k eta beta x i j * gradient u x j := rfl

/-- The lower ellipticity estimate from Assumption A3 yields
nonnegative integral energy, without regularity assumptions on Q. -/
theorem pressure_physical_threeD_energy_nonneg
    {V Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaM : 0 < etaM)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (u : V) :
    0 ≤ pressurePhysicalThreeDEnergy μ k eta beta gradient u u := by
  unfold pressurePhysicalThreeDEnergy
  apply integral_nonneg_of_ae
  have hlow := pressure_physical_tensor_elliptic_lower_ae
    μ k eta beta km etam etaM hbeta hkm hetam hetaLo hetaHi hkLo
  filter_upwards [hlow] with x hx
  have hsq : 0 ≤ ∑ i : Fin 3, (gradient u x i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg (gradient u x i))
  have hc : 0 ≤ km / (beta * etaM) :=
    (pressure_physical_gap_coefficient_pos beta km etaM hbeta hkm hetaM).le
  exact (mul_nonneg hc hsq).trans (hx (gradient u x))

/-- A continuous bilinear form which equals the physical integral is
symmetric under the actual a.e. symmetry assumption on permeability. -/
theorem pressure_physical_continuous_form_symmetric
    {V Ω : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (E : V →L[ℝ] V →L[ℝ] ℝ)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hsym : ∀ᵐ x ∂μ, ∀ i j : Fin 3, k x i j = k x j i)
    (u v : V) : E u v = E v u := by
  calc
    E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v := hEnergy u v
    _ = pressurePhysicalThreeDEnergy μ k eta beta gradient v u :=
      pressure_physical_threeD_energy_symmetric μ k eta beta gradient hsym u v
    _ = E v u := (hEnergy v u).symm

/-- The continuous weak form inherits nonnegativity from the physical
3D energy and the a.e. ellipticity bounds of Assumption A3. -/
theorem pressure_physical_continuous_form_nonneg
    {V Ω : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (E : V →L[ℝ] V →L[ℝ] ℝ)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaM : 0 < etaM)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (u : V) : 0 ≤ E u u := by
  rw [hEnergy u u]
  exact pressure_physical_threeD_energy_nonneg μ k eta beta km etam etaM gradient
    hbeta hkm hetam hetaM hetaLo hetaHi hkLo u

/-- Physical permeability symmetry automatically supplies the symmetry
of the canonical unit resolvent's shifted form. -/
theorem pressure_physical_unit_form_symmetric
    {V H Ω : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hsym : ∀ᵐ x ∂μ, ∀ i j : Fin 3, k x i j = k x j i)
    (u v : V) : B₁ u v = B₁ v u := by
  have hSymE : E u v = E v u :=
    pressure_physical_continuous_form_symmetric μ k eta beta gradient E hEnergy hsym u v
  calc
    B₁ u v = ⟪j u, j v⟫_ℝ + E u v := hForm₁ u v
    _ = ⟪j v, j u⟫_ℝ + E v u := by rw [real_inner_comm (j u) (j v), hSymE]
    _ = B₁ v u := (hForm₁ v u).symm

/-- Physical-data semigroup existence and precise weak generator equation.
No additional symmetry/positivity hypotheses on `B₁` or `E` are needed:
those are consequences of the physical permeability hypotheses above.

The Hilbert H¹ form-domain, dense embedding, and bounded continuous
realization of the tensor energy are *still explicit hypotheses*. -/
theorem pressure_physical_neumann_semigroup_exists
    {V H Ω : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : V → Ω → Fin 3 → ℝ)
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hEnergy : ∀ u v : V,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
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
  have hEn : ∀ u : V, 0 ≤ E u u :=
    pressure_physical_continuous_form_nonneg μ k eta beta km etam etaM gradient
      E hEnergy hbeta hkm hetam hetaM hetaLo hetaHi hkLo
  have hSymB : ∀ u v : V, B₁ u v = B₁ v u :=
    pressure_physical_unit_form_symmetric μ k eta beta gradient
      j B₁ E hForm₁ hEnergy hsym
  let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
    j B₁ E hB₁ hForm₁ hEn hSymB hjinj hjDense
  refine ⟨S, ?_⟩
  intro u f
  change
    (∃ x : V, j x = u ∧ ∀ v : V,
      pressurePhysicalThreeDEnergy μ k eta beta gradient x v = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hEn hSymB hjinj hjDense).generatorDomain,
        (pressureNeumannGeneratedSemigroupOfDenseEmbedding
          j B₁ E hB₁ hForm₁ hEn hSymB hjinj hjDense).generator ⟨u, hu⟩ = -f
  simpa only [hEnergy] using
    (pressure_neumann_dense_generator_weak_iff
      j B₁ E hB₁ hForm₁ hEn hSymB hjinj hjDense u f)

end ReservoirSeismicityControl
