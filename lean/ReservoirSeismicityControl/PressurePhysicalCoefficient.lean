import ReservoirSeismicityControl.PressureTensorOperatorBridge

/-!
# Stage 34: physical anisotropic coefficient from Assumption A3

The manuscript's pressure operator is

  A = -(1 / beta) div ((k / eta) grad).

Its pointwise effective tensor is k(x) / (beta * eta(x)).  This file
proves symmetry, positivity and the sharp inherited quadratic-form
bounds from physical permeability and viscosity bounds.  No extra
smoothness of k or eta and no bound on time derivatives is introduced.

The input permeability spectral inequalities are those of manuscript
Assumption A3. The final three theorems use almost-everywhere hypotheses
and conclusions, as in the paper. The geometry, Sobolev weak gradient, test-space density,
Poincare inequality, and Neumann operator spectral representation are
not established here. Matrix-entry bounds and measurability are not
claimed as consequences of this file.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped BigOperators

/-- Effective anisotropic diffusion coefficient k / (beta * eta). -/
noncomputable def pressurePhysicalTensor
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ) :
    Ω → Fin n → Fin n → ℝ :=
  fun x i j => k x i j / (beta * eta x)

/-- The physical tensor inherits symmetry from the permeability tensor. -/
theorem pressure_physical_tensor_symmetric
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (hsym : ∀ i j, k x i j = k x j i) :
    ∀ i j,
      pressurePhysicalTensor k eta beta x i j =
        pressurePhysicalTensor k eta beta x j i := by
  intro i j
  exact congrArg (fun y : ℝ => y / (beta * eta x)) (hsym i j)

/-- The physical quadratic form is the permeability quadratic form
scaled by the positive diffusion denominator. -/
theorem pressure_physical_tensor_quadratic_form
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (g : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      g i * pressurePhysicalTensor k eta beta x i j * g j) =
      (∑ i : Fin n, ∑ j : Fin n,
        g i * k x i j * g j) / (beta * eta x) := by
  unfold pressurePhysicalTensor
  simp only [div_eq_mul_inv]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      g i * (k x i j * (beta * eta x)⁻¹) * g j) =
      ∑ i : Fin n, ∑ j : Fin n,
        (g i * k x i j * g j) * (beta * eta x)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ i : Fin n, ∑ j : Fin n,
        g i * k x i j * g j) * (beta * eta x)⁻¹ := by
          simp only [Finset.sum_mul]

/-- Assumption A3 implies uniform ellipticity of k/(beta*eta):
cmin = km / (beta * etaM).  No matrix-entry bound is added. -/
theorem pressure_physical_tensor_elliptic_lower
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (x : Ω)
    (hetaLo : etam ≤ eta x)
    (hetaHi : eta x ≤ etaM)
    (hkLo : ∀ g : Fin n → ℝ,
      km * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * k x i j * g j)
    (g : Fin n → ℝ) :
    (km / (beta * etaM)) * (∑ i : Fin n, (g i) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        g i * pressurePhysicalTensor k eta beta x i j * g j := by
  have hS : 0 ≤ ∑ i : Fin n, (g i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg (g i))
  have he : 0 < eta x := lt_of_lt_of_le hetam hetaLo
  have hd : 0 < beta * eta x := mul_pos hbeta he
  have hdle : beta * eta x ≤ beta * etaM :=
    mul_le_mul_of_nonneg_left hetaHi (le_of_lt hbeta)
  calc
    (km / (beta * etaM)) * (∑ i : Fin n, (g i) ^ 2) =
      (km * (∑ i : Fin n, (g i) ^ 2)) / (beta * etaM) := by ring
    _ ≤ (km * (∑ i : Fin n, (g i) ^ 2)) / (beta * eta x) :=
      div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hkm) hS) hd hdle
    _ ≤ (∑ i : Fin n, ∑ j : Fin n,
          g i * k x i j * g j) / (beta * eta x) :=
      div_le_div_of_nonneg_right (hkLo g) (le_of_lt hd)
    _ = ∑ i : Fin n, ∑ j : Fin n,
          g i * pressurePhysicalTensor k eta beta x i j * g j :=
      (pressure_physical_tensor_quadratic_form k eta beta x g).symm

/-- An upper spectral bound for k gives the corresponding effective-tensor
upper bound, with cmax = kM / (beta * etam). -/
theorem pressure_physical_tensor_elliptic_upper
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ)
    (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (x : Ω)
    (hetaLo : etam ≤ eta x)
    (hkHi : ∀ g : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin n, g i * k x i j * g j) ≤
        kM * (∑ i : Fin n, (g i) ^ 2))
    (g : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      g i * pressurePhysicalTensor k eta beta x i j * g j) ≤
      (kM / (beta * etam)) * (∑ i : Fin n, (g i) ^ 2) := by
  have hS : 0 ≤ ∑ i : Fin n, (g i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg (g i))
  have he : 0 < eta x := lt_of_lt_of_le hetam hetaLo
  have hd : 0 < beta * eta x := mul_pos hbeta he
  have hdm : 0 < beta * etam := mul_pos hbeta hetam
  have hdle : beta * etam ≤ beta * eta x :=
    mul_le_mul_of_nonneg_left hetaLo (le_of_lt hbeta)
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      g i * pressurePhysicalTensor k eta beta x i j * g j) =
      (∑ i : Fin n, ∑ j : Fin n,
        g i * k x i j * g j) / (beta * eta x) :=
      pressure_physical_tensor_quadratic_form k eta beta x g
    _ ≤ (kM * (∑ i : Fin n, (g i) ^ 2)) / (beta * eta x) :=
      div_le_div_of_nonneg_right (hkHi g) (le_of_lt hd)
    _ ≤ (kM * (∑ i : Fin n, (g i) ^ 2)) / (beta * etam) :=
      div_le_div_of_nonneg_left (mul_nonneg hkM hS) hdm hdle
    _ = (kM / (beta * etam)) * (∑ i : Fin n, (g i) ^ 2) := by ring

/-- Strict positivity of the physical coercivity constant. -/
theorem pressure_physical_gap_coefficient_pos
    (beta km etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetaM : 0 < etaM) :
    0 < km / (beta * etaM) :=
  div_pos hkm (mul_pos hbeta hetaM)


/-- Symmetry a.e., matching the quantification in manuscript A3. -/
theorem pressure_physical_tensor_symmetric_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : MeasureTheory.Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j, k x i j = k x j i) :
    ∀ᵐ x ∂μ, ∀ i j,
      pressurePhysicalTensor k eta beta x i j =
        pressurePhysicalTensor k eta beta x j i := by
  filter_upwards [hsym] with x hx
  exact pressure_physical_tensor_symmetric k eta beta x hx

/-- Lower ellipticity holds a.e. under exactly the a.e. bounds of A3. -/
theorem pressure_physical_tensor_elliptic_lower_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : MeasureTheory.Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin n → ℝ,
      km * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, g i * k x i j * g j) :
    ∀ᵐ x ∂μ, ∀ g : Fin n → ℝ,
      (km / (beta * etaM)) * (∑ i : Fin n, (g i) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          g i * pressurePhysicalTensor k eta beta x i j * g j := by
  filter_upwards [hetaLo, hetaHi, hkLo] with x hlow hhigh hklow
  intro g
  exact pressure_physical_tensor_elliptic_lower
    k eta beta km etam etaM hbeta hkm hetam x hlow hhigh hklow g

/-- Upper ellipticity also holds a.e. under A3's a.e. bounds. -/
theorem pressure_physical_tensor_elliptic_upper_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : MeasureTheory.Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ)
    (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hkHi : ∀ᵐ x ∂μ, ∀ g : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin n, g i * k x i j * g j) ≤
        kM * (∑ i : Fin n, (g i) ^ 2)) :
    ∀ᵐ x ∂μ, ∀ g : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin n,
        g i * pressurePhysicalTensor k eta beta x i j * g j) ≤
        (kM / (beta * etam)) * (∑ i : Fin n, (g i) ^ 2) := by
  filter_upwards [hetaLo, hkHi] with x hlow hkhigh
  intro g
  exact pressure_physical_tensor_elliptic_upper
    k eta beta kM etam hbeta hkM hetam x hlow hkhigh g

end ReservoirSeismicityControl
