import ReservoirSeismicityControl.PressurePhysicalCoefficient

/-!
# Stage 35: measurable physical coefficients and entrywise bounds

The pressure diffusion tensor is `a(x) = k(x)/(beta * eta(x))`.
The Stage 32 tensor-integrability theorem needs measurability and an
almost-everywhere absolute bound for EACH matrix entry of `a`.

This module proves measurability of the quotient, transfers an entrywise
bound on `k` to `a`, and packages exactly the two hypotheses required by
Stage 32. The permeability entrywise bound is still assumed here: proving
it from the quadratic-form bounds in A3 is a separate finite-dimensional
spectral argument, NOT performed in this module.

This module does not construct the bounded-domain Sobolev space or operator.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- Measurability of each entry of the physical diffusion tensor. -/
theorem pressure_physical_tensor_entry_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ)
    (i j : Fin n)
    (hk : Measurable (fun x => k x i j))
    (heta : Measurable eta) :
    Measurable (fun x => pressurePhysicalTensor k eta beta x i j) := by
  change Measurable (fun x => k x i j / (beta * eta x))
  exact hk.div (measurable_const.mul heta)

/-- The real-valued coefficient is automatically a.e. strongly measurable. -/
theorem pressure_physical_tensor_entry_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta : ℝ)
    (i j : Fin n)
    (hk : Measurable (fun x => k x i j))
    (heta : Measurable eta) :
    AEStronglyMeasurable (fun x => pressurePhysicalTensor k eta beta x i j) μ := by
  exact (pressure_physical_tensor_entry_measurable k eta beta i j hk heta).aestronglyMeasurable

/-- An entry bound on permeability transfers to the effective tensor.
The denominator is positive and is bounded away from zero. -/
theorem pressure_physical_tensor_entry_abs_bound
    {Ω : Type*} {n : ℕ}
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (x : Ω) (i j : Fin n)
    (hetaLo : etam ≤ eta x)
    (hkEntry : |k x i j| ≤ kM) :
    |pressurePhysicalTensor k eta beta x i j| ≤ kM / (beta * etam) := by
  have he : 0 < eta x := lt_of_lt_of_le hetam hetaLo
  have hd : 0 < beta * eta x := mul_pos hbeta he
  have hdm : 0 < beta * etam := mul_pos hbeta hetam
  have hdle : beta * etam ≤ beta * eta x :=
    mul_le_mul_of_nonneg_left hetaLo (le_of_lt hbeta)
  change |k x i j / (beta * eta x)| ≤ kM / (beta * etam)
  rw [abs_div, abs_of_pos hd]
  calc
    |k x i j| / (beta * eta x) ≤ kM / (beta * eta x) :=
      div_le_div_of_nonneg_right hkEntry (le_of_lt hd)
    _ ≤ kM / (beta * etam) :=
      div_le_div_of_nonneg_left hkM hdm hdle

/-- The physical tensor has a uniform a.e. entrywise bound when permeability
has a uniform a.e. entrywise bound. -/
theorem pressure_physical_tensor_entry_abs_bound_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hkEntry : ∀ i j : Fin n, ∀ᵐ x ∂μ, |k x i j| ≤ kM) :
    ∀ i j : Fin n, ∀ᵐ x ∂μ,
      |pressurePhysicalTensor k eta beta x i j| ≤ kM / (beta * etam) := by
  intro i j
  filter_upwards [hetaLo, hkEntry i j] with x hlow hentry
  exact pressure_physical_tensor_entry_abs_bound
    k eta beta kM etam hbeta hkM hetam x i j hlow hentry

/-- Supply both coefficient hypotheses expected by Stage 32: a.e. strong
measurability and a common nonnegative entry bound. -/
theorem pressure_physical_tensor_stage32_coefficient_data
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω)
    (k : Ω → Fin n → Fin n → ℝ)
    (eta : Ω → ℝ) (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (hkMeas : ∀ i j : Fin n, Measurable (fun x => k x i j))
    (hetaMeas : Measurable eta)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hkEntry : ∀ i j : Fin n, ∀ᵐ x ∂μ, |k x i j| ≤ kM) :
    (0 ≤ kM / (beta * etam)) ∧
    (∀ i j : Fin n, AEStronglyMeasurable
      (fun x => pressurePhysicalTensor k eta beta x i j) μ) ∧
    (∀ i j : Fin n, ∀ᵐ x ∂μ,
      |pressurePhysicalTensor k eta beta x i j| ≤ kM / (beta * etam)) := by
  refine ⟨div_nonneg hkM (le_of_lt (mul_pos hbeta hetam)), ?_, ?_⟩
  · intro i j
    exact pressure_physical_tensor_entry_aestronglyMeasurable
      μ k eta beta i j (hkMeas i j) hetaMeas
  · exact pressure_physical_tensor_entry_abs_bound_ae
      μ k eta beta kM etam hbeta hkM hetam hetaLo hkEntry

end ReservoirSeismicityControl
