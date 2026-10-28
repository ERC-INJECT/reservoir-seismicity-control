import ReservoirSeismicityControl.Paper2026.SpatialDimensions20261027
import ReservoirSeismicityControl.PressureNeumannL2MultiplierEnergy
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-!
# A3 permeability tensor, dimensional Euclidean operator, and actual L² multiplier

Extends only the hard-coded Fin 3 pointwise and multiplier part of the passing
Neumann development to Fin n_d. The underlying k/(βη) tensor and A3
ellipticity proofs in PressurePhysicalCoefficient are already dimension-generic.
No extra bound on the tensor/operator is assumed: it is proved using A3.
This is independent of the geometric H¹ test-space realization.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

/-- The physical permeability tensor at x as a *bounded linear endomorphism*
of n_d-dimensional Euclidean space. Boundedness here is finite-dimensional,
not yet a uniform essential bound for the L² multiplication operator. -/
noncomputable def paperPressurePointwiseCLM
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ) (x : Ω) :
    EuclideanSpace ℝ (Fin n_d) →L[ℝ] EuclideanSpace ℝ (Fin n_d) :=
  Matrix.toEuclideanCLM (n := Fin n_d) (𝕜 := ℝ)
    (fun i j : Fin n_d => pressurePhysicalTensor k eta beta x i j)

/-- The pointwise operator acts by the physical anisotropic matrix product. -/
theorem paper_pressure_pointwise_apply
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (g : Fin n_d → ℝ) :
    paperPressurePointwiseCLM k eta beta x (WithLp.toLp 2 g) =
      WithLp.toLp 2
        ((fun i j : Fin n_d => pressurePhysicalTensor k eta beta x i j) *ᵥ g) := by
  exact Matrix.toEuclideanCLM_toLp _ _

/-- The inner product with the coefficient is precisely the tensor's
pointwise bilinear form, in the order h · Cg. -/
theorem paper_pressure_pointwise_inner
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (g h : Fin n_d → ℝ) :
    ⟪WithLp.toLp 2 h,
      paperPressurePointwiseCLM k eta beta x (WithLp.toLp 2 g)⟫_ℝ =
      ∑ i : Fin n_d, ∑ j : Fin n_d,
        h i * pressurePhysicalTensor k eta beta x i j * g j := by
  let A : Matrix (Fin n_d) (Fin n_d) ℝ :=
    fun i j => pressurePhysicalTensor k eta beta x i j
  change ⟪WithLp.toLp 2 h,
    Matrix.toEuclideanCLM (n := Fin n_d) (𝕜 := ℝ) A
      (WithLp.toLp 2 g)⟫_ℝ = _
  calc
    _ = (WithLp.toLp 2 h) ⬝ᵥ (A *ᵥ (WithLp.toLp 2 g)) :=
      Matrix.inner_toEuclideanCLM A _ _
    _ = ∑ j : Fin n_d, ∑ i : Fin n_d, h i * A i j * g j := by
      simpa only [Matrix.dot_mulVec_eq_sum_sum, PiLp.toLp_apply]
    _ = ∑ i : Fin n_d, ∑ j : Fin n_d, h i * A i j * g j := Finset.sum_comm
    _ = _ := rfl

/-- The pointwise physical tensor defines a symmetric operator under A3. -/
theorem paper_pressure_pointwise_symmetric
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (hsym : ∀ i j : Fin n_d, k x i j = k x j i)
    (g h : EuclideanSpace ℝ (Fin n_d)) :
    ⟪paperPressurePointwiseCLM k eta beta x g, h⟫_ℝ =
      ⟪g, paperPressurePointwiseCLM k eta beta x h⟫_ℝ := by
  let A := pressurePhysicalTensor k eta beta x
  have hA : ∀ i j : Fin n_d, A i j = A j i :=
    pressure_physical_tensor_symmetric k eta beta x hsym
  change ⟪paperPressurePointwiseCLM k eta beta x
      (WithLp.toLp 2 (WithLp.ofLp g)), WithLp.toLp 2 (WithLp.ofLp h)⟫_ℝ =
    ⟪WithLp.toLp 2 (WithLp.ofLp g), paperPressurePointwiseCLM
      k eta beta x (WithLp.toLp 2 (WithLp.ofLp h))⟫_ℝ
  rw [real_inner_comm]
  rw [paper_pressure_pointwise_inner,
    paper_pressure_pointwise_inner]
  calc
    (∑ i : Fin n_d, ∑ j : Fin n_d,
      (WithLp.ofLp h) i * A i j * (WithLp.ofLp g) j) =
      ∑ j : Fin n_d, ∑ i : Fin n_d,
        (WithLp.ofLp h) i * A i j * (WithLp.ofLp g) j := Finset.sum_comm
    _ = ∑ j : Fin n_d, ∑ i : Fin n_d,
      (WithLp.ofLp g) j * A j i * (WithLp.ofLp h) i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA i j]
      ring
    _ = ∑ i : Fin n_d, ∑ j : Fin n_d,
      (WithLp.ofLp g) i * A i j * (WithLp.ofLp h) j := rfl

/-- Uniform pointwise lower ellipticity is inherited from Assumption A3. -/
theorem paper_pressure_pointwise_lower
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (x : Ω) (hetaLo : etam ≤ eta x) (hetaHi : eta x ≤ etaM)
    (hkLo : ∀ g : Fin n_d → ℝ,
      km * (∑ i : Fin n_d, (g i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j)
    (g : Fin n_d → ℝ) :
    (km / (beta * etaM)) * (∑ i : Fin n_d, (g i) ^ 2) ≤
      ⟪paperPressurePointwiseCLM k eta beta x (WithLp.toLp 2 g),
        WithLp.toLp 2 g⟫_ℝ := by
  rw [real_inner_comm]
  rw [paper_pressure_pointwise_inner]
  exact pressure_physical_tensor_elliptic_lower k eta beta km etam etaM
    hbeta hkm hetam x hetaLo hetaHi hkLo g

/-- Upper pointwise spectral bound is inherited from Assumption A3. -/
theorem paper_pressure_pointwise_upper
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (x : Ω) (hetaLo : etam ≤ eta x)
    (hkHi : ∀ g : Fin n_d → ℝ,
      (∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j) ≤
        kM * (∑ i : Fin n_d, (g i) ^ 2))
    (g : Fin n_d → ℝ) :
    ⟪paperPressurePointwiseCLM k eta beta x (WithLp.toLp 2 g),
        WithLp.toLp 2 g⟫_ℝ ≤
      (kM / (beta * etam)) * (∑ i : Fin n_d, (g i) ^ 2) := by
  rw [real_inner_comm]
  rw [paper_pressure_pointwise_inner]
  exact pressure_physical_tensor_elliptic_upper k eta beta kM etam
    hbeta hkM hetam x hetaLo hkHi g


/-- Assumption A3 gives the pointwise operator-norm upper bound directly.
The lower ellipticity bound is used to guarantee positivity of the
quadratic form. There is no independent norm-bound assumption. -/
theorem paper_pressure_pointwise_opNorm_le_of_A3
    {n_d : ℕ} {Ω : Type*}
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (g : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (g i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j)
    (hKHi : ∀ x (g : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j) ≤
        kM * (∑ i : Fin n_d, (g i) ^ 2))
    (x : Ω) :
    ‖paperPressurePointwiseCLM k eta beta x‖ ≤
      kM / (beta * etam) := by
  let C := paperPressurePointwiseCLM k eta beta x
  have hM : 0 ≤ kM / (beta * etam) :=
    div_nonneg hkM (le_of_lt (mul_pos hbeta hetam))
  have hSym : C.IsSymmetric := by
    intro z w
    exact paper_pressure_pointwise_symmetric
      k eta beta x (hKSym x) z w
  have hUpper : ∀ z : EuclideanSpace ℝ (Fin n_d),
      ⟪C z, z⟫_ℝ ≤ (kM / (beta * etam)) * ‖z‖ ^ 2 := by
    intro z
    have h := paper_pressure_pointwise_upper
      k eta beta kM etam hbeta hkM hetam x (hEtaLo x)
      (hKHi x) (WithLp.ofLp z)
    simpa only [C, WithLp.toLp_ofLp, PiLp.toLp_apply,
      EuclideanSpace.real_norm_sq_eq] using h
  have hNonneg : ∀ z : EuclideanSpace ℝ (Fin n_d),
      0 ≤ ⟪C z, z⟫_ℝ := by
    intro z
    have hEtaM : 0 < etaM :=
      lt_of_lt_of_le hetam ((hEtaLo x).trans (hEtaHi x))
    have hCoeff : 0 ≤ km / (beta * etaM) :=
      le_of_lt (div_pos hkm (mul_pos hbeta hEtaM))
    have h := paper_pressure_pointwise_lower
      k eta beta km etam etaM hbeta hkm hetam x
      (hEtaLo x) (hEtaHi x) (hKLo x) (WithLp.ofLp z)
    have hlo : (km / (beta * etaM)) * ‖z‖ ^ 2 ≤ ⟪C z, z⟫_ℝ := by
      simpa only [C, WithLp.toLp_ofLp, PiLp.toLp_apply,
        EuclideanSpace.real_norm_sq_eq] using h
    exact (mul_nonneg hCoeff (sq_nonneg _)).trans hlo
  exact pressure_neumann_positive_symmetric_opNorm_le
    C (kM / (beta * etam)) hM hSym hNonneg hUpper


/-- Measurability of all n_d² physical tensor entries implies measurability
of the field of n_d-dimensional bounded coefficient endomorphisms. -/
theorem paper_pressure_pointwise_field_measurable
    {n_d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    Measurable (paperPressurePointwiseCLM k eta beta) := by
  let A : Ω → Matrix (Fin n_d) (Fin n_d) ℝ :=
    fun x i j => pressurePhysicalTensor k eta beta x i j
  have hMatrix : Measurable A := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hTensor i j
  have hMatrixOp : Continuous
      (fun A : Matrix (Fin n_d) (Fin n_d) ℝ =>
        Matrix.toEuclideanCLM (n := Fin n_d) (𝕜 := ℝ) A) := by
    exact LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin n_d) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  change Measurable (fun x : Ω =>
    Matrix.toEuclideanCLM (n := Fin n_d) (𝕜 := ℝ) (A x))
  exact hMatrixOp.measurable.comp hMatrix

/-- The n_d-dimensional physical coefficient now has an actual bounded L² multiplication
operator whenever the physical tensor is measurable and its operator norm
has a uniform essential bound. The latter bound is not postulated in the
PDE theorem: this bound is derived below from the A3 ellipticity assumptions. -/
noncomputable def paperPressureL2TensorMultiplier
    {n_d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j))
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, ‖paperPressurePointwiseCLM k eta beta x‖ ≤ M) :
    Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ :=
  pressureNeumannL2Multiplier μ
    (paperPressurePointwiseCLM k eta beta)
    (paper_pressure_pointwise_field_measurable k eta beta hTensor).aestronglyMeasurable
    M hM hBound


/-- The measurable physical tensor from A3 defines a bounded operator on
vector-valued L². All pointwise bounds follow from the tensor assumptions. -/
noncomputable def paperPressureL2MultiplierOfA3
    {n_d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (g : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (g i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j)
    (hKHi : ∀ x (g : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, g i * k x i j * g j) ≤
        kM * (∑ i : Fin n_d, (g i) ^ 2))
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ :=
  paperPressureL2TensorMultiplier μ k eta beta hTensor
    (kM / (beta * etam))
    (div_nonneg hkM (le_of_lt (mul_pos hbeta hetam)))
    (Filter.Eventually.of_forall
      (paper_pressure_pointwise_opNorm_le_of_A3
        k eta beta km kM etam etaM hbeta hkm hkM hetam
        hEtaLo hEtaHi hKSym hKLo hKHi))


#print axioms paper_pressure_pointwise_opNorm_le_of_A3

end ReservoirSeismicityControl
