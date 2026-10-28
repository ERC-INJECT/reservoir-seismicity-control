import ReservoirSeismicityControl.PressureNeumannBoundedCoefficientSemigroup
import ReservoirSeismicityControl.PressurePhysicalCoefficient
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Block 70 — pointwise three-dimensional anisotropic coefficient operator

Construct, from the physical permeability tensor k/(beta*eta), the actual
bounded linear endomorphism of EuclideanSpace ℝ (Fin 3) at every spatial point.
The pointwise self-adjointness and ellipticity inequalities follow from the
physical assumptions of A3. This does NOT yet lift the field of endomorphisms
to a bounded multiplication operator on vector-field L²(Ω).
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

/-- The physical permeability tensor at x as a *bounded linear endomorphism*
of three-dimensional Euclidean space. Boundedness here is finite-dimensional,
not yet a uniform essential bound for the L² multiplication operator. -/
noncomputable def pressureNeumannPhysicalPointwiseCLM
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ) (x : Ω) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
    (fun i j : Fin 3 => pressurePhysicalTensor k eta beta x i j)

/-- The pointwise operator acts by the physical anisotropic matrix product. -/
theorem pressure_neumann_physical_pointwise_apply
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (g : Fin 3 → ℝ) :
    pressureNeumannPhysicalPointwiseCLM k eta beta x (WithLp.toLp 2 g) =
      WithLp.toLp 2
        ((fun i j : Fin 3 => pressurePhysicalTensor k eta beta x i j) *ᵥ g) := by
  exact Matrix.toEuclideanCLM_toLp _ _

/-- The inner product with the coefficient is precisely the tensor's
pointwise bilinear form, in the order h · Cg. -/
theorem pressure_neumann_physical_pointwise_inner
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (g h : Fin 3 → ℝ) :
    ⟪WithLp.toLp 2 h,
      pressureNeumannPhysicalPointwiseCLM k eta beta x (WithLp.toLp 2 g)⟫_ℝ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        h i * pressurePhysicalTensor k eta beta x i j * g j := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => pressurePhysicalTensor k eta beta x i j
  change ⟪WithLp.toLp 2 h,
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A
      (WithLp.toLp 2 g)⟫_ℝ = _
  calc
    _ = (WithLp.toLp 2 h) ⬝ᵥ (A *ᵥ (WithLp.toLp 2 g)) :=
      Matrix.inner_toEuclideanCLM A _ _
    _ = ∑ j : Fin 3, ∑ i : Fin 3, h i * A i j * g j := by
      simpa only [Matrix.dot_mulVec_eq_sum_sum, PiLp.toLp_apply]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, h i * A i j * g j := Finset.sum_comm
    _ = _ := rfl

/-- The pointwise physical tensor defines a symmetric operator under A3. -/
theorem pressure_neumann_physical_pointwise_symmetric
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ) (beta : ℝ)
    (x : Ω) (hsym : ∀ i j : Fin 3, k x i j = k x j i)
    (g h : EuclideanSpace ℝ (Fin 3)) :
    ⟪pressureNeumannPhysicalPointwiseCLM k eta beta x g, h⟫_ℝ =
      ⟪g, pressureNeumannPhysicalPointwiseCLM k eta beta x h⟫_ℝ := by
  let A := pressurePhysicalTensor k eta beta x
  have hA : ∀ i j : Fin 3, A i j = A j i :=
    pressure_physical_tensor_symmetric k eta beta x hsym
  change ⟪pressureNeumannPhysicalPointwiseCLM k eta beta x
      (WithLp.toLp 2 (WithLp.ofLp g)), WithLp.toLp 2 (WithLp.ofLp h)⟫_ℝ =
    ⟪WithLp.toLp 2 (WithLp.ofLp g), pressureNeumannPhysicalPointwiseCLM
      k eta beta x (WithLp.toLp 2 (WithLp.ofLp h))⟫_ℝ
  rw [real_inner_comm]
  rw [pressure_neumann_physical_pointwise_inner,
    pressure_neumann_physical_pointwise_inner]
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
      (WithLp.ofLp h) i * A i j * (WithLp.ofLp g) j) =
      ∑ j : Fin 3, ∑ i : Fin 3,
        (WithLp.ofLp h) i * A i j * (WithLp.ofLp g) j := Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
      (WithLp.ofLp g) j * A j i * (WithLp.ofLp h) i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA i j]
      ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
      (WithLp.ofLp g) i * A i j * (WithLp.ofLp h) j := rfl

/-- Uniform pointwise lower ellipticity is inherited from Assumption A3. -/
theorem pressure_neumann_physical_pointwise_lower
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (x : Ω) (hetaLo : etam ≤ eta x) (hetaHi : eta x ≤ etaM)
    (hkLo : ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j)
    (g : Fin 3 → ℝ) :
    (km / (beta * etaM)) * (∑ i : Fin 3, (g i) ^ 2) ≤
      ⟪pressureNeumannPhysicalPointwiseCLM k eta beta x (WithLp.toLp 2 g),
        WithLp.toLp 2 g⟫_ℝ := by
  rw [real_inner_comm]
  rw [pressure_neumann_physical_pointwise_inner]
  exact pressure_physical_tensor_elliptic_lower k eta beta km etam etaM
    hbeta hkm hetam x hetaLo hetaHi hkLo g

/-- Upper pointwise spectral bound is inherited from Assumption A3. -/
theorem pressure_neumann_physical_pointwise_upper
    {Ω : Type*}
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta kM etam : ℝ)
    (hbeta : 0 < beta) (hkM : 0 ≤ kM) (hetam : 0 < etam)
    (x : Ω) (hetaLo : etam ≤ eta x)
    (hkHi : ∀ g : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, g i * k x i j * g j) ≤
        kM * (∑ i : Fin 3, (g i) ^ 2))
    (g : Fin 3 → ℝ) :
    ⟪pressureNeumannPhysicalPointwiseCLM k eta beta x (WithLp.toLp 2 g),
        WithLp.toLp 2 g⟫_ℝ ≤
      (kM / (beta * etam)) * (∑ i : Fin 3, (g i) ^ 2) := by
  rw [real_inner_comm]
  rw [pressure_neumann_physical_pointwise_inner]
  exact pressure_physical_tensor_elliptic_upper k eta beta kM etam
    hbeta hkM hetam x hetaLo hkHi g

end ReservoirSeismicityControl
