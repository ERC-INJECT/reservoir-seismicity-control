import ReservoirSeismicityControl.PressurePositiveSemigroupStrongBridge
import ReservoirSeismicityControl.PressureNeumannGeneratedSemigroup
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Self-adjointness and positive partitions of the canonical Neumann semigroup

The semigroup is constructed from the symmetric canonical weak resolvents by
Yosida approximation. Its bounded Yosida generators are self-adjoint, their
exponentials are self-adjoint, and their strong limits remain symmetric.
Consequently, the finite weighted-partition theorem can be used without an
extra self-adjointness premise on the semigroup itself.

This does not yet prove the passage to a forced Duhamel integral or an A5
estimate for the unbounded generator acting on that integral.
-/

namespace ReservoirSeismicityControl

open Filter Topology
open scoped InnerProductSpace BigOperators

section AbstractResolvent

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every Yosida exponential of a self-adjoint resolvent family is self-adjoint. -/
theorem pressure_yosida_isSelfAdjoint
    (R : MarkovProcess.Semigroup.ContractiveResolvent H)
    (hR : ∀ α : MarkovProcess.Semigroup.PositiveShift,
      IsSelfAdjoint (R.operator α))
    (α : MarkovProcess.Semigroup.PositiveShift) (t : NNReal) :
    IsSelfAdjoint (R.yosidaOperator α t) := by
  have hScaled : IsSelfAdjoint (R.scaledOperator α) := by
    unfold MarkovProcess.Semigroup.ContractiveResolvent.scaledOperator
    exact (IsSelfAdjoint.all (α : ℝ)).smul (hR α)
  have hGenerator : IsSelfAdjoint (R.yosidaGenerator α) := by
    unfold MarkovProcess.Semigroup.ContractiveResolvent.yosidaGenerator
    exact (IsSelfAdjoint.all (α : ℝ)).smul
      (hScaled.sub (IsSelfAdjoint.one (H →L[ℝ] H)))
  unfold MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator
  exact ((IsSelfAdjoint.all (t : ℝ)).smul hGenerator).exp

/-- Self-adjointness passes from the bounded Yosida exponentials to the
strongly continuous contraction semigroup that they generate. -/
theorem pressure_generated_semigroup_isSelfAdjoint
    (R : MarkovProcess.Semigroup.ContractiveResolvent H)
    (hR : ∀ α : MarkovProcess.Semigroup.PositiveShift,
      IsSelfAdjoint (R.operator α))
    (t : NNReal) :
    IsSelfAdjoint (R.generatedSemigroup t) := by
  have hSym (x y : H) :
      ⟪R.generatedSemigroup t x, y⟫_ℝ =
        ⟪x, R.generatedSemigroup t y⟫_ℝ := by
    have hx := R.tendsto_yosidaOperator_naturalShift_apply t x
    have hy := R.tendsto_yosidaOperator_naturalShift_apply t y
    have hLeft : Tendsto
        (fun n : ℕ => ⟪R.yosidaOperator (MarkovProcess.Semigroup.naturalShift n) t x, y⟫_ℝ)
        atTop (𝓝 ⟪R.generatedSemigroup t x, y⟫_ℝ) := by
      have hc : Continuous (fun z : H => ⟪z, y⟫_ℝ) := by fun_prop
      exact (hc.tendsto _).comp (by simpa only [R.generatedSemigroup_apply] using hx)
    have hRight : Tendsto
        (fun n : ℕ => ⟪x, R.yosidaOperator (MarkovProcess.Semigroup.naturalShift n) t y⟫_ℝ)
        atTop (𝓝 ⟪x, R.generatedSemigroup t y⟫_ℝ) := by
      have hc : Continuous (fun z : H => ⟪x, z⟫_ℝ) := by fun_prop
      exact (hc.tendsto _).comp (by simpa only [R.generatedSemigroup_apply] using hy)
    have hSeq :
        (fun n : ℕ => ⟪R.yosidaOperator (MarkovProcess.Semigroup.naturalShift n) t x, y⟫_ℝ) =
          (fun n : ℕ => ⟪x, R.yosidaOperator (MarkovProcess.Semigroup.naturalShift n) t y⟫_ℝ) := by
      funext n
      let T := R.yosidaOperator (MarkovProcess.Semigroup.naturalShift n) t
      have hT : IsSelfAdjoint T := pressure_yosida_isSelfAdjoint R hR _ t
      calc
        ⟪T x, y⟫_ℝ = ⟪x, T.adjoint y⟫_ℝ :=
          (ContinuousLinearMap.adjoint_inner_right T x y).symm
        _ = ⟪x, T y⟫_ℝ := by rw [hT.adjoint_eq]
    rw [hSeq] at hLeft
    exact tendsto_nhds_unique hLeft hRight
  have hAdj : ContinuousLinearMap.adjoint (R.generatedSemigroup t) =
      R.generatedSemigroup t := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff
      (R.generatedSemigroup t) (R.generatedSemigroup t)).2
    exact hSym
  exact (isSelfAdjoint_iff).2 hAdj

end AbstractResolvent

section CanonicalNeumann

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- No symmetry assumption on `E` is necessary: it follows from the
symmetric unit form and its decomposition into Hilbert and energy terms. -/
theorem pressure_canonical_energy_symmetric
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (x y : V) : E x y = E y x := by
  calc
    E x y = B₁ x y - ⟪j x, j y⟫_ℝ := by rw [hForm₁]; ring
    _ = B₁ y x - ⟪j y, j x⟫_ℝ := by
      rw [hSymB x y, real_inner_comm (j x) (j y)]
    _ = E y x := by rw [hForm₁]; ring

/-- Every positive-shift canonical weak resolvent is self-adjoint. -/
theorem pressure_canonical_resolvent_isSelfAdjoint
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x) (hLam : 0 < lam)
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x) :
    IsSelfAdjoint (pressureNeumannCanonicalResolvent
      lam j B₁ E hB₁ hForm₁ hE hLam) := by
  have hSymE : ∀ x y : V, E x y = E y x :=
    pressure_canonical_energy_symmetric j B₁ E hForm₁ hSymB
  have hShiftSym : ∀ x y : V,
      pressureNeumannCanonicalShiftForm lam B₁ E x y =
        pressureNeumannCanonicalShiftForm lam B₁ E y x := by
    intro x y
    simp only [pressureNeumannCanonicalShiftForm,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hSymB x y, hSymE x y]
  have hAdj := pressure_hilbert_resolvent_selfadjoint j
    (pressureNeumannCanonicalShiftForm lam B₁ E)
    (pressure_neumann_canonical_shift_coercive
      lam j B₁ E hB₁ hForm₁ hE hLam) hShiftSym
  exact (isSelfAdjoint_iff).2 hAdj

/-- The semigroup obtained from the *physical weak-form construction* is
self-adjoint at every time, without assuming this separately. -/
theorem pressure_canonical_semigroup_isSelfAdjoint
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent
        lam j B₁ E hB₁ hForm₁ hE hLam))
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (t : NNReal) :
    IsSelfAdjoint (pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense t) := by
  let R := pressureNeumannContractiveResolvent
    j B₁ E hB₁ hForm₁ hE hDense
  change IsSelfAdjoint (R.generatedSemigroup t)
  apply pressure_generated_semigroup_isSelfAdjoint R
  intro α
  change IsSelfAdjoint (pressureNeumannCanonicalResolvent
    (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property)
  exact pressure_canonical_resolvent_isSelfAdjoint
    (α : ℝ) j B₁ E hB₁ hForm₁ hE α.property hSymB

/-- The sharp weighted-partition estimate for the constructed canonical
Neumann semigroup, now with NO semigroup self-adjointness premise. -/
theorem pressure_canonical_semigroup_partition_bound
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hDense : ∀ (lam : ℝ) (hLam : 0 < lam),
      DenseRange (pressureNeumannCanonicalResolvent
        lam j B₁ E hB₁ hForm₁ hE hLam))
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (n : ℕ) (τ step : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + step i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M) (f : H) :
    let S := pressureNeumannGeneratedSemigroup
      j B₁ E hB₁ hForm₁ hE hDense
    ‖∑ i ∈ Finset.range n,
        q i • (S (τ i) - S (τ (i + 1))) f‖ ≤ M * ‖f‖ := by
  intro S
  exact pressure_C0_semigroup_partition_weighted_bound S
    (pressure_canonical_semigroup_isSelfAdjoint
      j B₁ E hB₁ hForm₁ hE hDense hSymB)
    n τ step hτ0 hStep q M hM hq f

end CanonicalNeumann

end ReservoirSeismicityControl
