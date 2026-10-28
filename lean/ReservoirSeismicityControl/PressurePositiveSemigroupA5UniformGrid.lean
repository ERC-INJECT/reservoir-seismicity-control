import ReservoirSeismicityControl.PressurePositiveSemigroupA5PhysicalNeumann
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

/-!
# Explicit regular grids and sharp A5 without a grid-existence assumption

The grid on [0,t) has k+1 cells for t>0. At t=0 it has no cells.
Both cases satisfy the hypotheses of the previously verified theorem.
No time derivative of a well rate or spectral assumption is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

/-- Number of cells: zero for a zero-length time interval. -/
noncomputable def pressureA5UniformN (t : NNReal) (k : ℕ) : ℕ :=
  if t = 0 then 0 else k + 1

/-- Left endpoints and final endpoint of the uniform partition. -/
noncomputable def pressureA5UniformTau (t : NNReal) (k i : ℕ) : NNReal :=
  (i : NNReal) * (t / ((k + 1 : ℕ) : NNReal))

/-- Uniform cell length. -/
noncomputable def pressureA5UniformH (t : NNReal) (k i : ℕ) : NNReal :=
  t / ((k + 1 : ℕ) : NNReal)

/-- Real-valued mesh used in the convergence argument. -/
noncomputable def pressureA5UniformMesh (t : NNReal) (k : ℕ) : ℝ :=
  (t : ℝ) / ((k + 1 : ℕ) : ℝ)

/-- Every explicit grid is increasing (also for zero time). -/
theorem pressure_A5_uniform_monotone (t : NNReal) (k : ℕ) :
    Monotone (pressureA5UniformTau t k) := by
  intro i j hij
  unfold pressureA5UniformTau
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- Every cell of a nonzero-time grid has strictly positive length. -/
theorem pressure_A5_uniform_strict (t : NNReal) (k i : ℕ)
    (hi : i < pressureA5UniformN t k) :
    pressureA5UniformTau t k i < pressureA5UniformTau t k (i + 1) := by
  have ht : t ≠ 0 := by
    intro hz
    simp [pressureA5UniformN, hz] at hi
  have htpos : 0 < t := (pos_iff_ne_zero).mpr ht
  have hlen : 0 < t / ((k + 1 : ℕ) : NNReal) :=
    div_pos htpos (by positivity)
  unfold pressureA5UniformTau
  apply mul_lt_mul_of_pos_right _ hlen
  exact_mod_cast Nat.lt_succ_self i

/-- The first grid endpoint is zero. -/
theorem pressure_A5_uniform_start (t : NNReal) (k : ℕ) :
    pressureA5UniformTau t k 0 = 0 := by
  simp [pressureA5UniformTau]

/-- The last endpoint is exactly t. -/
theorem pressure_A5_uniform_end (t : NNReal) (k : ℕ) :
    pressureA5UniformTau t k (pressureA5UniformN t k) = t := by
  by_cases ht : t = 0
  · simp [pressureA5UniformTau, pressureA5UniformN, ht]
  · apply NNReal.coe_injective
    simp only [pressureA5UniformTau, pressureA5UniformN, if_neg ht,
      NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp

/-- The grid recursion is exact in nonnegative real time. -/
theorem pressure_A5_uniform_step (t : NNReal) (k i : ℕ)
    (_hi : i < pressureA5UniformN t k) :
    pressureA5UniformTau t k (i + 1) =
      pressureA5UniformTau t k i + pressureA5UniformH t k i := by
  simp only [pressureA5UniformTau, pressureA5UniformH,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- The length of any cell equals the mesh. -/
theorem pressure_A5_uniform_length (t : NNReal) (k i : ℕ)
    (hi : i < pressureA5UniformN t k) :
    (pressureA5UniformTau t k (i + 1) : ℝ) -
      (pressureA5UniformTau t k i : ℝ) ≤ pressureA5UniformMesh t k := by
  have hs := congrArg (fun x : NNReal => (x : ℝ))
    (pressure_A5_uniform_step t k i hi)
  simp only [NNReal.coe_add] at hs
  simp only [pressureA5UniformH, NNReal.coe_div, NNReal.coe_natCast] at hs
  rw [hs]
  simp [pressureA5UniformMesh]

/-- The uniform mesh tends to zero. -/
theorem pressure_A5_uniform_mesh_tendsto (t : NNReal) :
    Tendsto (pressureA5UniformMesh t) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t : ℝ)
  change Tendsto (fun k : ℕ => (t : ℝ) / (((k + 1 : ℕ) : ℝ))) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, mul_zero, div_eq_mul_inv, one_div, one_mul] using h

section AbstractNoGrid

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Sharp multiwell A5 for arbitrary integrable, essentially bounded
signed rates, with the time grid now explicitly constructed for every t ≥ 0. -/
theorem pressure_multiwell_A5_measurable_no_grid
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H)
    (r : Fin m → ℝ → ℝ)
    (hr : ∀ j, Integrable (r j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |r j s| ≤ M j) :
    ∃ hp : (S t (p₀ : H) +
        pressureMultiwellBochnerForcing S
          (volume.restrict (Set.Ico 0 (t : ℝ)))
          Real.toNNReal m f r) ∈ S.generatorDomain,
      ‖S.generator ⟨S t (p₀ : H) +
          pressureMultiwellBochnerForcing S
            (volume.restrict (Set.Ico 0 (t : ℝ)))
            Real.toNNReal m f r, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  exact pressure_multiwell_A5_measurable_elapsed
    S hSelf hGraph t p₀ m f r hr M hM hBound
    (pressureA5UniformN t) (pressureA5UniformTau t)
    (pressureA5UniformH t)
    (pressure_A5_uniform_monotone t)
    (pressure_A5_uniform_strict t)
    (pressure_A5_uniform_start t)
    (pressure_A5_uniform_end t)
    (pressure_A5_uniform_step t)
    (pressureA5UniformMesh t)
    (pressure_A5_uniform_length t)
    (pressure_A5_uniform_mesh_tendsto t)

end AbstractNoGrid

section DenseWeakFormNoGrid

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- No spectral premises, no time-grid premises, no rate derivatives. -/
theorem pressure_dense_neumann_A5_measurable_no_grid
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSymB : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j)
    (hjDense : DenseRange j) :
    let S := pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense
    ∀ (t : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f : Fin m → H) (r : Fin m → ℝ → ℝ)
      (hr : ∀ q, Integrable (r q)
        (volume.restrict (Set.Ico 0 (t : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q)
      (hBound : ∀ q, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
        |r q s| ≤ M q),
      ∃ hp : (S t (p₀ : H) +
          pressureMultiwellBochnerForcing S
            (volume.restrict (Set.Ico 0 (t : ℝ)))
            Real.toNNReal m f r) ∈ S.generatorDomain,
        ‖S.generator ⟨S t (p₀ : H) +
            pressureMultiwellBochnerForcing S
              (volume.restrict (Set.Ico 0 (t : ℝ)))
              Real.toNNReal m f r, hp⟩‖ ≤
          ‖S.generator p₀‖ + ∑ q : Fin m, M q * ‖f q‖ := by
  intro S t p₀ m f r hr M hM hBound
  obtain ⟨hSelf, hGraph⟩ :=
    pressure_dense_neumann_semigroup_selfadjoint_and_graph
      j B₁ E hB₁ hForm₁ hE hSymB hjinj hjDense
  exact pressure_multiwell_A5_measurable_no_grid
    S hSelf hGraph t p₀ m f r hr M hM hBound

end DenseWeakFormNoGrid


section PhysicalThreeDNoGrid

open TopologicalSpace
set_option maxHeartbeats 2000000

theorem pressure_neumann_3d_physical_A5_measurable_no_grid
    (Ω : Opens pressureNeumannE3)
    (hΩ : Bornology.IsBounded (Ω : Set pressureNeumannE3))
    (k : ↥(Ω : Set pressureNeumannE3) → Fin 3 → Fin 3 → ℝ)
    (eta : ↥(Ω : Set pressureNeumannE3) → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin 3 → ℝ),
      km * (∑ i : Fin 3, (z i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin 3 → ℝ),
      (∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j) ≤
        kM * (∑ i : Fin 3, (z i) ^ 2))
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let μ := pressureNeumann3DRestrictedMeasure Ω
      (volume : Measure pressureNeumannE3)
    let embed := pressureNeumann3DRestrictedVectorL2Embed Ω
      (volume : Measure pressureNeumannE3) hΩ
    let negDiv := pressureNeumann3DRestrictedNegDivL2 Ω
      (volume : Measure pressureNeumannE3) hΩ
    let D := pressureNeumann3DWeakH1Candidate μ embed negDiv
    let hTests := pressure_neumann_3d_canonical_vector_tests_dense Ω
      (volume : Measure pressureNeumannE3) hΩ
    let G := pressureNeumann3DWeakGradient μ embed negDiv hTests
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    let j := pressureNeumannGraphHilbertEmbedding D G
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
          (pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ),
      (∀ u g : pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          j x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
                ⟪g, j v⟫_ℝ) ↔
          ∃ hu : u ∈ S.generatorDomain,
            S.generator ⟨u, hu⟩ = -g) ∧
      (∀ (t : NNReal) (p₀ : S.generatorDomain)
        (m : ℕ)
        (f : Fin m → pressureNeumann3DScalarL2 (Ω : Set pressureNeumannE3) μ)
        (r : Fin m → ℝ → ℝ)
        (hr : ∀ q, Integrable (r q)
          (volume.restrict (Set.Ico 0 (t : ℝ))))
        (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q)
        (hBound : ∀ q, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
          |r q s| ≤ M q),
        ∃ hp : (S t (p₀ : pressureNeumann3DScalarL2
              (Ω : Set pressureNeumannE3) μ) +
            pressureMultiwellBochnerForcing S
              (volume.restrict (Set.Ico 0 (t : ℝ)))
              Real.toNNReal m f r) ∈ S.generatorDomain,
          ‖S.generator ⟨S t (p₀ : pressureNeumann3DScalarL2
                (Ω : Set pressureNeumannE3) μ) +
              pressureMultiwellBochnerForcing S
                (volume.restrict (Set.Ico 0 (t : ℝ)))
                Real.toNNReal m f r, hp⟩‖ ≤
            ‖S.generator p₀‖ + ∑ q : Fin m, M q * ‖f q‖) := by
  intro μ embed negDiv D hTests G C j
  obtain ⟨S, hWeak, hA5⟩ :=
    pressure_neumann_3d_physical_A5_measurable_elapsed
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨S, hWeak, ?_⟩
  intro t p₀ m f r hr M hM hBound
  exact hA5 t p₀ m f r hr M hM hBound
    (pressureA5UniformN t) (pressureA5UniformTau t)
    (pressureA5UniformH t)
    (pressure_A5_uniform_monotone t)
    (pressure_A5_uniform_strict t)
    (pressure_A5_uniform_start t)
    (pressure_A5_uniform_end t)
    (pressure_A5_uniform_step t)
    (pressureA5UniformMesh t)
    (pressure_A5_uniform_length t)
    (pressure_A5_uniform_mesh_tendsto t)


end PhysicalThreeDNoGrid

section ForwardTimeIdentity

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The forward-time Duhamel term in the customary physical-time
parameter s. No regularity of the scalar rate is assumed in its definition. -/
noncomputable def pressureA5ForwardDuhamel
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (m : ℕ) (f : Fin m → H)
    (q : Fin m → ℝ → ℝ) : H :=
  ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
    q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j)

/-- The Lebesgue integral on the half-open observation interval equals
its standard oriented interval integral, also when t=0. -/
theorem pressure_A5_integral_Ico_eq_interval (t : NNReal) (F : ℝ → H) :
    (∫ s, F s ∂(volume.restrict (Set.Ico 0 (t : ℝ)))) =
      ∫ s in (0 : ℝ)..(t : ℝ), F s := by
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  exact congrArg (fun ν : Measure ℝ => ∫ s, F s ∂ν)
    ((volume : Measure ℝ).restrict_congr_set
      (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := (t : ℝ))))

/-- Exact forward/backward time-reversal identity for finitely many wells.
This is an equality of *actual Bochner integrals* and imposes no derivative
assumption. The forward rate q(s) becomes the elapsed rate r(u)=q(t-u). -/
theorem pressure_A5_elapsed_equals_forward
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (m : ℕ) (f : Fin m → H)
    (q : Fin m → ℝ → ℝ) :
    pressureMultiwellBochnerForcing S
        (volume.restrict (Set.Ico 0 (t : ℝ)))
        Real.toNNReal m f (fun j u => q j ((t : ℝ) - u)) =
      pressureA5ForwardDuhamel S t m f q := by
  unfold pressureMultiwellBochnerForcing pressureBochnerForcing
    pressureA5ForwardDuhamel
  apply Finset.sum_congr rfl
  intro j _
  let F : ℝ → H := fun s =>
    q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j)
  calc
    (∫ s, q j ((t : ℝ) - s) • S (Real.toNNReal s) (f j)
        ∂(volume.restrict (Set.Ico 0 (t : ℝ)))) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          q j ((t : ℝ) - s) • S (Real.toNNReal s) (f j) :=
      pressure_A5_integral_Ico_eq_interval t _
    _ = ∫ s in (0 : ℝ)..(t : ℝ), F ((t : ℝ) - s) := by
      congr 1
      funext s
      dsimp [F]
      rw [show (t : ℝ) - ((t : ℝ) - s) = s by ring]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), F s := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left F (t : ℝ)
          (a := (0 : ℝ)) (b := (t : ℝ)))
    _ = ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j) := rfl

end ForwardTimeIdentity

end ReservoirSeismicityControl
