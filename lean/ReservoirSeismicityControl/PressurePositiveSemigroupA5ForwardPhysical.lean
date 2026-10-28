import ReservoirSeismicityControl.PressurePositiveSemigroupA5UniformGrid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# Forward-time, no-grid A5 for physical three-dimensional Neumann diffusion

The explicit uniform-grid theorem proves A5 for elapsed-time well inputs.
This file shows that the transformation `s ↦ t - s` preserves the restricted
Lebesgue measure on `[0,t)`, so the original physically timed measurable
rates automatically supply all elapsed-rate hypotheses. The actual forward
Duhamel integral is identified by the earlier interval-integral lemma.

No bounded input derivative, spectral expansion, compact-resolvent hypothesis,
or refining-grid assumption is introduced.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

section Reflection

/-- Time reflection preserves Lebesgue measure restricted to `[0,t)`.
The reversal exchanges the excluded endpoint 0 with the excluded endpoint t;
these endpoints are Lebesgue-null. The theorem includes `t = 0`. -/
theorem pressure_A5_reflection_preserving (t : NNReal) :
    MeasurePreserving (fun s : ℝ => (t : ℝ) - s)
      (volume.restrict (Set.Ico 0 (t : ℝ)))
      (volume.restrict (Set.Ico 0 (t : ℝ))) := by
  let φ : ℝ → ℝ := fun s => (t : ℝ) - s
  have hφ : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hPre : φ ⁻¹' (Set.Ico 0 (t : ℝ)) = Set.Ioc 0 (t : ℝ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_Ioc]
    dsimp [φ]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  have hCon :
      (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)) =
        (volume : Measure ℝ).restrict (Set.Ico 0 (t : ℝ)) :=
    ((volume : Measure ℝ).restrict_congr_set
      (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := (t : ℝ)))).symm
  have hVol : Measure.map φ (volume : Measure ℝ) = volume := by
    simpa only [φ] using
      ((volume : Measure ℝ).measurePreserving_sub_left (t : ℝ)).map_eq
  refine ⟨hφ, ?_⟩
  calc
    Measure.map φ ((volume : Measure ℝ).restrict (Set.Ico 0 (t : ℝ))) =
        Measure.map φ ((volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ))) := by
      rw [hCon]
    _ = (Measure.map φ (volume : Measure ℝ)).restrict (Set.Ico 0 (t : ℝ)) := by
      rw [Measure.restrict_map hφ measurableSet_Ico, hPre]
    _ = (volume : Measure ℝ).restrict (Set.Ico 0 (t : ℝ)) := by
      rw [hVol]

/-- Original forward-time rates are integrable after reflection, without
any pointwise regularity or derivative assumption. -/
theorem pressure_A5_reflected_integrable (t : NNReal) (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ico 0 (t : ℝ)))) :
    Integrable (fun u => q ((t : ℝ) - u))
      (volume.restrict (Set.Ico 0 (t : ℝ))) := by
  exact (pressure_A5_reflection_preserving t).integrable_comp_of_integrable hq

/-- Essential amplitude bounds of the original rates remain unchanged
under time reflection. -/
theorem pressure_A5_reflected_bound (t : NNReal) (q : ℝ → ℝ)
    (M : ℝ)
    (hq : ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q s| ≤ M) :
    ∀ᵐ u ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |q ((t : ℝ) - u)| ≤ M := by
  exact (pressure_A5_reflection_preserving t).quasiMeasurePreserving.ae hq

end Reflection

section AbstractForward

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The sharp forward-time multiwell estimate for signed integrable,
essentially bounded physical rates. The uniform grid and all reflected-rate
hypotheses are proved internally. -/
theorem pressure_multiwell_A5_measurable_forward
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |q j s| ≤ M j) :
    ∃ hp : (S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
      ‖S.generator ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  have hr (j : Fin m) :
      Integrable (fun u => q j ((t : ℝ) - u))
        (volume.restrict (Set.Ico 0 (t : ℝ))) :=
    pressure_A5_reflected_integrable t (q j) (hq j)
  have hrBound (j : Fin m) :
      ∀ᵐ u ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
        |q j ((t : ℝ) - u)| ≤ M j :=
    pressure_A5_reflected_bound t (q j) (M j) (hBound j)
  obtain ⟨hp, hEstimate⟩ := pressure_multiwell_A5_measurable_no_grid
    S hSelf hGraph t p₀ m f (fun j u => q j ((t : ℝ) - u))
    hr M hM hrBound
  have hDuhamel := pressure_A5_elapsed_equals_forward S t m f q
  -- Rewrite the dependent existential goal before inserting its domain witness.
  -- Rewriting `hEstimate` directly would invalidate the proof carried by `hp`.
  rw [← hDuhamel]
  exact ⟨hp, hEstimate⟩

end AbstractForward

section PhysicalForward

open TopologicalSpace
set_option maxHeartbeats 2000000

/-- Final sharp A5 for the forward-time Duhamel solution of the physical
three-dimensional weak Neumann diffusion operator. All temporal assumptions
refer directly to the forward well rates `q(s)` on `[0,t)`.

The generator is the negative weak Neumann operator constructed from the
physical symmetric elliptic tensor `k/(beta*eta)`. -/
theorem pressure_neumann_3d_physical_A5_measurable_forward
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
        (q : Fin m → ℝ → ℝ)
        (hq : ∀ j, Integrable (q j)
          (volume.restrict (Set.Ico 0 (t : ℝ))))
        (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
        (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
          |q j s| ≤ M j),
        ∃ hp : (S t (p₀ : pressureNeumann3DScalarL2
              (Ω : Set pressureNeumannE3) μ) +
            pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
          ‖S.generator ⟨S t (p₀ : pressureNeumann3DScalarL2
                (Ω : Set pressureNeumannE3) μ) +
              pressureA5ForwardDuhamel S t m f q, hp⟩‖ ≤
            ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖) := by
  intro μ embed negDiv D hTests G C j
  obtain ⟨S, hWeak, hA5⟩ :=
    pressure_neumann_3d_physical_A5_measurable_no_grid
      Ω hΩ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨S, hWeak, ?_⟩
  intro t p₀ m f q hq M hM hBound
  have hr (i : Fin m) :
      Integrable (fun u => q i ((t : ℝ) - u))
        (volume.restrict (Set.Ico 0 (t : ℝ))) :=
    pressure_A5_reflected_integrable t (q i) (hq i)
  have hrBound (i : Fin m) :
      ∀ᵐ u ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
        |q i ((t : ℝ) - u)| ≤ M i :=
    pressure_A5_reflected_bound t (q i) (M i) (hBound i)
  obtain ⟨hp, hEstimate⟩ := hA5 t p₀ m f
    (fun i u => q i ((t : ℝ) - u)) hr M hM hrBound
  have hDuhamel := pressure_A5_elapsed_equals_forward S t m f q
  -- Rewrite the dependent existential goal before inserting its domain witness.
  -- Rewriting `hEstimate` directly would invalidate the proof carried by `hp`.
  rw [← hDuhamel]
  exact ⟨hp, hEstimate⟩

end PhysicalForward

end ReservoirSeismicityControl
