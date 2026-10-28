import ReservoirSeismicityControl.PaperA5PhysicalGeneratorContinuity
import ReservoirSeismicityControl.PaperNearWeakNeumannMovingDerivative
import Mathlib.Tactic

/-!
# Stage 74 — connect physical A5 generator continuity to the moving near observation

Stage 73 gives continuity of the *actual* generator of the full multiwell
mild pressure solution, for arbitrary fixed L² well profiles and bounded
locally integrable rates, without time derivatives of the rates.

The Stage 63 moving-observation product rule required continuity of the weak
Neumann operator applied to the pressure path as an independent hypothesis.
Here we **derive** that continuity from Stage 73 after explicitly stating
the two remaining realization obligations:

  1. the weak-domain pressure path has the same L² carrier as the finite-
     horizon physical pressure (with time clamped to `[0,T]`);
  2. the positive weak Neumann operator agrees with the *negative* semigroup
     generator on the weak-domain elements representing physical pressure.

These two properties need to be specialized/proved for the physical 3D
Sobolev realization. The regularity of the moving SR weight, the derivative
of the pressure path, and their bounds are **not** established here.
No `Qdot` assumption is made. No theorem below claims to discharge the
unproved physical realization/weight conditions.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace BigOperators

section PhysicalMovingNear

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Restrict physical time to a finite observation horizon. This allows the
Stage 73 real-time continuous representative to be used at all real times,
including both physical endpoints. -/
noncomputable def pressureA5HorizonClip (T : NNReal) (τ : ℝ) : NNReal :=
  min (Real.toNNReal τ) T

private theorem pressureA5HorizonClip_le (T : NNReal) (τ : ℝ) :
    pressureA5HorizonClip T τ ≤ T := by
  exact min_le_right _ _

theorem pressure_A5_horizon_clip_real_continuous (T : NNReal) :
    Continuous (fun τ : ℝ => (pressureA5HorizonClip T τ : ℝ)) := by
  dsimp [pressureA5HorizonClip]
  exact NNReal.continuous_coe.comp
    (continuous_real_toNNReal.min continuous_const)

/-- The full physical Neumann generator continuity of Stage 73 removes
`hpGraph` from Stage 63, conditional ONLY on the explicit identification
of the weak Neumann realization and the pressure path with the physical
semigroup realization. The SR weight does not enter this statement. -/
theorem pressure_A5_weak_near_graph_continuous_of_physical
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (T : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ t : NNReal, t ≤ T → ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q j s| ≤ M j)
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ x : H, (∀ v : V, ⟪x, (v : H)⟫_ℝ = 0) → x = 0)
    (p : ℝ → pressureWeakNeumannDomain V E)
    (hpPhysical : ∀ τ : ℝ,
      (((p τ : V) : H)) =
        S (pressureA5HorizonClip T τ) (p₀ : H) +
          pressureA5ForwardDuhamel S (pressureA5HorizonClip T τ) m f q)
    (hOperatorIdent : ∀ u : pressureWeakNeumannDomain V E,
      ∀ hu : (((u : V) : H)) ∈ S.generatorDomain,
        pressureWeakNeumannOperator V E hsep u =
          -S.generator ⟨(((u : V) : H)), hu⟩) :
    Continuous (fun τ : ℝ => pressureWeakNeumannOperator V E hsep (p τ)) := by
  classical
  obtain ⟨F, hFCont, hF⟩ :=
    pressure_A5_general_multiwell_generator_continuous_representative
      S hSelf hGraph T p₀ m f q hq M hM hBound
  have hEq :
      (fun τ : ℝ => pressureWeakNeumannOperator V E hsep (p τ)) =
        (fun τ : ℝ => -F (pressureA5HorizonClip T τ : ℝ)) := by
    funext τ
    let t : NNReal := pressureA5HorizonClip T τ
    obtain ⟨hp, hpValue⟩ := hF t (pressureA5HorizonClip_le T τ)
    have hCarrier : (((p τ : V) : H)) =
        S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q :=
      hpPhysical τ
    have hPDomain : (((p τ : V) : H)) ∈ S.generatorDomain := by
      rw [hCarrier]
      exact hp
    have hSubtype :
        (⟨(((p τ : V) : H)), hPDomain⟩ : S.generatorDomain) =
          (⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q, hp⟩ :
            S.generatorDomain) := by
      exact Subtype.ext hCarrier
    calc
      pressureWeakNeumannOperator V E hsep (p τ) =
          -S.generator ⟨(((p τ : V) : H)), hPDomain⟩ :=
        hOperatorIdent (p τ) hPDomain
      _ = -S.generator ⟨S t (p₀ : H) +
            pressureA5ForwardDuhamel S t m f q, hp⟩ := by
        rw [hSubtype]
      _ = -F (pressureA5HorizonClip T τ : ℝ) := by
        rw [hpValue]
  rw [hEq]
  exact (hFCont.comp (pressure_A5_horizon_clip_real_continuous T)).neg

/-- Physical Stage 73 continuity discharges the specific `hpGraph` premise
of the genuine Stage 63 moving-near product rule, without `Qdot`.

The `hw`, `hp` derivatives and weak Neumann domain of the SR observation
weight are retained explicitly. They remain physical proof obligations.
-/
theorem pressure_A5_moving_near_hasDerivAt_of_physical
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (T : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ t : NNReal, t ≤ T → ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q j s| ≤ M j)
    (V : Submodule ℝ H) (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ x : H, (∀ v : V, ⟪x, (v : H)⟫_ℝ = 0) → x = 0)
    (hEsym : ∀ u v : V, E u v = E v u)
    (w p : ℝ → pressureWeakNeumannDomain V E)
    (hpPhysical : ∀ τ : ℝ,
      (((p τ : V) : H)) =
        S (pressureA5HorizonClip T τ) (p₀ : H) +
          pressureA5ForwardDuhamel S (pressureA5HorizonClip T τ) m f q)
    (hOperatorIdent : ∀ u : pressureWeakNeumannDomain V E,
      ∀ hu : (((u : V) : H)) ∈ S.generatorDomain,
        pressureWeakNeumannOperator V E hsep u =
          -S.generator ⟨(((u : V) : H)), hu⟩)
    (wdot pdot : H) (τ : ℝ)
    (hw : HasDerivAt (fun s : ℝ => (((w s : V) : H))) wdot τ)
    (hp : HasDerivAt (fun s : ℝ => (((p s : V) : H))) pdot τ) :
    HasDerivAt (paperNearWeakNeumannMovingObservation V E hsep w p)
      (⟪wdot, pressureWeakNeumannOperator V E hsep (p τ)⟫_ℝ +
       ⟪pressureWeakNeumannOperator V E hsep (w τ), pdot⟫_ℝ) τ := by
  have hCont := pressure_A5_weak_near_graph_continuous_of_physical
    S hSelf hGraph T p₀ m f q hq M hM hBound V E hsep p
      hpPhysical hOperatorIdent
  exact paper_near_weak_neumann_moving_hasDerivAt
    V E hsep hEsym w p wdot pdot τ hw hp hCont.continuousAt

end PhysicalMovingNear
end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_weak_near_graph_continuous_of_physical
#print axioms ReservoirSeismicityControl.pressure_A5_moving_near_hasDerivAt_of_physical
