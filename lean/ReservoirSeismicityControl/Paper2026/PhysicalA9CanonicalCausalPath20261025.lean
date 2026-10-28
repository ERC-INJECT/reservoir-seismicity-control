import ReservoirSeismicityControl.Paper2026.PhysicalA9CanonicalGeneratorProjection
import ReservoirSeismicityControl.Paper2026.PhysicalA9MildValueAndHomogeneousOrbit20261025
import Mathlib.Tactic

/-!
# A9: one canonical physical pressure path, one generator, one causal value

This theorem *combines* two previously passing physical results:
* A5 constructs the canonical weak-Neumann pressure path whose carrier is
  exactly the finite-well Duhamel solution, with `A = -S.generator`.
* A9 identifies the projected generator of exactly that Duhamel solution
  with its causal analytic-semigroup integral.

The result refers to the **same** physical path at every observation time
in a finite horizon, and eliminates the separate physical-path/generator
identification from the A9 causal-value interface. It introduces no
assumption about the time derivative of Q or of the final A9 observation.

The cited analytic-semigroup smoothing and Davies--Gaffney estimates remain
explicit, as they must; the identification of their bounded kernel with the
weak Neumann orbit is a separate physical-operator application.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- Construct the *actual canonical physical pressure path* and establish
its projected elliptic generator's causal representation, without assuming
that the given path or its projected generator is already identified.

The only external analytic data here concern the positive-lag analytic
operator `Tker` and an integrable off-diagonal majorant. In particular,
`hOffDiag` is a **norm** bound, not the desired generator equality. -/
theorem paper_A9_canonical_physical_pressure_causal_value_from_A5_and_DG
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (j : U →L[ℝ] Lp ℝ 2 μ)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    let S := ReservoirSeismicityControl.pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    let V : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range j.toLinearMap
    let Ew := ReservoirSeismicityControl.pressureA5CanonicalRangeEnergy j Eform hjinj
    let hsep := ReservoirSeismicityControl.pressure_A5_canonical_range_separates
      j hjinj hjDense
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    ∀ (T : NNReal) (p₀ : S.generatorDomain)
      (m : ℕ) (f : Fin m → Lp ℝ 2 μ) (q : Fin m → ℝ → ℝ)
      (hq : ∀ i : Fin m, Integrable (q i)
        (volume.restrict (Set.Ico 0 (T : ℝ))))
      (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
      (hBound : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i)
      (g : ℕ → Fin m → S.generatorDomain)
      (hgLimit : ∀ i : Fin m, Tendsto
        (fun n : ℕ => (g n i : Lp ℝ 2 μ)) atTop (𝓝 (f i)))
      (Tker : NNReal → ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hAnalytic : ∀ t : NNReal, t ≤ T →
        ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) (t : ℝ) →
          ∀ u : S.generatorDomain,
            P (S (Real.toNNReal ((t : ℝ) - s)) (S.generator u)) =
              Tker t s (u : Lp ℝ 2 μ))
      (b : NNReal → Fin m → ℝ → ℝ)
      (hbInt : ∀ t : NNReal, t ≤ T → ∀ i : Fin m,
        Integrable (b t i)
          (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))))
      (hOffDiag : ∀ t : NNReal, t ≤ T → ∀ i : Fin m, ∀ n : ℕ,
        ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))),
          ‖(q i s) • P
            (S (Real.toNNReal ((t : ℝ) - s)) (S.generator (g n i)))‖
              ≤ b t i s),
      ∃ p : ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        (∀ τ : ℝ, (((p τ : V) : Lp ℝ 2 μ)) =
          S (ReservoirSeismicityControl.pressureA5HorizonClip T τ) (p₀ : Lp ℝ 2 μ) +
            ReservoirSeismicityControl.pressureA5ForwardDuhamel S
              (ReservoirSeismicityControl.pressureA5HorizonClip T τ) m f q) ∧
        Continuous (fun τ : ℝ =>
          ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p τ)) ∧
        (∀ t : NNReal, t ≤ T →
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
            -(P (S t (S.generator p₀)) +
              ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
                (q i s) • Tker t s (f i))) := by
  classical
  intro S V Ew hsep P T p₀ m f q hq M hM hBound
    g hgLimit Tker hAnalytic b hbInt hOffDiag
  obtain ⟨hSelf, hGraph⟩ :=
    ReservoirSeismicityControl.pressure_dense_neumann_semigroup_selfadjoint_and_graph
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
  obtain ⟨p, hpCarrier, hpContinuous, hpPhysical⟩ :=
    paper_A9_physical_mild_projected_generator_identification
      μ far hfar j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      T p₀ m f q hq M hM hBound
  refine ⟨p, hpCarrier, hpContinuous, ?_⟩
  intro t ht
  have hqt : ∀ i : Fin m, Integrable (q i)
      (volume.restrict (Set.Ico 0 (t : ℝ))) := by
    intro i
    have hsub : Set.Ico (0 : ℝ) (t : ℝ) ⊆
        Set.Ico (0 : ℝ) (T : ℝ) := by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 (NNReal.coe_le_coe.mpr ht)⟩
    exact IntegrableOn.mono_set (hq i) hsub
  obtain ⟨hpDG, hDG⟩ :=
    paper_A9_actual_negative_generator_causal_value_of_analytic_DG
      μ far hfar S hSelf hGraph t p₀ m f q hqt M hM (hBound t ht)
      g hgLimit (Tker t) (hAnalytic t ht) (b t)
      (hbInt t ht) (hOffDiag t ht)
  obtain ⟨hpCan, hPhysicalValue⟩ := hpPhysical t ht
  have hSame :
      (⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpCan⟩ :
            S.generatorDomain) =
      (⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpDG⟩ :
            S.generatorDomain) := Subtype.ext rfl
  dsimp only at hDG
  calc
    P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
        -P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpCan⟩) :=
            hPhysicalValue
    _ = P (-(S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpDG⟩)) := by
            rw [hSame, map_neg]
    _ = -(P (S t (S.generator p₀)) +
          ∑ i : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            (q i s) • Tker t s (f i)) := hDG

#print axioms paper_A9_canonical_physical_pressure_causal_value_from_A5_and_DG

end ReservoirSeismicityControl.Paper2026
