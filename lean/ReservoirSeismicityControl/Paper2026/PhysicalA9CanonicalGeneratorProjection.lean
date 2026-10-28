import ReservoirSeismicityControl.PaperA5CanonicalPhysicalWeakPath
import ReservoirSeismicityControl.PaperA5CanonicalWeakRange
import ReservoirSeismicityControl.Paper2026.PhysicalA9ProjectedFullLimit
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): projected generator of the actual physical mild pressure

Use the PREVIOUSLY PROVED canonical A5 weak pressure path, whose carrier is
exactly the physical multiwell Duhamel solution. Identify its far-projected
weak Neumann image with minus the far-projected generator of that *same*
physical mild state. No derivative of the well rates is assumed.

This does NOT yet identify that generator with the full zero-lag causal
forcing integral; that remains the next genuinely missing A9 connection.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped NNReal InnerProductSpace BigOperators

/-- The physical mild pressure from A5 has a canonical weak Neumann
representative. Its far projection agrees exactly with the projected
negative generator of the *physical* finite-well semigroup trajectory.
No assertion concerning the causal A9 derivative is assumed here. -/
theorem paper_A9_physical_mild_projected_generator_identification
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
        ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q i s| ≤ M i),
      ∃ p : ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        (∀ τ : ℝ, (((p τ : V) : Lp ℝ 2 μ)) =
          S (ReservoirSeismicityControl.pressureA5HorizonClip T τ) (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S
            (ReservoirSeismicityControl.pressureA5HorizonClip T τ) m f q) ∧
        Continuous (fun τ : ℝ =>
          ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p τ)) ∧
        (∀ t : NNReal, t ≤ T →
          ∃ hphysical :
            (S t (p₀ : Lp ℝ 2 μ) +
              ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈
              S.generatorDomain,
            P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
              -P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
                ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hphysical⟩)) := by
  intro S V Ew hsep P T p₀ m f q hq M hM hBound
  obtain ⟨p, hpCarrier, hpContinuous⟩ :=
    ReservoirSeismicityControl.pressure_A5_canonical_physical_weak_path_exists
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      T p₀ m f q hq M hM hBound
  refine ⟨p, hpCarrier, hpContinuous, ?_⟩
  intro t ht
  have hclip : ReservoirSeismicityControl.pressureA5HorizonClip T (t : ℝ) = t := by
    simp [ReservoirSeismicityControl.pressureA5HorizonClip, min_eq_left ht]
  have hstate : (((p (t : ℝ) : V) : Lp ℝ 2 μ)) =
      S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q := by
    simpa only [hclip] using hpCarrier (t : ℝ)
  have hpGen : (((p (t : ℝ) : V) : Lp ℝ 2 μ)) ∈
      S.generatorDomain := by
    apply (ReservoirSeismicityControl.pressure_A5_canonical_range_domain_iff_generator_domain
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      (((p (t : ℝ) : V) : Lp ℝ 2 μ))).mp
    exact ⟨p (t : ℝ), rfl⟩
  have hphysical :
      (S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈
        S.generatorDomain := by
    rw [← hstate]
    exact hpGen
  have hoperator :=
    ReservoirSeismicityControl.pressure_A5_canonical_range_operator_eq_neg_generator
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      (p (t : ℝ)) hpGen
  have hsubtype :
      (⟨(((p (t : ℝ) : V) : Lp ℝ 2 μ)), hpGen⟩ : S.generatorDomain) =
      ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hphysical⟩ :=
    Subtype.ext hstate
  refine ⟨hphysical, ?_⟩
  calc
    P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (p (t : ℝ))) =
        P (-S.generator ⟨(((p (t : ℝ) : V) : Lp ℝ 2 μ)), hpGen⟩) := by
          exact congrArg P hoperator
    _ = -P (S.generator ⟨(((p (t : ℝ) : V) : Lp ℝ 2 μ)), hpGen⟩) := by
      rw [map_neg]
    _ = -P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hphysical⟩) := by
      rw [hsubtype]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_mild_projected_generator_identification
