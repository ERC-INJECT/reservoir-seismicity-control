import ReservoirSeismicityControl.PaperA5SmoothGeneratorContinuity
import ReservoirSeismicityControl.PaperA5ProfileStability
import ReservoirSeismicityControl.PaperA5GeneratorContinuityBridge
import ReservoirSeismicityControl.PaperA5CausalLocalIntegrability
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Stage 73: strong continuity of the actual multiwell pressure generator (Fix 1)

The smooth-profile pressure generator has a continuous real-time representative
(Stage 72). Here we use density of the domain of the semigroup generator,
sharp physical A5 stability of its generator image (Stage 65), and the
uniform-limit theorem (Stage 64) to remove the smooth-profile requirement.

This gives continuity on any finite physical time horizon for arbitrary
fixed spatial L² forcing profiles and locally integrable, uniformly bounded
well-rate inputs. No time derivative of a well rate is assumed.

The hypotheses `hSelf` and `hGraph` are exactly the self-adjoint/weak-generator
properties used in the physical A5 bound. The generator of S is -A in the
paper's notation, so its strong continuity is equivalent to continuity of Ap.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace

section PhysicalGeneratorContinuity

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual generator image of the full physical multiwell pressure mild
solution admits a continuous representative on every finite horizon,
without any `Qdot` hypothesis and without requiring the spatial profiles to
lie in the generator domain.

The rate bound is stated on every subinterval of the horizon, as required
by the sharp A5 estimate. It follows from a single uniform a.e. bound on
`[0,T)`; this routine measure-restriction implication can also be provided
when applying this theorem to the physical well rates. -/
theorem pressure_A5_general_multiwell_generator_continuous_representative
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (T : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → H)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (T : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ t : NNReal, t ≤ T → ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))), |q j s| ≤ M j) :
    ∃ F : ℝ → H, Continuous F ∧
      ∀ t : NNReal, t ≤ T →
        ∃ hp : (S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q)
            ∈ S.generatorDomain,
          S.generator ⟨S t (p₀ : H) +
            pressureA5ForwardDuhamel S t m f q, hp⟩ = F (t : ℝ) := by
  classical
  have hSeq (j : Fin m) :
      ∃ a : ℕ → H, (∀ n, a n ∈ S.generatorDomain) ∧
        Tendsto a atTop (𝓝 (f j)) := by
    exact mem_closure_iff_seq_limit.mp (S.dense_generatorDomain (f j))
  let fApprox (n : ℕ) (j : Fin m) : S.generatorDomain :=
    ⟨(hSeq j).choose n, (hSeq j).choose_spec.1 n⟩
  have hApproxLimit (j : Fin m) :
      Tendsto (fun n : ℕ => (fApprox n j : H)) atTop (𝓝 (f j)) :=
    (hSeq j).choose_spec.2
  have hLocal (t : NNReal) (ht : t ≤ T) (j : Fin m) :
      Integrable (q j) (volume.restrict (Set.Ico 0 (t : ℝ))) := by
    have htr : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
    exact IntegrableOn.mono_set (hq j) (by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 htr⟩)
  have hInterval (t : NNReal) (ht : t ≤ T) (j : Fin m) :
      IntervalIntegrable (q j) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le
      (NNReal.coe_nonneg t)).2 (hLocal t ht j)
  let P : NNReal → H := fun t =>
    S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q
  have hPhysical (t : NNReal) (ht : t ≤ T) :
      P t ∈ S.generatorDomain := by
    have hA5 := pressure_multiwell_A5_measurable_forward
      S hSelf hGraph t p₀ m f q (hLocal t ht) M hM (hBound t ht)
    exact hA5.choose
  have hSmooth (n : ℕ) :
      ∃ G : ℝ → H, Continuous G ∧
        ∀ t : NNReal, t ≤ T →
          ∃ hp : (S t (p₀ : H) +
              pressureA5ForwardDuhamel S t m
                (fun j => (fApprox n j : H)) q) ∈ S.generatorDomain,
            S.generator ⟨S t (p₀ : H) +
              pressureA5ForwardDuhamel S t m
                (fun j => (fApprox n j : H)) q, hp⟩ = G (t : ℝ) :=
    pressure_A5_smooth_multiwell_generator_continuous_representative
      S T p₀ m (fApprox n) q hq
  let clip : ℝ → NNReal := fun τ => min (Real.toNNReal τ) T
  have hClip : Continuous (fun τ : ℝ => (clip τ : ℝ)) := by
    dsimp [clip]
    exact NNReal.continuous_coe.comp
      (continuous_real_toNNReal.min continuous_const)
  let GApprox : ℕ → ℝ → H := fun n τ => (hSmooth n).choose (clip τ : ℝ)
  have hGApprox (n : ℕ) : Continuous (GApprox n) :=
    (hSmooth n).choose_spec.1.comp hClip
  let Ap : ℝ → H := fun τ =>
    S.generator ⟨P (clip τ), hPhysical (clip τ) (min_le_right _ _)⟩
  let e : ℕ → ℝ := fun n =>
    ∑ j : Fin m, M j * ‖f j - (fApprox n j : H)‖
  have he (j : Fin m) :
      Tendsto (fun n : ℕ => ‖f j - (fApprox n j : H)‖) atTop (𝓝 0) := by
    have hconstant :
        Tendsto (fun _ : ℕ => f j) atTop (𝓝 (f j)) :=
      tendsto_const_nhds
    have hdiff :
        Tendsto (fun n : ℕ => f j - (fApprox n j : H))
          atTop (𝓝 (f j - f j)) :=
      hconstant.sub (hApproxLimit j)
    simpa only [sub_self, norm_zero] using hdiff.norm
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n : ℕ => ∑ j : Fin m,
          M j * ‖f j - (fApprox n j : H)‖)
        atTop (𝓝 (∑ j : Fin m, (0 : ℝ))) := by
      apply tendsto_finsetSum Finset.univ
      intro j _
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (he j) :
          Tendsto (fun n : ℕ => M j * ‖f j - (fApprox n j : H)‖)
            atTop (𝓝 (M j * 0)))
    simpa only [e, Finset.sum_const_zero] using hsum
  have hUniform (n : ℕ) (τ : ℝ) :
      ‖Ap τ - GApprox n τ‖ ≤ e n := by
    let t : NNReal := clip τ
    have ht : t ≤ T := min_le_right _ _
    have hSmoothAt := (hSmooth n).choose_spec.2 t ht
    obtain ⟨hpSmooth, hgenSmooth⟩ := hSmoothAt
    have hForward (j : Fin m) : IntervalIntegrable
        (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j))
          volume 0 (t : ℝ) :=
      pressure_A5_forward_orbit_intervalIntegrable
        S t (q j) (f j) (hInterval t ht j)
    have hRegular (j : Fin m) : IntervalIntegrable
        (fun s : ℝ => q j s •
          S (Real.toNNReal ((t : ℝ) - s)) (fApprox n j : H))
          volume 0 (t : ℝ) :=
      pressure_A5_forward_orbit_intervalIntegrable
        S t (q j) (fApprox n j : H) (hInterval t ht j)
    have hStable := pressure_A5_forward_generator_profile_stability
      S hSelf hGraph t p₀ m f (fun j => (fApprox n j : H)) q
      (hLocal t ht) M hM (hBound t ht) hForward hRegular
      (hPhysical t ht) hpSmooth
    have hGen : GApprox n τ =
        S.generator ⟨S t (p₀ : H) +
          pressureA5ForwardDuhamel S t m
            (fun j => (fApprox n j : H)) q, hpSmooth⟩ := by
      exact hgenSmooth.symm
    have hOriginal : Ap τ =
        S.generator ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q,
          hPhysical t ht⟩ := by
      rfl
    simpa only [e, hGen, hOriginal] using hStable
  have hAp : Continuous Ap := by
    apply paper_neumann_generator_continuous_of_uniform_A5_approximants
      Ap GApprox 1 e hGApprox
    · intro n τ
      simpa using hUniform n τ
    · exact he0
  refine ⟨Ap, hAp, ?_⟩
  intro t ht
  refine ⟨hPhysical t ht, ?_⟩
  have hClipAt : clip (t : ℝ) = t := by
    simp [clip, min_eq_left ht]
  have hSubtype :
      (⟨P t, hPhysical t ht⟩ : S.generatorDomain) =
        ⟨P (clip (t : ℝ)),
          hPhysical (clip (t : ℝ)) (min_le_right _ _)⟩ := by
    apply Subtype.ext
    change P t = P (clip (t : ℝ))
    rw [hClipAt]
  exact congrArg S.generator hSubtype

end PhysicalGeneratorContinuity
end ReservoirSeismicityControl

#print axioms ReservoirSeismicityControl.pressure_A5_general_multiwell_generator_continuous_representative
