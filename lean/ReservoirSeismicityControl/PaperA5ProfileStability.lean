import ReservoirSeismicityControl.PressurePositiveSemigroupA5ForwardPhysical
import ReservoirSeismicityControl.PaperA5GeneratorContinuityBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Stage 65: sharp A5 stability under spatial-profile perturbations

The well rates q_j are the *same* in both trajectories. Only the fixed
spatial forcing profiles f_j and g_j change. This isolates exactly the
spatial approximation error needed by Stage 64.

* We first prove linearity of the ACTUAL forward Bochner-Duhamel integral
  with respect to the spatial forcing profiles.
* We then apply the already verified forward A5 estimate to the difference
  profiles, using a zero initial difference, to bound the difference of the
  generator images by Sum_j M_j ‖f_j-g_j‖.

Neither proof invokes q_j', and the generator images refer to the actual
abstract self-adjoint Neumann semigroup. Integrability of the individual
Duhamel integrands is explicit. The physical A5 theorem supplies generator
domain membership for both profiles separately.

This does NOT prove that the smoothed-profile generator images are continuous.
That is the other missing premise of the Stage 64 uniform-limit theorem.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

section ProfileStability

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Linearity of the *actual forward* multiwell Duhamel term under changes
of the fixed spatial profiles. q_j may be merely integrable in time. -/
theorem pressure_A5_forward_Duhamel_profile_sub
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (m : ℕ) (f g : Fin m → H) (q : Fin m → ℝ → ℝ)
    (hf : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j))
      volume 0 (t : ℝ))
    (hg : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (g j))
      volume 0 (t : ℝ)) :
    pressureA5ForwardDuhamel S t m f q -
      pressureA5ForwardDuhamel S t m g q =
        pressureA5ForwardDuhamel S t m (fun j => f j - g j) q := by
  unfold pressureA5ForwardDuhamel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← intervalIntegral.integral_sub (hf j) (hg j)]
  congr 1
  funext s
  simp only [map_sub, smul_sub]

/-- The sharp bound on generator-image differences, derived using the
*proved* A5 estimate for the difference profiles. This is the desired
error estimate for the spatial regularization in Stage 64.

The domain hypotheses `hpF` and `hpG` are supplied by the preexisting
physical A5 theorem applied separately to f and g. -/
theorem pressure_A5_forward_generator_profile_stability
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f g : Fin m → H)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j, ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
      |q j s| ≤ M j)
    (hf : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j))
      volume 0 (t : ℝ))
    (hg : ∀ j : Fin m, IntervalIntegrable
      (fun s : ℝ => q j s • S (Real.toNNReal ((t : ℝ) - s)) (g j))
      volume 0 (t : ℝ))
    (hpF : (S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q)
      ∈ S.generatorDomain)
    (hpG : (S t (p₀ : H) + pressureA5ForwardDuhamel S t m g q)
      ∈ S.generatorDomain) :
    ‖S.generator ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q, hpF⟩ -
      S.generator ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m g q, hpG⟩‖ ≤
        ∑ j : Fin m, M j * ‖f j - g j‖ := by
  obtain ⟨hpD, hD⟩ := pressure_multiwell_A5_measurable_forward
    S hSelf hGraph t (0 : S.generatorDomain) m
    (fun j => f j - g j) q hq M hM hBound
  let PF : S.generatorDomain :=
    ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q, hpF⟩
  let PG : S.generatorDomain :=
    ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m g q, hpG⟩
  let PD : S.generatorDomain :=
    ⟨S t ((0 : S.generatorDomain) : H) +
      pressureA5ForwardDuhamel S t m (fun j => f j - g j) q, hpD⟩
  have hCarrier : ((PF - PG : S.generatorDomain) : H) = (PD : H) := by
    change (S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q) -
      (S t (p₀ : H) + pressureA5ForwardDuhamel S t m g q) =
      S t (0 : H) + pressureA5ForwardDuhamel S t m (fun j => f j - g j) q
    rw [map_zero, zero_add]
    calc
      (S t (p₀ : H) + pressureA5ForwardDuhamel S t m f q) -
          (S t (p₀ : H) + pressureA5ForwardDuhamel S t m g q) =
        pressureA5ForwardDuhamel S t m f q -
          pressureA5ForwardDuhamel S t m g q := by abel
      _ = pressureA5ForwardDuhamel S t m (fun j => f j - g j) q :=
        pressure_A5_forward_Duhamel_profile_sub S t m f g q hf hg
  have hEq : PF - PG = PD := Subtype.ext hCarrier
  calc
    ‖S.generator PF - S.generator PG‖ =
        ‖S.generator (PF - PG)‖ := by rw [map_sub]
    _ = ‖S.generator PD‖ := by rw [hEq]
    _ ≤ ∑ j : Fin m, M j * ‖f j - g j‖ := by
      simpa only [PD, map_zero, norm_zero, zero_add] using hD

end ProfileStability

end ReservoirSeismicityControl
