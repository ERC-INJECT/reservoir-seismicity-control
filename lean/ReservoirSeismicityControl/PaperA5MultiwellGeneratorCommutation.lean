import ReservoirSeismicityControl.PaperA5GeneratorDuhamelCommutation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Stage 71: generator commutation for the entire finite-well pressure solution

Stage 70 proved the exact generator/Bochner-integral interchange for one
fixed well profile in the generator domain and a locally integrable input.
This module proves the corresponding statement for all wells, and also
includes the free semigroup orbit of the initial pressure.

No derivative of the well inputs is assumed. The theorem is for **smooth
spatial well profiles** in `S.generatorDomain`; extending it to general L²
profiles uses the approximation estimate of Stage 65 and continuity from
Stages 64 and 66–69, and is a separate task.

The semigroup generator `L = S.generator` is `-A` in the paper's notation.
The sign does not affect the commutation identity.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal BigOperators

section MultiwellGenerator

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For a finite family of spatial profiles in the generator domain, the
actual forward multiwell Duhamel integral belongs to the generator domain,
and its generator equals the same forward integral with generator-applied
profiles. This is derived by summing Stage 70's one-well results. -/
theorem pressure_A5_forward_generator_commutes_multiwell
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (m : ℕ) (f : Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, IntervalIntegrable (q j) volume 0 (t : ℝ)) :
    ∃ hu : pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q
        ∈ S.generatorDomain,
      S.generator ⟨pressureA5ForwardDuhamel S t m
          (fun j => (f j : H)) q, hu⟩ =
        pressureA5ForwardDuhamel S t m
          (fun j => S.generator (f j)) q := by
  classical
  have hOne (j : Fin m) :
      ∃ hu : (∫ s in (0 : ℝ)..(t : ℝ),
          q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j : H))
            ∈ S.generatorDomain,
        S.generator ⟨∫ s in (0 : ℝ)..(t : ℝ),
            q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j : H), hu⟩ =
          ∫ s in (0 : ℝ)..(t : ℝ),
            q j s • S (Real.toNNReal ((t : ℝ) - s))
              (S.generator (f j)) :=
    pressure_A5_forward_generator_commutes_onewell S t (f j) (q j) (hq j)
  let F (j : Fin m) : S.generatorDomain :=
    ⟨∫ s in (0 : ℝ)..(t : ℝ),
        q j s • S (Real.toNNReal ((t : ℝ) - s)) (f j : H),
      (hOne j).choose⟩
  have hF (j : Fin m) :
      S.generator (F j) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          q j s • S (Real.toNNReal ((t : ℝ) - s))
            (S.generator (f j)) :=
    (hOne j).choose_spec
  have hCarrier :
      (((∑ j : Fin m, F j) : S.generatorDomain) : H) =
        pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q := by
    simp only [Submodule.coe_sum, pressureA5ForwardDuhamel]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hMem : pressureA5ForwardDuhamel S t m
      (fun j => (f j : H)) q ∈ S.generatorDomain := by
    rw [← hCarrier]
    exact (∑ j : Fin m, F j).property
  refine ⟨hMem, ?_⟩
  have hSubtype :
      (⟨pressureA5ForwardDuhamel S t m
          (fun j => (f j : H)) q, hMem⟩ : S.generatorDomain) =
        ∑ j : Fin m, F j := by
    apply Subtype.ext
    exact hCarrier.symm
  calc
    S.generator ⟨pressureA5ForwardDuhamel S t m
        (fun j => (f j : H)) q, hMem⟩ =
        S.generator (∑ j : Fin m, F j) :=
      congrArg S.generator hSubtype
    _ = ∑ j : Fin m, S.generator (F j) := by rw [map_sum]
    _ = pressureA5ForwardDuhamel S t m
          (fun j => S.generator (f j)) q := by
      unfold pressureA5ForwardDuhamel
      exact Finset.sum_congr rfl (fun j _ => hF j)

/-- Generator identity for the **whole** finite-well mild solution, with
initial pressure and smooth spatial well profiles. It proves its domain
membership, rather than assuming the solution is a classical trajectory. -/
theorem pressure_A5_full_generator_commutes_smooth_multiwell
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, IntervalIntegrable (q j) volume 0 (t : ℝ)) :
    ∃ hp : (S t (p₀ : H) +
        pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q)
          ∈ S.generatorDomain,
      S.generator ⟨S t (p₀ : H) +
          pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q, hp⟩ =
        S t (S.generator p₀) +
          pressureA5ForwardDuhamel S t m
            (fun j => S.generator (f j)) q := by
  obtain ⟨hD, hCommutation⟩ :=
    pressure_A5_forward_generator_commutes_multiwell S t m f q hq
  let P₀ : S.generatorDomain :=
    ⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩
  let D : S.generatorDomain :=
    ⟨pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q, hD⟩
  have hMem : (S t (p₀ : H) +
      pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q)
        ∈ S.generatorDomain := by
    change ((P₀ + D : S.generatorDomain) : H) ∈ S.generatorDomain
    exact (P₀ + D).property
  refine ⟨hMem, ?_⟩
  have hSubtype :
      (⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m
          (fun j => (f j : H)) q, hMem⟩ : S.generatorDomain) = P₀ + D := by
    apply Subtype.ext
    rfl
  have hInitial : S.generator P₀ = S t (S.generator p₀) :=
    S.generator_operator p₀ t
  calc
    S.generator ⟨S t (p₀ : H) + pressureA5ForwardDuhamel S t m
        (fun j => (f j : H)) q, hMem⟩ = S.generator (P₀ + D) :=
      congrArg S.generator hSubtype
    _ = S.generator P₀ + S.generator D := by rw [map_add]
    _ = S t (S.generator p₀) +
          pressureA5ForwardDuhamel S t m
            (fun j => S.generator (f j)) q :=
      congrArg₂ (· + ·) hInitial hCommutation

/-- The whole-pressure theorem in the exact finite-interval form used by
the physical bounded-measurable well-rate assumption. -/
theorem pressure_A5_full_generator_commutes_of_local_rates
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → S.generatorDomain)
    (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ)))) :
    ∃ hp : (S t (p₀ : H) +
        pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q)
          ∈ S.generatorDomain,
      S.generator ⟨S t (p₀ : H) +
          pressureA5ForwardDuhamel S t m (fun j => (f j : H)) q, hp⟩ =
        S t (S.generator p₀) +
          pressureA5ForwardDuhamel S t m
            (fun j => S.generator (f j)) q := by
  have hInterval (j : Fin m) :
      IntervalIntegrable (q j) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le
      (NNReal.coe_nonneg t)).2 (hq j)
  exact pressure_A5_full_generator_commutes_smooth_multiwell S t p₀ m f q hInterval

end MultiwellGenerator

end ReservoirSeismicityControl

/- Axiom audit for the newly connected Stage 70–71 generator results.
Expected standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
Any `sorryAx` or custom axiom requires investigation. -/
#print axioms ReservoirSeismicityControl.pressure_A5_generator_integral_commutes
#print axioms ReservoirSeismicityControl.pressure_A5_generator_interval_integral_commutes
#print axioms ReservoirSeismicityControl.pressure_A5_forward_generator_commutes_onewell
#print axioms ReservoirSeismicityControl.pressure_A5_forward_generator_commutes_multiwell
#print axioms ReservoirSeismicityControl.pressure_A5_full_generator_commutes_smooth_multiwell
#print axioms ReservoirSeismicityControl.pressure_A5_full_generator_commutes_of_local_rates
