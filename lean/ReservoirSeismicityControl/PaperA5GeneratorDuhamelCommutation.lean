import ReservoirSeismicityControl.PaperA5CausalLocalIntegrability
import MarkovProcess.Semigroup.Resolvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Stage 70: closed-generator interchange with physical Duhamel integrals

The generator of a strongly continuous contraction semigroup is unbounded,
so commuting it with a Bochner integral cannot be justified by the continuous
linear map integral lemma alone. We instead use the already formalized bounded
positive resolvent, which preserves Bochner integrals and inverts `shift - L`.

The abstract theorem below derives generator-domain membership of the
integral, together with the exact generator/integral commutation, from
integrability of the vector-valued integrands `F` and `L F`. The specialized
theorem verifies those integrability conditions for the *actual* physical
forward-time semigroup orbit with a fixed spatial well profile in the
generator domain and merely locally integrable scalar rate.

No regularity of the time derivative of a well rate is assumed.
Here `S.generator` has the opposite sign from the positive diffusion operator
`A` of the manuscript. The commutation identity holds for either sign.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped NNReal BigOperators

section GeneratorIntegral

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The closed generator commutes with the Bochner integral of a domain-valued
map, provided the map and its generator image are both Bochner integrable.
The proof uses a *bounded resolvent*, not continuity of the generator. -/
theorem pressure_A5_generator_integral_commutes
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure ℝ) (F : ℝ → S.generatorDomain)
    (hF : Integrable (fun s : ℝ => (F s : H)) μ)
    (hLF : Integrable (fun s : ℝ => S.generator (F s)) μ) :
    ∃ hu : (∫ s : ℝ, (F s : H) ∂μ) ∈ S.generatorDomain,
      S.generator ⟨∫ s : ℝ, (F s : H) ∂μ, hu⟩ =
        ∫ s : ℝ, S.generator (F s) ∂μ := by
  let shift : MarkovProcess.Semigroup.PositiveShift := ⟨1, by norm_num⟩
  have hSmul : Integrable (fun s : ℝ => (shift : ℝ) • (F s : H)) μ := by
    have hfun :
        ((shift : ℝ) • (fun s : ℝ => (F s : H))) =
          (fun s : ℝ => (shift : ℝ) • (F s : H)) := by
      funext s
      simp only [Pi.smul_apply]
    exact hfun ▸ (hF.smul (shift : ℝ))
  have hG : Integrable
      (fun s : ℝ => (shift : ℝ) • (F s : H) - S.generator (F s)) μ :=
    hSmul.sub hLF
  -- State the vector-integral identity separately. Rewriting with an
  -- unelaborated `hF.smul` leaves a function-level smul in the pattern,
  -- which need not match the pointwise-smul integral syntactically.
  have hIntegral :
      (∫ s : ℝ, ((shift : ℝ) • (F s : H) - S.generator (F s)) ∂μ) =
        (shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
          (∫ s : ℝ, S.generator (F s) ∂μ) := by
    calc
      _ = (∫ s : ℝ, (shift : ℝ) • (F s : H) ∂μ) -
            (∫ s : ℝ, S.generator (F s) ∂μ) :=
          integral_sub hSmul hLF
      _ = (shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
            (∫ s : ℝ, S.generator (F s) ∂μ) := by
          rw [integral_smul]
  have hR :
      S.resolvent shift
        ((shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
          (∫ s : ℝ, S.generator (F s) ∂μ)) =
        ∫ s : ℝ, (F s : H) ∂μ := by
    calc
      S.resolvent shift
          ((shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
            (∫ s : ℝ, S.generator (F s) ∂μ)) =
          S.resolvent shift
            (∫ s : ℝ, ((shift : ℝ) • (F s : H) - S.generator (F s)) ∂μ) := by
        exact congrArg (S.resolvent shift) hIntegral.symm
      _ = ∫ s : ℝ,
          S.resolvent shift ((shift : ℝ) • (F s : H) - S.generator (F s)) ∂μ := by
        exact (ContinuousLinearMap.integral_comp_comm (S.resolvent shift) hG).symm
      _ = ∫ s : ℝ, (F s : H) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
          S.resolvent_smul_sub_generator shift (F s))
  have hdom : (∫ s : ℝ, (F s : H) ∂μ) ∈ S.generatorDomain := by
    rw [← hR]
    exact S.resolvent_mem_generatorDomain shift _
  refine ⟨hdom, ?_⟩
  calc
    S.generator ⟨∫ s : ℝ, (F s : H) ∂μ, hdom⟩ =
        (shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
          ((shift : ℝ) • (∫ s : ℝ, (F s : H) ∂μ) -
            ∫ s : ℝ, S.generator (F s) ∂μ) :=
      S.generator_eq_of_resolvent_eq shift hdom hR
    _ = ∫ s : ℝ, S.generator (F s) ∂μ := by abel

/-- The generator commutation theorem on a physical forward-time interval.
This is derived from the previous Bochner-integral theorem and the verified
identity between `Ico` integrals and oriented interval integrals. -/
theorem pressure_A5_generator_interval_integral_commutes
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (F : ℝ → S.generatorDomain)
    (hF : IntervalIntegrable (fun s : ℝ => (F s : H)) volume 0 (t : ℝ))
    (hLF : IntervalIntegrable (fun s : ℝ => S.generator (F s)) volume 0 (t : ℝ)) :
    ∃ hu : (∫ s in (0 : ℝ)..(t : ℝ), (F s : H)) ∈ S.generatorDomain,
      S.generator ⟨∫ s in (0 : ℝ)..(t : ℝ), (F s : H), hu⟩ =
        ∫ s in (0 : ℝ)..(t : ℝ), S.generator (F s) := by
  have hF' : Integrable (fun s : ℝ => (F s : H))
      (volume.restrict (Set.Ico 0 (t : ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le (NNReal.coe_nonneg t)).1 hF
  have hLF' : Integrable (fun s : ℝ => S.generator (F s))
      (volume.restrict (Set.Ico 0 (t : ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le (NNReal.coe_nonneg t)).1 hLF
  obtain ⟨hdom, hgen⟩ := pressure_A5_generator_integral_commutes
    S (volume.restrict (Set.Ico 0 (t : ℝ))) F hF' hLF'
  -- Avoid rewriting inside a subtype whose domain-membership proof
  -- depends on the integral being rewritten.
  have hforward :
      (∫ s in (0 : ℝ)..(t : ℝ), (F s : H)) ∈ S.generatorDomain := by
    simpa only [pressure_A5_integral_Ico_eq_interval t
      (fun s : ℝ => (F s : H))] using hdom
  refine ⟨hforward, ?_⟩
  have hSubtypeEq :
      (⟨∫ s in (0 : ℝ)..(t : ℝ), (F s : H), hforward⟩ : S.generatorDomain) =
        ⟨∫ s in Set.Ico (0 : ℝ) (t : ℝ), (F s : H), hdom⟩ := by
    apply Subtype.ext
    exact (pressure_A5_integral_Ico_eq_interval t
      (fun s : ℝ => (F s : H))).symm
  calc
    S.generator ⟨∫ s in (0 : ℝ)..(t : ℝ), (F s : H), hforward⟩ =
        S.generator ⟨∫ s in Set.Ico (0 : ℝ) (t : ℝ), (F s : H), hdom⟩ :=
      congrArg S.generator hSubtypeEq
    _ = ∫ s in Set.Ico (0 : ℝ) (t : ℝ), S.generator (F s) := hgen
    _ = ∫ s in (0 : ℝ)..(t : ℝ), S.generator (F s) :=
      pressure_A5_integral_Ico_eq_interval t (fun s : ℝ => S.generator (F s))

/-- Physical one-well Duhamel generator commutation. The profile is a
member of the generator domain, and the actual well rate is only locally
integrable. Unlike an abstract operator interchange hypothesis, the domain
membership of the forward integral is proved here. -/
theorem pressure_A5_forward_generator_commutes_onewell
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (t : NNReal) (f : S.generatorDomain) (q : ℝ → ℝ)
    (hq : IntervalIntegrable q volume 0 (t : ℝ)) :
    ∃ hu : (∫ s in (0 : ℝ)..(t : ℝ),
          q s • S (Real.toNNReal ((t : ℝ) - s)) (f : H)) ∈ S.generatorDomain,
      S.generator ⟨∫ s in (0 : ℝ)..(t : ℝ),
          q s • S (Real.toNNReal ((t : ℝ) - s)) (f : H), hu⟩ =
        ∫ s in (0 : ℝ)..(t : ℝ),
          q s • S (Real.toNNReal ((t : ℝ) - s)) (S.generator f) := by
  let F : ℝ → S.generatorDomain := fun s =>
    q s • ⟨S (Real.toNNReal ((t : ℝ) - s)) (f : H),
      S.operator_mem_generatorDomain f (Real.toNNReal ((t : ℝ) - s))⟩
  have hFpoint (s : ℝ) :
      (F s : H) = q s • S (Real.toNNReal ((t : ℝ) - s)) (f : H) := by
    simp only [F, Submodule.coe_smul]
  have hLFpoint (s : ℝ) :
      S.generator (F s) = q s • S (Real.toNNReal ((t : ℝ) - s)) (S.generator f) := by
    simp only [F, map_smul, S.generator_operator]
  have hF : IntervalIntegrable (fun s : ℝ => (F s : H)) volume 0 (t : ℝ) := by
    simpa only [hFpoint] using
      pressure_A5_forward_orbit_intervalIntegrable S t q (f : H) hq
  have hLF : IntervalIntegrable (fun s : ℝ => S.generator (F s)) volume 0 (t : ℝ) := by
    simpa only [hLFpoint] using
      pressure_A5_forward_orbit_intervalIntegrable S t q (S.generator f) hq
  simpa only [hFpoint, hLFpoint] using
    (pressure_A5_generator_interval_integral_commutes S t F hF hLF)

end GeneratorIntegral

end ReservoirSeismicityControl
