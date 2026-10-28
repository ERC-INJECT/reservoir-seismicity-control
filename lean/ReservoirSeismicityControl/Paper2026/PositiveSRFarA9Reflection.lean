import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9Causal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (A9): positive-lag to causal time reversal

The positive-lag `L¹` estimate from the locally verified A8 theorem is
transported to the physical causal interval by the standard Lebesgue
change of variables `s ↦ t-s`. In particular, the existing A9 causal
bound no longer needs independent time-reversed kernel-integrability or
kernel-mass hypotheses.

No semigroup estimates are reproved. Their physical applicability is the
same explicit prerequisite as in A8. Identifying the *actual* far
observation derivative with the (A9) causal formula remains OPEN.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace

/-- Reflection on a finite causal interval: positive-lag `L¹` suffices.
This is standard interval-integral change-of-variables, not a new PDE
assumption. -/
theorem paper_A9_lag_reflection
    (k : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hk : Integrable k ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    Integrable (fun s => k (t - s))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) ∧
    (∫ s in Set.Ioc (0 : ℝ) t, |k (t - s)|) =
      (∫ s in Set.Ioc (0 : ℝ) t, |k s|) := by
  have hsubset : Set.Ioc (0 : ℝ) t ⊆ Set.Ioi (0 : ℝ) :=
    fun _ hx => hx.1
  have hlocal : IntegrableOn k (Set.Ioc (0 : ℝ) t) volume := by
    exact hk.mono_measure
      (Measure.restrict_mono_set (volume : Measure ℝ) hsubset)
  have hint : IntervalIntegrable k volume (0 : ℝ) t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hlocal
  have hrev : IntervalIntegrable (fun s => k (t - s)) volume (0 : ℝ) t := by
    have h := (hint.comp_sub_left t).symm
    simpa only [sub_self, sub_zero] using h
  have hkintegrable : Integrable (fun s => k (t - s))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hrev
  have hchange : (∫ s in (0 : ℝ)..t, |k (t - s)|) =
      (∫ s in (0 : ℝ)..t, |k s|) := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (fun s => |k s|) t
        (a := (0 : ℝ)) (b := t))
  constructor
  · exact hkintegrable
  · simpa only [intervalIntegral.integral_of_le ht] using hchange

/-- Restrict the causal mass to the positive-lag mass using only
nonnegativity and monotonicity of Lebesgue integration. -/
theorem paper_A9_lag_mass_le_positive
    (k : ℝ → ℝ) (t : ℝ) :
    Integrable k ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) →
    (∫ s in Set.Ioc (0 : ℝ) t, |k s|) ≤
      (∫ s in Set.Ioi (0 : ℝ), |k s|) := by
  intro hk
  have hsubset : Set.Ioc (0 : ℝ) t ⊆ Set.Ioi (0 : ℝ) :=
    fun _ hx => hx.1
  exact integral_mono_measure
    (Measure.restrict_mono_set (volume : Measure ℝ) hsubset)
    (Filter.Eventually.of_forall (fun s => abs_nonneg (k s)))
    hk.abs

/-- The physical A9 causal *bound* with both causal L¹ hypotheses removed.
The only lag-envelope inputs are those already needed by the A8 theorem. -/
theorem paper_sr_smooth_far_A9_causal_bound_from_A8_L1
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star Cγ CR MR : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hR : ∀ τ, ‖R τ‖ ≤ MR)
    (hderiv : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot τ) τ)
    (hrate : ∀ᵐ τ ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot τ‖ ≤ CR)
    (ζ : X → ℝ)
    (hfar : MeasurableSet {x : X | ζ x ≠ 1})
    (hcutoff : ∀ τ : ℝ, ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
        gamma10 R0star τ)) x : ℝ) =
        ζ x * ((paperSRDiffusionWeight μ region hregion Kγ R
          gamma10 R0star τ) x : ℝ))
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (well : Fin n → Set X) (dsep : ℝ)
    (hnear : ∀ (j : Fin n) (x y : X),
      y ∈ well j → dist x y < dsep → ζ x = 1)
    (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin n → ℝ → Lp ℝ 2 μ)
    (B₀ B₁ : Fin n → ℝ → ℝ)
    (hB₀ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₀ j s)
    (hB₁ : ∀ j : Fin n, ∀ s : ℝ, 0 < s → 0 ≤ B₁ j s)
    (hProjectedOrbit : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j s))‖ ≤
          B₀ j s)
    (hProjectedSecond : ∀ j : Fin n, ∀ s : ℝ, 0 < s →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j s)‖ ≤ B₁ j s)
    (C₀ : Fin n → ℝ)
    (hB₀Bound : ∀ j : Fin n, ∀ s : ℝ, 0 < s → B₀ j s ≤ C₀ j)
    (t initial : ℝ) (ht : 0 < t)
    (Q : Fin n → ℝ → ℝ) (M : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hQ : ∀ j : Fin n, ∀ s : ℝ, |Q j s| ≤ M j)
    (hB₁Integrable : ∀ j : Fin n,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hLagRateMeasurable : ∀ (observation : ℝ) (j : Fin n),
      AEStronglyMeasurable
        (fun s => ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
          (paperSRFarDiffusionWeight μ region hregion Kγ R
            gamma10 R0star cutoff) second observation j s)
        (volume.restrict (Set.Ioi (0 : ℝ))))
 :
    let Lw := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
      ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
    |ReservoirSeismicityControl.paperFarCausalKernelRate t initial
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| ≤
      |initial| + ∑ j : Fin n,
        M j * (Lw * C₀ j +
          Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)) := by
  let Lw : ℝ := |1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR) +
    ‖cutoff‖ * (|1 / (gamma10 * R0star * μ.real region)| * (Cγ * MR))
  let lag (j : Fin n) (s : ℝ) : ℝ :=
    ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
      (paperSRFarDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff) second t j s
  let K₁ : Fin n → ℝ := fun j =>
    Lw * (∫ s in Set.Ioi (0 : ℝ), B₁ j s)
  have hA8 (j : Fin n) :
      Integrable (lag j) (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∫ s in Set.Ioi (0 : ℝ), |lag j s|) ≤ K₁ j := by
    have h := paper_sr_smooth_far_A8_lag_rate_integrable
      μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
      cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
      V E hsep well dsep hnear orbit second B₀ B₁
      hB₀ hB₁ hProjectedOrbit hProjectedSecond
      hB₁Integrable hLagRateMeasurable t j
    exact h
  have hCausal (j : Fin n) :
      Integrable (fun s => lag j (t - s))
        (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
      (∫ s in Set.Ioc (0 : ℝ) t, |lag j (t - s)|) ≤ K₁ j := by
    have hr := paper_A9_lag_reflection (lag j) t ht.le (hA8 j).1
    refine ⟨hr.1, ?_⟩
    calc
      (∫ s in Set.Ioc (0 : ℝ) t, |lag j (t - s)|) =
          (∫ s in Set.Ioc (0 : ℝ) t, |lag j s|) := hr.2
      _ ≤ (∫ s in Set.Ioi (0 : ℝ), |lag j s|) :=
        paper_A9_lag_mass_le_positive (lag j) t (hA8 j).1
      _ ≤ K₁ j := (hA8 j).2
  change |ReservoirSeismicityControl.paperFarCausalKernelRate t initial
      (paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t)
      (ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
        (paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff) second t) Q| ≤
      |initial| + ∑ j : Fin n, M j * (Lw * C₀ j + K₁ j)
  exact paper_sr_smooth_far_A9_causal_bound_from_A8_value
    μ region hregion Kγ R Rdot gamma10 R0star Cγ CR MR
    cutoff hCγ hK hR hderiv hrate ζ hfar hcutoff
    V E hsep well dsep hnear orbit second B₀ B₁
    hB₀ hB₁ hProjectedOrbit hProjectedSecond C₀ hB₀Bound
    t initial ht Q M K₁ hM hQ
    (fun j => (hCausal j).1) (fun j => (hCausal j).2)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_lag_reflection
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_lag_mass_le_positive
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_smooth_far_A9_causal_bound_from_A8_L1
