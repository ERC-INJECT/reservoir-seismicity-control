import ReservoirSeismicityControl.Paper2026.PhysicalA9VectorL1Bridge20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9PositiveTimeApplicability20261025
import Mathlib.Tactic

/-!
# A9: applying the vector L1 bridge to the actual physical far-field forcing

This is an application of the previously PASSED vector-convolution lemma to
manuscript equation (A9). It discharges THREE premises of the prior exact
four-term A9 theorem:

  * hForcingRate is derived from the vector W1,1 approximants;
  * hBochner follows from global projected-vector integrability and the
    causal kernel identity;
  * hR follows from the physical SR Caratheodory integral evolution.

The W1,1 approximants are the standard external smooth approximation of the
positive-lag projected Neumann kernel, whose W1,1 estimate is given by the
manuscript-cited analytic-semigroup/Davies--Gaffney bounds. The assumptions
hForcingValue / hRateCausal are CAUSAL VALUE identifications,
not derivative or A9 assumptions; they are to be instantiated from the
previously verified physical semigroup path and the zero-lag support.

NO hypothesis on Qdot, NO new PDE proof, NO new generic convolution theorem.
This statement remains conditional until its physical source/semigroup
hypotheses are instantiated. A successful Lean build does not imply them.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000


/-- Physical causality for an L²-valued kernel: full-line convolution
of the zero-extended well rate with the zero-extended positive-lag
kernel equals the physical interval integral. This reuses the exact
indicator argument already proved in `PaperA5CausalConvolutionIdentity`;
it does not use a derivative of the well rate or prove any PDE estimate. -/
theorem paper_A9_vector_full_line_equals_physical_causal
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (Q qext : Fin m → ℝ → ℝ)
    (kernel physical : Fin m → ℝ → Lp ℝ 2 μ)
    (hQext : ∀ j s, qext j s = if 0 ≤ s then Q j s else 0)
    (hKernelPos : ∀ j lag, 0 < lag → kernel j lag = physical j lag)
    (hKernelZero : ∀ j lag, lag ≤ 0 → kernel j lag = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ j : Fin m, ∫ s : ℝ, qext j s • kernel j (t - s)) =
      (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
        Q j s • physical j (t - s)) := by
  apply Finset.sum_congr rfl
  intro j _
  have hpoint (s : ℝ) :
      qext j s • kernel j (t - s) =
      (Set.Ico (0 : ℝ) t).indicator
        (fun y : ℝ => Q j y • physical j (t - y)) s := by
    by_cases hs : s ∈ Set.Ico (0 : ℝ) t
    · rw [Set.indicator_of_mem hs, hQext j s,
        if_pos hs.1, hKernelPos j (t - s) (sub_pos.mpr hs.2)]
    · by_cases hsneg : s < 0
      · rw [hQext j s, if_neg (not_le_of_gt hsneg),
          zero_smul, Set.indicator_of_notMem hs]
      · have hts : t ≤ s := by
          by_contra hn
          exact hs ⟨le_of_not_gt hsneg, lt_of_not_ge hn⟩
        rw [hKernelZero j (t - s) (sub_nonpos.mpr hts),
          smul_zero, Set.indicator_of_notMem hs]
  calc
    (∫ s : ℝ, qext j s • kernel j (t - s)) =
        ∫ s : ℝ, (Set.Ico (0 : ℝ) t).indicator
          (fun y : ℝ => Q j y • physical j (t - y)) s := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ s : ℝ, Q j s • physical j (t - s)
          ∂((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) t)) := by
            rw [integral_indicator measurableSet_Ico]
    _ = ∫ s in (0 : ℝ)..t, Q j s • physical j (t - s) := by
          rw [intervalIntegral.integral_of_le ht]
          exact congrArg
            (fun ν : Measure ℝ =>
              ∫ s : ℝ, Q j s • physical j (t - s) ∂ν)
            ((volume : Measure ℝ).restrict_congr_set
              (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := t)))

/-- The precise four terms of the paper's equation (A9), without the former
strong derivative, Bochner-integrability, or SR-rate premises. Those are now
proofs from the preceding vector W1,1 certificate, ordinary causal identities,
and the existing integrated physical SR evolution theorem.

The remaining kernel-approximation and causal-value hypotheses are explicitly
visible, so this does not claim unconditional physical applicability. -/
theorem paper_A9_four_terms_from_projected_W11_and_physical_SR
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
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
    {m : ℕ}
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (f : Fin m → Lp ℝ 2 μ)
    (Q : Fin m → ℝ → ℝ)
    (Ap0 pt0 : Lp ℝ 2 μ)
    (hInitial : pt0 = -Ap0 + ∑ j : Fin m, (Q j 0) • f j)
    (L : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hOrbitCompatibility : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        L t (f j) = ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j t))
    (Ap homogeneous forcing : ℝ → Lp ℝ 2 μ)
    (hPositiveDecomposition : ∀ τ : ℝ, 0 < τ →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap τ) =
        homogeneous τ + forcing τ)
    (hHomogeneousRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt homogeneous
        (-(ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
          (L t Ap0))) t)
    -- Physical SR equation in genuine integral (Caratheodory) form.
    (hSRIntegrable : ∀ N : ℕ,
      IntervalIntegrable Rdot volume (0 : ℝ) ((N : ℝ) + 1))
    (hSRIntegrated : ∀ t : ℝ, 0 ≤ t →
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    -- The CAUSAL zero extensions of the bounded well fluxes and the
    -- projected positive-lag Neumann kernel/its derivative.
    (qext : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (hQextDef : ∀ j s, qext j s = if 0 ≤ s then Q j s else 0)
    (hKernelDef : ∀ j lag, 0 < lag →
      kernel j lag = ReservoirSeismicityControl.paperFarLpProjection μ
        {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
    (hRateDef : ∀ j lag, 0 < lag →
      rate j lag = -(ReservoirSeismicityControl.paperFarLpProjection μ
        {x : X | ζ x ≠ 1} hfar (second j lag)))
    (hKernelZero : ∀ j lag, lag ≤ 0 → kernel j lag = 0)
    (hRateZero : ∀ j lag, lag ≤ 0 → rate j lag = 0)
    (kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ)
    (hqext : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    -- External smooth-W11 approximation (standard cited Sobolev calculus).
    (hCompact : ∀ n j, HasCompactSupport (kn n j))
    (hSmooth : ∀ n j, ContDiff ℝ 1 (kn n j))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hQBound : ∀ j s, 0 ≤ s → |Q j s| ≤ M j)
    (errValue errRate : Fin m → ℕ → ℝ)
    (herrValue : ∀ j, Tendsto (errValue j) atTop (𝓝 (0 : ℝ)))
    (herrRate : ∀ j, Tendsto (errRate j) atTop (𝓝 (0 : ℝ)))
    (hIntValue : ∀ j t,
      Integrable (fun s : ℝ => qext j s • kernel j (t - s)) volume)
    (hIntKn : ∀ j n t,
      Integrable (fun s : ℝ => qext j s • kn n j (t - s)) volume)
    (hIntRate : ∀ j t,
      Integrable (fun s : ℝ => qext j s • rate j (t - s)) volume)
    (hIntKnRate : ∀ j n t,
      Integrable (fun s : ℝ => qext j s • deriv (kn n j) (t - s)) volume)
    (hDiffValueInt : ∀ j n t,
      Integrable (fun s : ℝ =>
        ‖kn n j (t - s) - kernel j (t - s)‖) volume)
    (hDiffValueMass : ∀ j n t,
      (∫ s : ℝ, ‖kn n j (t - s) - kernel j (t - s)‖) ≤
        errValue j n)
    (hDiffRateInt : ∀ j n t,
      Integrable (fun s : ℝ =>
        ‖deriv (kn n j) (t - s) - rate j (t - s)‖) volume)
    (hDiffRateMass : ∀ j n t,
      (∫ s : ℝ, ‖deriv (kn n j) (t - s) - rate j (t - s)‖) ≤
        errRate j n)
    -- These are value identities, supplied by the earlier physical DG and
    -- causal-support proofs. Neither assumes a derivative of forcing.
    -- This is the actual physical DG/causal *value* identity,
    -- not the derivative of the forcing or the conclusion of (A9).
    (hForcingCausal : ∀ t : ℝ, 0 < t →
      forcing t = ∑ j : Fin m,
        ∫ s in (0 : ℝ)..t, (Q j s) •
          (ReservoirSeismicityControl.paperFarLpProjection μ
            {x : X | ζ x ≠ 1} hfar
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit j (t - s)))))
    : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, Ap τ⟫_ℝ)
        (⟪paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t -
           cutoff (paperSRDiffusionWeightRate μ region hregion Kγ Rdot
             gamma10 R0star t), Ap t⟫_ℝ +
         ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
           gamma10 R0star cutoff t, L t pt0⟫_ℝ -
         ∑ j : Fin m,
           paperSRFarSmoothKernel μ region hregion Kγ R
             gamma10 R0star cutoff V E hsep orbit t j t * Q j 0 +
         ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
           ReservoirSeismicityControl.paperFarWeakNeumannKernelRate
             (paperSRFarDiffusionWeight μ region hregion Kγ R
               gamma10 R0star cutoff) second t j (t - s) * Q j s) t := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
  let fullConv : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s : ℝ, qext j s • kernel j (t - s)
  let fullRate : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)
  let physicalRate : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s in (0 : ℝ)..t, Q j s • (-(P (second j (t - s))))
  have hQextBound : ∀ j s, |qext j s| ≤ M j := by
    intro j s
    rw [hQextDef j s]
    by_cases hs : 0 ≤ s
    · simpa only [if_pos hs] using hQBound j s hs
    · simpa only [if_neg hs, abs_zero] using hM j
  have hRateIntegrand : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        (fun s : ℝ => qext j s • rate j (t - s)) =ᵐ[
          (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)]
        (fun s : ℝ => (Q j s) • (-(P (second j (t - s))))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht j
    have hne : ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
        s ≠ t :=
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)).ae_ne t
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc, hne]
      with s hs hsne
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hst : s < t := by
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · exact hlt
      · exact (hsne heq).elim
    have hlag : 0 < t - s := sub_pos.mpr hst
    change qext j s • rate j (t - s) =
      Q j s • (-(P (second j (t - s))))
    rw [hQextDef j s, if_pos hs0, hRateDef j (t - s) hlag]
  have hForcingValue : ∀ t : ℝ, 0 < t →
      forcing t = ∑ j : Fin m,
        ∫ s : ℝ, qext j s • kernel j (t - s) := by
    intro t ht
    rw [hForcingCausal t ht]
    exact (paper_A9_vector_full_line_equals_physical_causal
      μ Q qext kernel
      (fun j lag => P
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
      hQextDef hKernelDef hKernelZero t ht.le).symm
  have hRateCausal : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      (∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)) =
      (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
        (Q j s) • (-(P (second j (t - s))))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    exact paper_A9_vector_full_line_equals_physical_causal
      μ Q qext rate (fun j lag => -(P (second j lag)))
      hQextDef hRateDef hRateZero t ht.le
  have hFullDerivative : ∀ t : ℝ,
      HasDerivAt fullConv (fullRate t) t := by
    intro t
    exact paper_A9_vector_multiwell_rate_from_L1_kernel_approximation
      μ qext kernel rate kn hqext hCompact hSmooth M hM hQextBound
      errValue errRate herrValue herrRate hIntValue hIntKn hIntRate
      hIntKnRate hDiffValueInt hDiffValueMass hDiffRateInt hDiffRateMass t
  have hForcingDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing (physicalRate t) t := by
    exact paper_A9_positive_physical_forcing_rate_from_full_convolution
      μ forcing fullConv fullRate physicalRate hFullDerivative
      hForcingValue hRateCausal
  have hBochner : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
      Integrable (fun s : ℝ => (Q j s) • (-(P (second j (t - s)))))
        (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    filter_upwards [hRateIntegrand] with t ht j
    have hRes : Integrable
        (fun s : ℝ => qext j s • rate j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) := by
      exact (hIntRate j t).mono_measure Measure.restrict_le_self
    exact hRes.congr (ht j)
  have hSRRate := paper_A9_physical_SR_strong_rate_from_integral_evolution
    μ R Rdot hSRIntegrable hSRIntegrated
  exact paper_A9_exact_four_terms_positive_physical_time
    μ region hregion Kγ R Rdot gamma10 R0star cutoff ζ hfar hcutoff
    V E hsep orbit second hOrbit f Q Ap0 pt0 hInitial L
    hOrbitCompatibility Ap homogeneous forcing hPositiveDecomposition
    hHomogeneousRate hForcingDeriv hBochner hSRRate

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_four_terms_from_projected_W11_and_physical_SR
