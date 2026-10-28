import ReservoirSeismicityControl.Paper2026.PhysicalA9ExactManuscriptFormula
import ReservoirSeismicityControl.SeismicityPhysicalIntegratedAEEvolution
import Mathlib.Tactic

/-!
# A9 physical-time applicability: no negative-time PDE premise, strong SR rate from integral evolution

This file only reuses already proved physical A9 algebra and the already
proved Banach-valued fundamental theorem of calculus for the SR integral ODE.
It does NOT rebuild any heat kernel or diffusion estimate.

The first theorem proves the strong L2 time derivative of the physical SR on
(0,infinity) from its Caratheodory integral equation on each finite horizon.
The second theorem removes the artificial requirement that the physical mild
pressure-generator identity hold at *negative time*; only the physical half-line
is needed. Neither theorem assumes a derivative of the well flux.

The physical forcing's vector W1,1 derivative is STILL a separate standard
semigroup-convolution applicability obligation; this file does not disguise
that input as a proved fact. See the accompanying applicability note.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- The already proved finite-horizon Bochner FTC for the SR evolution yields
one a.e. strong L2 derivative on the entire physical positive-time half-line.
The signed physical ODE enters through `Rdot` and its integral evolution;
there is NO assumption of a pointwise SR derivative. -/
theorem paper_A9_physical_SR_strong_rate_from_integral_evolution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (hIntegrable : ∀ N : ℕ,
      IntervalIntegrable Rdot volume (0 : ℝ) ((N : ℝ) + 1))
    (hIntegrated : ∀ t : ℝ, 0 ≤ t →
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t := by
  have hEach (N : ℕ) :
      ∀ᵐ t : ℝ ∂volume,
        t ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) →
          HasDerivAt R (Rdot t) t := by
    let T : NNReal := ⟨(N : ℝ) + 1, by positivity⟩
    have hI : IntervalIntegrable Rdot volume (0 : ℝ) (T : ℝ) := by
      exact hIntegrable N
    have hD : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
        R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s := by
      intro t ht
      exact hIntegrated t ht.1
    exact ReservoirSeismicityControl.sr_integrated_L2_evolution_hasDerivAt_ae
      μ T R Rdot hI hD
  have hAll : ∀ᵐ t : ℝ ∂volume,
      ∀ N : ℕ, t ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) →
        HasDerivAt R (Rdot t) t := by
    exact eventually_countable_forall.mpr hEach
  have hReal : ∀ᵐ t : ℝ ∂volume,
      0 < t → HasDerivAt R (Rdot t) t := by
    filter_upwards [hAll] with t hNt ht
    obtain ⟨N, hN⟩ := exists_nat_gt t
    apply hNt N
    exact ⟨ht, by linarith⟩
  change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
    HasDerivAt R (Rdot t) t
  exact (ae_restrict_iff' measurableSet_Ioi).2 hReal

/-- The literal four-term A9 derivative is an assertion on positive physical
  time. The generator's causal decomposition is therefore required only for
  t > 0; an arbitrary negative-time PDE evolution is not introduced.

  This theorem uses the PASSED exact-four-terms theorem unchanged. Truncating
  the three L2 paths to zero at nonpositive times gives global equality, and
  locality of `HasDerivAt` transfers its conclusion back to the actual paths.

  The remaining strong forcing derivative remains visible and must be
  discharged by the cited separated vector-kernel W1,1 convolution theorem,
  not by assuming the desired scalar A9 conclusion. -/
theorem paper_A9_exact_four_terms_positive_physical_time
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
    (hForcingRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing
        (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          (Q j s) • (-(ReservoirSeismicityControl.paperFarLpProjection μ
            {x : X | ζ x ≠ 1} hfar (second j (t - s))))) t)
    (hBochner : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        Integrable (fun s : ℝ => (Q j s) • (-(ReservoirSeismicityControl.paperFarLpProjection μ
          {x : X | ζ x ≠ 1} hfar (second j (t - s)))))
          (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hR : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
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
  let positiveCut (g : ℝ → Lp ℝ 2 μ) : ℝ → Lp ℝ 2 μ :=
    fun τ => if 0 < τ then g τ else 0
  have hGlobal : ∀ τ : ℝ,
      P (positiveCut Ap τ) =
        positiveCut homogeneous τ + positiveCut forcing τ := by
    intro τ
    by_cases ht : 0 < τ
    · simp only [positiveCut, if_pos ht]
      exact hPositiveDecomposition τ ht
    · simp only [positiveCut, if_neg ht, map_zero, add_zero]
  have hCutRate (g gdot : ℝ → Lp ℝ 2 μ)
      (hg : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        HasDerivAt g (gdot t) t) :
      ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        HasDerivAt (positiveCut g) (gdot t) t := by
    filter_upwards [hg, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht htpos
    have hLocal : positiveCut g =ᶠ[𝓝 t] g := by
      filter_upwards [isOpen_Ioi.mem_nhds htpos] with τ hτ
      change (if 0 < τ then g τ else 0) = g τ
      exact if_pos (show 0 < τ from hτ)
    exact ht.congr_of_eventuallyEq hLocal
  have hHCut := hCutRate homogeneous
    (fun t => -(P (L t Ap0))) hHomogeneousRate
  have hFCut := hCutRate forcing
    (fun t => ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
      (Q j s) • (-(P (second j (t - s))))) hForcingRate
  have hMain := (paper_A9_exact_physical_four_terms_from_existing_assembly
    μ region hregion Kγ R Rdot gamma10 R0star cutoff ζ hfar hcutoff
    V E hsep orbit second hOrbit f Q Ap0 pt0 hInitial L
    hOrbitCompatibility (positiveCut Ap) (positiveCut homogeneous)
    (positiveCut forcing) hGlobal hHCut hFCut hBochner hR).2
  filter_upwards [hMain, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with t hd ht
  have hAp : positiveCut Ap t = Ap t := by
    change (if 0 < t then Ap t else 0) = Ap t
    exact if_pos (show 0 < t from ht)
  have hLocal :
      (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, Ap τ⟫_ℝ) =ᶠ[𝓝 t]
      (fun τ => ⟪paperSRFarDiffusionWeight μ region hregion Kγ R
          gamma10 R0star cutoff τ, positiveCut Ap τ⟫_ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
    have hAtτ : positiveCut Ap τ = Ap τ := by
      change (if 0 < τ then Ap τ else 0) = Ap τ
      exact if_pos (show 0 < τ from hτ)
    rw [hAtτ]
  rw [hAp] at hd
  exact hd.congr_of_eventuallyEq hLocal

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_SR_strong_rate_from_integral_evolution
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_exact_four_terms_positive_physical_time
