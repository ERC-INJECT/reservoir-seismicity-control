import ReservoirSeismicityControl.Paper2026.PhysicalA9W11DensityFromFTC20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9W11ManuscriptApplicability20261025
import Mathlib.Tactic

/-!
# Appendix A.3: actual projected physical forcing and four-term rate

The physical far forcing is *defined* as a causal full-line convolution of the
projected positive-lag Neumann operator. Its derivative follows from the
previously VERIFIED physical W1,1 density/FTC theorem, not an A9 derivative
hypothesis or a bound on time derivatives of well fluxes.

The remaining PDE-specific inputs are the physical projected mild VALUE
identity and analytic homogeneous semigroup-orbit derivative. Those are
applications of the existing Neumann/Duhamel and semigroup results, not
assumptions of the final moving SR far derivative. This theorem does not
pretend to discharge their concrete-domain applicability.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology

set_option maxHeartbeats 2000000

/-- The literal A9 four-term SR far derivative with the actual physical
    projected forcing derivative and its Bochner integrability proved from
    the vector W11 density theorem. The pressure-generator mild *value*
    identity and analytic semigroup orbit rate remain transparent inputs;
    they do not assert a derivative of the forcing or of the observation. -/
theorem paper_A9_four_terms_from_physical_causal_density_and_mild_value
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
    (B₀ B₁ : Fin m → ℝ → ℝ)
    (hB₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₀ j lag)
    (hB₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₁ j lag)
    (hDG₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))‖
        ≤ B₀ j lag)
    (hDG₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
        (second j lag)‖ ≤ B₁ j lag)
    (hB₀Int : ∀ j : Fin m,
      Integrable (B₀ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₁Int : ∀ j : Fin m,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₀Zero : ∀ j : Fin m,
      Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hOrbitMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ
          {x : X | ζ x ≠ 1} hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSecondMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ
          {x : X | ζ x ≠ 1} hfar (second j lag))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (Q qext : Fin m → ℝ → ℝ)
    (hQext : ∀ j s, qext j s = if 0 ≤ s then Q j s else 0)
    (hqLoc : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (qext j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |qext j s| ≤ M j)
    (f : Fin m → Lp ℝ 2 μ)
    (Ap0 pt0 : Lp ℝ 2 μ)
    (hInitial : pt0 = -Ap0 + ∑ j : Fin m, (Q j 0) • f j)
    (L : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (hOrbitCompatibility : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        L t (f j) = ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j t))
    (Ap homOrbit : ℝ → Lp ℝ 2 μ)
    -- PDE mild VALUE: follows from A5 physical generator/Duhamel theorem.
    (hMildValue : ∀ t : ℝ, 0 < t →
      ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (Ap t) =
        ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar (homOrbit t) +
        ∑ j : Fin m, ∫ s in (0 : ℝ)..t, Q j s •
          (ReservoirSeismicityControl.paperFarLpProjection μ {x : X | ζ x ≠ 1} hfar
            (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit j (t - s)))))
    -- Standard analytic semigroup ORBIT derivative (not the A9 observation).
    (hHomOrbitRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt homOrbit (-(L t Ap0)) t)
    (hSRIntegrable : ∀ N : ℕ,
      IntervalIntegrable Rdot volume (0 : ℝ) ((N : ℝ) + 1))
    (hSRIntegrated : ∀ t : ℝ, 0 ≤ t →
      R t = R 0 + ∫ s in (0 : ℝ)..t, Rdot s)
    -- Only the standard universal Bochner-Sobolev density theorem is external.
    (hDensity : PaperA9BanachW11Density μ) :
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
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  let homogeneous : ℝ → Lp ℝ 2 μ := fun t => P (homOrbit t)
  let forcing : ℝ → Lp ℝ 2 μ := fun t =>
    ∑ j : Fin m, ∫ s : ℝ, qext j s • kernel j (t - s)
  have hKernelPos (j : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      kernel j lag = P
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)) := by
    dsimp [kernel]
    rw [if_pos hlag]
  have hRatePos (j : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      rate j lag = -(P (second j lag)) := by
    dsimp [rate]
    rw [if_pos hlag]
  have hKernelZero (j : Fin m) (lag : ℝ) (hlag : lag ≤ 0) :
      kernel j lag = 0 := by
    dsimp [kernel]
    rw [if_neg (not_lt.mpr hlag)]
  have hRateZero (j : Fin m) (lag : ℝ) (hlag : lag ≤ 0) :
      rate j lag = 0 := by
    dsimp [rate]
    rw [if_neg (not_lt.mpr hlag)]
  have hCausalValue (t : ℝ) (ht : 0 ≤ t) :
      forcing t =
        ∑ j : Fin m, ∫ s in (0 : ℝ)..t, Q j s •
          (P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
            (orbit j (t - s)))) := by
    exact paper_A9_vector_full_line_equals_physical_causal μ Q qext kernel
      (fun j lag => P
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
      hQext hKernelPos hKernelZero t ht
  have hPositiveDecomposition (t : ℝ) (ht : 0 < t) :
      P (Ap t) = homogeneous t + forcing t := by
    change P (Ap t) = P (homOrbit t) + forcing t
    rw [hMildValue t ht]
    congr 1
    exact (hCausalValue t ht.le).symm
  have hHomogeneousRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt homogeneous (-(P (L t Ap0))) t := by
    filter_upwards [hHomOrbitRate] with t hd
    have hcomp := P.hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun τ => P (homOrbit τ)) (P (-(L t Ap0))) t at hcomp
    simpa only [homogeneous, map_neg] using hcomp
  have hFullDerivative : ∀ t : ℝ,
      HasDerivAt forcing
        (∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)) t := by
    exact paper_A9_physical_projected_convolution_rate_from_DG_and_density
      μ {x : X | ζ x ≠ 1} hfar V E hsep orbit second hOrbit
      B₀ B₁ hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas qext hqLoc hqMeas M hqBound hDensity
  have hRateCausal : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      (∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)) =
      (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
        Q j s • (-(P (second j (t - s))))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    exact paper_A9_vector_full_line_equals_physical_causal μ Q qext rate
      (fun j lag => -(P (second j lag)))
      hQext hRatePos hRateZero t ht.le
  have hForcingRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt forcing
        (∑ j : Fin m, ∫ s in (0 : ℝ)..t,
          Q j s • (-(P (second j (t - s))))) t := by
    exact paper_A9_positive_physical_forcing_rate_from_full_convolution
      μ forcing forcing
      (fun t => ∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s))
      (fun t => ∑ j : Fin m, ∫ s in (0 : ℝ)..t,
        Q j s • (-(P (second j (t - s)))))
      hFullDerivative (fun _ _ => rfl) hRateCausal
  obtain ⟨_hKInt, _hDkInt, _hKConvInt, hDkConvInt, _, _, _⟩ :=
    paper_A9_physical_projected_vector_full_line_certificate
      μ {x : X | ζ x ≠ 1} hfar V E hsep orbit second hOrbit
      B₀ B₁ hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas qext hqMeas M hqBound
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
    change qext j s • rate j (t - s) = Q j s • (-(P (second j (t - s))))
    rw [hQext j s, if_pos hs0, hRatePos j (t - s) hlag]
  have hBochner : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ∀ j : Fin m,
        Integrable (fun s : ℝ => Q j s • (-(P (second j (t - s)))))
          (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    filter_upwards [hRateIntegrand] with t ht j
    have hRes : Integrable
        (fun s : ℝ => qext j s • rate j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) := by
      exact (hDkConvInt j t).mono_measure Measure.restrict_le_self
    exact hRes.congr (ht j)
  have hSRRate := paper_A9_physical_SR_strong_rate_from_integral_evolution
    μ R Rdot hSRIntegrable hSRIntegrated
  exact paper_A9_exact_four_terms_positive_physical_time
    μ region hregion Kγ R Rdot gamma10 R0star cutoff ζ hfar hcutoff
    V E hsep orbit second hOrbit f Q Ap0 pt0 hInitial L
    hOrbitCompatibility Ap homogeneous forcing hPositiveDecomposition
    hHomogeneousRate hForcingRate hBochner hSRRate

#print axioms paper_A9_four_terms_from_physical_causal_density_and_mild_value

end ReservoirSeismicityControl.Paper2026
