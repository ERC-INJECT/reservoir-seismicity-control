import ReservoirSeismicityControl.Paper2026.PhysicalA7M1CausalKernelMeasurable20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7NormalizedDuhamel
import ReservoirSeismicityControl.SeismicitySignedH2BochnerLift
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# M1, consolidated: physical causal H² construction and exact normalization

This imports the PASSING time-measurable kernel module and proves two
substantive new statements:

* The exponentially weighted normalized Bochner integral is EXACTLY the
  original Lebesgue-time Bochner integral for arbitrary Banach-valued paths.
  This rules out a second, accidental damping factor.
* A time-integrable H² coefficient, a strongly measurable uniformly bounded
  H² forcing and the already verified physical 2m damping estimate construct
  one Bochner candidate at EVERY t ≥ 0 with a COMMON uniform H² bound,
  eliminating assumed homogeneous bounds, normalized-kernel measurability,
  normalized-kernel integrability and the final candidate norm estimate.

No hypothesis asserting H² regularity of the actual scalar Y or R is used.
The remaining physical step is the standard L² representative/Fubini
identification, which must NOT be treated as proved by this construction.
The standard continuous Sobolev exponential/product operators and their
physical factor representatives are still explicit analysis inputs.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

set_option maxHeartbeats 1500000

/-- EXACT Banach-valued normalization. This is not a mere scalar identity:
    it applies directly to the actual H² Bochner kernel. In particular,
    normalized integration adds NO extra exponential damping. -/
theorem a7_bochner_normalized_eq_causal
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (K : ℝ → H) (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) :
    m⁻¹ • (∫ v, Real.exp (m * (t-v)) • K v
      ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
        ∫ v in (0 : ℝ)..t, K v := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc 0 t)
  let k : ℝ → ℝ := fun v => m * Real.exp (-(m * (t-v)))
  let F : ℝ → H := fun v => Real.exp (m * (t-v)) • K v
  have hν : ReservoirSeismicityControl.pressureExponentialKernelMeasure m t =
      μ.withDensity (fun v => ENNReal.ofReal (k v)) := rfl
  have hkpos (v : ℝ) : 0 ≤ k v :=
    mul_nonneg hm.le (Real.exp_pos _).le
  have hkmeas : AEMeasurable (fun v => ENNReal.ofReal (k v)) μ := by
    have h : Measurable (fun v : ℝ => ENNReal.ofReal (k v)) := by
      dsimp [k]
      fun_prop
    exact h.aemeasurable
  have hkfinite : ∀ᵐ v ∂μ, ENNReal.ofReal (k v) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hchange :
      (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
        ∫ v, k v • F v ∂μ := by
    rw [hν]
    calc
      (∫ v, F v ∂μ.withDensity (fun v => ENNReal.ofReal (k v))) =
          ∫ v, (ENNReal.ofReal (k v)).toReal • F v ∂μ := by
            exact integral_withDensity_eq_integral_toReal_smul₀
              hkmeas hkfinite F
      _ = ∫ v, k v • F v ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with v
        rw [ENNReal.toReal_ofReal (hkpos v)]
  have hpoint (v : ℝ) : k v • F v = m • K v := by
    dsimp [k, F]
    rw [smul_smul]
    have he : Real.exp (-(m*(t-v))) * Real.exp (m*(t-v)) = 1 := by
      rw [← Real.exp_add]
      simp
    congr 1
    calc
      (m * Real.exp (-(m*(t-v)))) * Real.exp (m*(t-v)) =
          m * (Real.exp (-(m*(t-v))) * Real.exp (m*(t-v))) := by ring
      _ = m := by rw [he]; ring
  have heq : (fun v : ℝ => k v • F v) = (fun v => m • K v) := by
    funext v
    exact hpoint v
  have hmeasure :
      (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) =
        m • ∫ v, K v ∂μ := by
    rw [hchange, heq, integral_smul]
  have hmne : m ≠ 0 := ne_of_gt hm
  change m⁻¹ • (∫ v, F v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) = _
  rw [hmeasure, smul_smul, inv_mul_cancel₀ hmne, one_smul]
  rw [intervalIntegral.integral_of_le ht]

/-- The same concrete H² candidate written with the physical Lebesgue
    kernel or the analytically convenient normalized probability kernel. -/
theorem a7_normalized_H2_candidate_is_direct_duhamel
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (hom : ℝ → H) (K : ℝ → ℝ → H)
    (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) :
    ReservoirSeismicityControl.srSignedH2BochnerCandidate m hom
       (fun q v => Real.exp (m * (q-v)) • K q v) t =
        hom t + ∫ v in (0 : ℝ)..t, K t v := by
  dsimp [ReservoirSeismicityControl.srSignedH2BochnerCandidate]
  rw [a7_bochner_normalized_eq_causal (K t) m t hm ht]

/-- From a twice-damped physical H² propagator and its measurable forcing,
    construct the actual causal H² Bochner CANDIDATE with a uniform bound.
    The normalization identity is part of the conclusion.

    In physical application, `H = A7PhysicalH2 U`, `a=gamma2 Rstar`,
    `b=gamma2 exp(s gamma1 u)`, `expH` is the *negative exponential*
    Sobolev map, and `prod` is the H² multiplication map.

    This theorem removes the previously separate hypotheses on the
    homogenous norm, kernel measurability and integrability, and the
    constructed Y's uniform norm. It does not postulate H² of Y.
-/
theorem a7_M1_causal_H2_candidate_uniform_from_coefficients
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (a b : ℝ → H) (Y0 : H)
    (expH : H → H) (prod : H → H → H)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : H × H => prod z.1 z.2))
    (m Cprod MB MY0 E0 E1 E2 : ℝ)
    (hm : 0 < m) (hCprod : 0 ≤ Cprod)
    (hMB : 0 ≤ MB) (hMY0 : 0 ≤ MY0)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hY0 : ‖Y0‖ ≤ MY0)
    (ha : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable a volume 0 t)
    (hbMeas : ∀ t : ℝ, 0 ≤ t →
       AEStronglyMeasurable b
         (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hbBound : ∀ t : ℝ, 0 ≤ t →
       ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖b v‖ ≤ MB)
    (hProdBound : ∀ y z, ‖prod y z‖ ≤ Cprod * ‖y‖ * ‖z‖)
    (hDecay : ∀ t v, 0 ≤ v → v ≤ t →
      ‖expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))‖ ≤
          (E0 + E1 * (t-v) + E2 * (t-v)^2) *
            Real.exp (-((2*m)*(t-v)))) :
    let F := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
    let Fhom := E0 + E1 * (2*m)⁻¹ + E2 * (((2*m)/2)⁻¹)^2
    let Ybound := Cprod * MY0 * Fhom + Cprod * MB * F / m
    ∀ t : ℝ, 0 ≤ t →
      ∃ Yh : H,
        Yh = prod (expH (∫ q in (0 : ℝ)..t, a q)) Y0 +
          (∫ v in (0 : ℝ)..t,
             prod (expH ((∫ q in (0 : ℝ)..t, a q) -
               (∫ q in (0 : ℝ)..v, a q))) (b v)) ∧
        ‖Yh‖ ≤ Ybound := by
  dsimp only
  intro t ht
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc 0 t)
  let ν : Measure ℝ := ReservoirSeismicityControl.pressureExponentialKernelMeasure m t
  let E : ℝ → H := fun v =>
    expH ((∫ q in (0 : ℝ)..t, a q) -
       (∫ q in (0 : ℝ)..v, a q))
  let K : ℝ → H := fun v => prod (E v) (b v)
  let KN : ℝ → H := fun v => Real.exp (m * (t-v)) • K v
  let F : ℝ := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
  let Fhom : ℝ := E0 + E1 * (2*m)⁻¹ + E2 * (((2*m)/2)⁻¹)^2
  let Hmax : ℝ := Cprod * MY0 * Fhom
  let Kmax : ℝ := Cprod * MB * F
  have hm2 : 0 < 2 * m := by positivity
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hFhomnonneg : 0 ≤ Fhom := by dsimp [Fhom]; positivity
  have hKmaxnonneg : 0 ≤ Kmax := by dsimp [Kmax]; positivity
  have hHom : ‖prod (E 0) Y0‖ ≤ Hmax := by
    have hEzero : ‖E 0‖ ≤ Fhom := by
      have hE0bound := hDecay t 0 (le_refl _) ht
      have hEnv := ReservoirSeismicityControl.sr_signed_half_damping_quadratic_envelope
        (2*m) t E0 E1 E2 hm2 ht hE0 hE1 hE2
      have hZeroInt : (∫ q in (0 : ℝ)..(0 : ℝ), a q) = 0 := by simp
      have hb : ‖E 0‖ ≤ (E0 + E1*t + E2*t^2) *
            Real.exp (-((2*m)*t)) := by
        simpa only [E, hZeroInt, sub_zero] using hE0bound
      exact hb.trans (by simpa only [Fhom] using hEnv)
    calc
      ‖prod (E 0) Y0‖ ≤ Cprod * ‖E 0‖ * ‖Y0‖ := hProdBound _ _
      _ ≤ Cprod * ‖E 0‖ * MY0 :=
        mul_le_mul_of_nonneg_left hY0
          (mul_nonneg hCprod (norm_nonneg _))
      _ ≤ Cprod * Fhom * MY0 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEzero hCprod) hMY0
      _ = Hmax := by dsimp [Hmax]; ring
  have hLebMeas : AEStronglyMeasurable K μ := by
    have hEmeas := a7_physical_propagator_time_measurable
      a expH hExp t ht (ha t ht)
    exact hProdCont.comp_aestronglyMeasurable
      (hEmeas.prodMk (hbMeas t ht))
  have hKNLebMeas : AEStronglyMeasurable KN μ := by
    have hex : AEStronglyMeasurable
        (fun v : ℝ => Real.exp (m*(t-v))) μ :=
      (by fun_prop : Measurable (fun v : ℝ => Real.exp (m*(t-v)))).aestronglyMeasurable
    exact hex.smul hLebMeas
  have hAC : ν.AbsolutelyContinuous μ := by
    exact withDensity_absolutelyContinuous _ _
  have hKNmeas : AEStronglyMeasurable KN ν :=
    hKNLebMeas.mono_ac hAC
  have hwindow : ∀ᵐ v ∂ν, 0 < v ∧ v ≤ t :=
    hAC.ae_le (ae_restrict_mem measurableSet_Ioc)
  have hKNbound : ∀ᵐ v ∂ν, ‖KN v‖ ≤ Kmax := by
    filter_upwards [hwindow, hAC.ae_le (hbBound t ht)] with v hv hb
    have hlag : 0 ≤ t - v := sub_nonneg.mpr hv.2
    have htwo :
       ‖E v‖ ≤ (E0 + E1*(t-v) + E2*(t-v)^2) *
         Real.exp (-((2*m)*(t-v))) := hDecay t v hv.1.le hv.2
    have hNormKN : ‖KN v‖ = Real.exp (m*(t-v)) * ‖K v‖ := by
      dsimp [KN]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hExpShift :
       Real.exp (m*(t-v)) * Real.exp (-((2*m)*(t-v))) =
         Real.exp (-(m*(t-v))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hNormE : Real.exp (m*(t-v)) * ‖E v‖ ≤
        (E0 + E1*(t-v) + E2*(t-v)^2) * Real.exp (-(m*(t-v))) := by
      calc
        _ ≤ Real.exp (m*(t-v)) *
          ((E0 + E1*(t-v) + E2*(t-v)^2) *
            Real.exp (-((2*m)*(t-v)))) :=
          mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
        _ = _ := by
          calc
            Real.exp (m*(t-v)) *
                ((E0 + E1*(t-v) + E2*(t-v)^2) *
                  Real.exp (-((2*m)*(t-v)))) =
              (E0 + E1*(t-v) + E2*(t-v)^2) *
                (Real.exp (m*(t-v)) * Real.exp (-((2*m)*(t-v)))) := by ring
            _ = _ := by rw [hExpShift]
    have hEnv := ReservoirSeismicityControl.sr_signed_half_damping_quadratic_envelope
       m (t-v) E0 E1 E2 hm hlag hE0 hE1 hE2
    have hEscaled : Real.exp (m*(t-v)) * ‖E v‖ ≤ F :=
      hNormE.trans (by simpa only [F] using hEnv)
    calc
      ‖KN v‖ = Real.exp (m*(t-v)) * ‖K v‖ := hNormKN
      _ ≤ Real.exp (m*(t-v)) * (Cprod * ‖E v‖ * ‖b v‖) :=
        mul_le_mul_of_nonneg_left (hProdBound (E v) (b v))
          (Real.exp_pos _).le
      _ ≤ Real.exp (m*(t-v)) * (Cprod * ‖E v‖ * MB) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb
            (mul_nonneg hCprod (norm_nonneg _)))
          (Real.exp_pos _).le
      _ = Cprod * (Real.exp (m*(t-v)) * ‖E v‖) * MB := by ring
      _ ≤ Cprod * F * MB := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEscaled hCprod) hMB
      _ = Kmax := by dsimp [Kmax]; ring
  haveI : IsFiniteMeasure ν :=
    ReservoirSeismicityControl.pressure_exponential_kernel_measure_finite m t hm.le ht
  have hKNintegrable : Integrable KN ν :=
    Integrable.of_bound hKNmeas Kmax hKNbound
  have hKernelIntegral :
      ‖m⁻¹ • (∫ v, KN v ∂ν)‖ ≤ Kmax / m := by
    exact ReservoirSeismicityControl.sr_damped_bochner_convolution_norm_le
      m t Kmax hm ht hKmaxnonneg KN hKNbound
  have hUbound :
      ‖prod (E 0) Y0 + m⁻¹ • (∫ v, KN v ∂ν)‖ ≤
        Hmax + Kmax/m := by
    calc
      _ ≤ ‖prod (E 0) Y0‖ + ‖m⁻¹ • (∫ v, KN v ∂ν)‖ :=
        norm_add_le _ _
      _ ≤ Hmax + Kmax/m := add_le_add hHom hKernelIntegral
  -- Since the normalized measure is finite, the candidate is equal to the
  -- original physical Lebesgue-time Duhamel integral, with no double damping.
  let Yh : H := prod (E 0) Y0 + m⁻¹ • (∫ v, KN v ∂ν)
  have hDirect : Yh = prod (E 0) Y0 +
      ∫ v in (0 : ℝ)..t, K v := by
    change prod (E 0) Y0 +
      m⁻¹ • (∫ v, Real.exp (m*(t-v)) • K v
        ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t)) = _
    rw [a7_bochner_normalized_eq_causal K m t hm ht]
  refine ⟨Yh, ?_, ?_⟩
  · simpa only [E, K, intervalIntegral.integral_same, sub_zero] using hDirect
  · simpa only [Yh, Hmax, Kmax] using hUbound

#print axioms a7_bochner_normalized_eq_causal
#print axioms a7_normalized_H2_candidate_is_direct_duhamel
#print axioms a7_M1_causal_H2_candidate_uniform_from_coefficients

end ReservoirSeismicityControl.Paper2026
