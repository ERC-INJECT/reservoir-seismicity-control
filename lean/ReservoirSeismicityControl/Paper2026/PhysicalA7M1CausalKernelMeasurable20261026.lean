import ReservoirSeismicityControl.Paper2026.PhysicalA7A3ToActualPropagatorH2_20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalH2HalfDamping
import ReservoirSeismicityControl.PressurePositiveSemigroupTimeIntervalCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# A7 M1: causal H² primitive -> strongly measurable and integrable physical kernel

The crucial NEW assertion is that no time-measurability assumption on the
propagator or product kernel is needed: an integrable Banach-valued coefficient
has a continuous causal time primitive, continuous Sobolev exponential
composition preserves that continuity, and continuous Sobolev multiplication
preserves a.e. strong measurability of the forcing.

The H² exponential operator and H² multiplication are **standard Sobolev
calculus interfaces** and are NOT proved by this module. The primitive is
constructed from the actual time-dependent H² coefficient, not postulated.

This file intentionally does not claim full M1: the time-space Bochner/L²
representative identity still requires the standard pointwise Bochner/Fubini
theorem and the physical factor representatives. No hypothesis asserting H²(Y)
or H²(R) appears here.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

set_option maxHeartbeats 800000

/-- The finite-interval Bochner coefficient primitive has a continuous
    dependence on the lower causal endpoint. This uses mere L¹ time
    regularity, not continuity or differentiability of `a` itself. -/
theorem a7_causal_primitive_continuousOn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (a : ℝ → H) (t : ℝ) (ht : 0 ≤ t)
    (ha : IntervalIntegrable a volume 0 t) :
    ContinuousOn
      (fun v : ℝ => (∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))
      (Set.Icc (0 : ℝ) t) := by
  have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) t := by
    rw [Set.uIcc_of_le ht]
    exact ⟨le_refl _, ht⟩
  have hprim : ContinuousOn
      (fun v : ℝ => ∫ q in (0 : ℝ)..v, a q)
      (Set.Icc (0 : ℝ) t) := by
    simpa only [Set.uIcc_of_le ht] using
      (intervalIntegral.continuousOn_primitive_interval' ha hzero)
  exact continuousOn_const.sub hprim

/-- The actual exponential of a time-integrated H² coefficient is a
    strongly measurable time path on the physical causal window.

    `expH` is the independent, continuous Sobolev-composition operator.
    It is not an assumed measurable propagator and not an assumed
    regularity conclusion for Y. -/
theorem a7_physical_propagator_time_measurable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (a : ℝ → H) (expH : H → H) (hExp : Continuous expH)
    (t : ℝ) (ht : 0 ≤ t)
    (ha : IntervalIntegrable a volume 0 t) :
    AEStronglyMeasurable
      (fun v : ℝ => expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q)))
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  have hcont : ContinuousOn
      (fun v : ℝ => expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q)))
      (Set.Icc (0 : ℝ) t) := by
    exact hExp.continuousOn.comp
      (a7_causal_primitive_continuousOn a t ht ha)
      (by intro v hv; exact Set.mem_univ _)
  apply hcont.aestronglyMeasurable_of_subset_isCompact
    isCompact_Icc measurableSet_Ioc
  intro v hv
  exact ⟨le_of_lt hv.1, hv.2⟩

/-- The entire physical causal kernel is strongly measurable and Bochner
    integrable, with a UNIFORM norm envelope independent of the final time.

    The hypotheses are the actual coefficient path `a`, the actual forcing
    `b`, the continuous general Sobolev maps `expH` and `prod`, and the
    *already established* quadratic decay and coefficient bounds.
    There is no separate `hKernelMeas` or `hInt` premise.

    In the physical application H = `A7PhysicalH2 U`; `expH` and `prod`
    are the bounded-Lipschitz H² nonlinear calculus maps. The uniform
    envelope below reuses the already passing half-damping theorem.
-/
theorem a7_physical_kernel_measurable_integrable_of_coefficient
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (a b : ℝ → H) (expH : H → H) (prod : H → H → H)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : H × H => prod z.1 z.2))
    (t m Cprod MB E0 E1 E2 : ℝ)
    (ht : 0 ≤ t) (hm : 0 < m)
    (hCprod : 0 ≤ Cprod) (hMB : 0 ≤ MB)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (ha : IntervalIntegrable a volume 0 t)
    (hbMeas : AEStronglyMeasurable b
      (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hbBound : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖b v‖ ≤ MB)
    (hProdBound : ∀ y z, ‖prod y z‖ ≤ Cprod * ‖y‖ * ‖z‖)
    (hDecay : ∀ v, 0 < v → v ≤ t →
      ‖expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))‖ ≤
        (E0 + E1 * (t-v) + E2 * (t-v)^2) *
          Real.exp (-(m*(t-v)))) :
    let K : ℝ → H := fun v =>
      prod (expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))) (b v)
    AEStronglyMeasurable K
      (volume.restrict (Set.Ioc (0 : ℝ) t)) ∧
    (∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖K v‖ ≤ Cprod * MB *
        (E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2)) ∧
    Integrable K (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  dsimp only
  let E : ℝ → H := fun v =>
    expH ((∫ q in (0 : ℝ)..t, a q) -
      (∫ q in (0 : ℝ)..v, a q))
  let K : ℝ → H := fun v => prod (E v) (b v)
  let F : ℝ := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hEmeas : AEStronglyMeasurable E
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    a7_physical_propagator_time_measurable a expH hExp t ht ha
  have hKmeas : AEStronglyMeasurable K
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    hProdCont.comp_aestronglyMeasurable (hEmeas.prodMk hbMeas)
  have hKbound : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖K v‖ ≤ Cprod * MB * F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hbBound]
      with v hv hb
    have hlag : 0 ≤ t-v := sub_nonneg.mpr hv.2
    have he := hDecay v hv.1 hv.2
    have henv := ReservoirSeismicityControl.sr_signed_half_damping_quadratic_envelope
      m (t-v) E0 E1 E2 hm hlag hE0 hE1 hE2
    have hEbd : ‖E v‖ ≤ F := by
      exact he.trans (by simpa only [F] using henv)
    calc
      ‖K v‖ ≤ Cprod * ‖E v‖ * ‖b v‖ := hProdBound _ _
      _ ≤ Cprod * ‖E v‖ * MB :=
        mul_le_mul_of_nonneg_left hb
          (mul_nonneg hCprod (norm_nonneg _))
      _ ≤ Cprod * F * MB := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEbd hCprod) hMB
      _ = Cprod * MB * F := by ring
  haveI : IsFiniteMeasure
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    rw [((volume : Measure ℝ).restrict_congr_set
      (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := t))).symm]
    exact ReservoirSeismicityControl.pressure_time_Ico_finite 0 t
  have hKint : Integrable K
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    Integrable.of_bound hKmeas (Cprod * MB * F) hKbound
  exact ⟨hKmeas, hKbound, hKint⟩

/-- Physical application of the preceding theorem to the *actual normalized
    exponentially weighted causal measure* used in the passing signed H²
    Bochner lifting theorem. No independent measurability or integrability
    hypothesis is made for this weighted kernel.

    The density is the already established positive pressure kernel. By
    absolute continuity, all the measure-zero exceptions from the physical
    Lebesgue interval remain negligible for the normalized convolution. -/
theorem a7_physical_normalized_kernel_integrable_from_coefficient
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (a b : ℝ → H) (expH : H → H) (prod : H → H → H)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : H × H => prod z.1 z.2))
    (t m Cprod MB E0 E1 E2 : ℝ)
    (ht : 0 ≤ t) (hm : 0 < m)
    (hCprod : 0 ≤ Cprod) (hMB : 0 ≤ MB)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (ha : IntervalIntegrable a volume 0 t)
    (hbMeas : AEStronglyMeasurable b
      (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hbBound : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖b v‖ ≤ MB)
    (hProdBound : ∀ y z, ‖prod y z‖ ≤ Cprod * ‖y‖ * ‖z‖)
    (hDecay : ∀ v, 0 < v → v ≤ t →
      ‖expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))‖ ≤
        (E0 + E1 * (t-v) + E2 * (t-v)^2) *
          Real.exp (-(m*(t-v)))) :
    let K : ℝ → H := fun v =>
      prod (expH ((∫ q in (0 : ℝ)..t, a q) -
        (∫ q in (0 : ℝ)..v, a q))) (b v)
    AEStronglyMeasurable K
      (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t) ∧
    (∀ᵐ v ∂(ReservoirSeismicityControl.pressureExponentialKernelMeasure m t),
      ‖K v‖ ≤ Cprod * MB *
        (E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2)) ∧
    Integrable K
      (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t) := by
  dsimp only
  have hLeb := a7_physical_kernel_measurable_integrable_of_coefficient
    a b expH prod hExp hProdCont t m Cprod MB E0 E1 E2
    ht hm hCprod hMB hE0 hE1 hE2 ha hbMeas hbBound
    hProdBound hDecay
  dsimp only at hLeb
  rcases hLeb with ⟨hMeas, hBound, _⟩
  have hAC :
      (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t).AbsolutelyContinuous
        (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    exact withDensity_absolutelyContinuous _ _
  have hWeightedMeas := hMeas.mono_ac hAC
  have hWeightedBound := hAC.ae_le hBound
  haveI : IsFiniteMeasure
      (ReservoirSeismicityControl.pressureExponentialKernelMeasure m t) :=
    ReservoirSeismicityControl.pressure_exponential_kernel_measure_finite m t hm.le ht
  exact ⟨hWeightedMeas, hWeightedBound,
    Integrable.of_bound hWeightedMeas _ hWeightedBound⟩

#print axioms a7_causal_primitive_continuousOn
#print axioms a7_physical_propagator_time_measurable
#print axioms a7_physical_kernel_measurable_integrable_of_coefficient
#print axioms a7_physical_normalized_kernel_integrable_from_coefficient

end ReservoirSeismicityControl.Paper2026
