import ReservoirSeismicityControl.Paper2026.PhysicalA7M1NormalizedCandidate20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualSignedField20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ConcreteBanachH2Gate20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalLocalH2
import Mathlib.Tactic

/-!
# A7-M1/M2: Actual signed reciprocal and SR, relative to STANDARD Sobolev--Fubini theorems

This is the intended terminal physical identification. External ANALYSIS results
are recorded as explicit universally formulated interfaces, not new model
postulates and not an assumption that the actual Y or R has H² regularity:

* hPointwiseBochner: standard Bochner/L² Fubini representative theorem for
  every integrable H² path (with a compatible jointly measurable version).
* hExpRep, hProductRep: ordinary H² exponential and product calculus.
* hCausalRep: standard joint representative of those operations for the
  time-dependent *physical coefficients*, checked from A3 representatives.
* hPositiveQuotient: the standard positive Sobolev reciprocal/quotient
  calculus, uniformly for every H² numerator and reciprocal, not for R.

No hypotheses assert the final identification of physical Y, or any H²
regularity of the physical Y or physical R. Scalar Duhamel and the uniform
H² candidate estimate are imported FROM ALREADY PASSING MODULES.

The final theorem is a proof relative to these documented standard inputs.
It must not be advertised as unconditional Lean verification of the external
standard theorems themselves. No new `axiom`, `sorry`, `admit`, or Q-dot.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

set_option maxHeartbeats 1500000

/-- Actual signed reciprocal in the physical L² field is represented by the
uniformly bounded H² Duhamel candidate. There is no a priori H² premise
for `physicalSignedYL2`.

`hPointwiseBochner` is the GENERAL external theorem concerning arbitrary
Bochner-integrable spatial Sobolev paths, not a hypothesis equating Y and
its construction. `hCausalRep` asserts only the *kernel's* joint a.e.
Sobolev representative identity and is to be instantiated using the
standard product/composition calculus applied to physical A3 paths.
-/
theorem a7_M1_actual_signed_Y_uniform_H2_from_standard_results
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) (embed : H →L[ℝ] Lp ℝ 2 μ)
    (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hYLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ)
    (aH bH : ℝ → H) (Y0 : H)
    (expH : H → H) (prod : H → H → H)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : H × H => prod z.1 z.2))
    (m Cprod MB MY0 E0 E1 E2 : ℝ)
    (hm : 0 < m) (hCprod : 0 ≤ Cprod)
    (hMB : 0 ≤ MB) (hMY0 : 0 ≤ MY0)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hY0 : ‖Y0‖ ≤ MY0)
    (ha : ∀ t, 0 ≤ t → IntervalIntegrable aH volume 0 t)
    (hbMeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable bH (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hbBound : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖bH v‖ ≤ MB)
    (hProdBound : ∀ y z, ‖prod y z‖ ≤ Cprod * ‖y‖ * ‖z‖)
    (hDecay : ∀ t v, 0 ≤ v → v ≤ t →
      ‖expH ((∫ q in (0 : ℝ)..t, aH q) -
        (∫ q in (0 : ℝ)..v, aH q))‖ ≤
        (E0 + E1 * (t-v) + E2 * (t-v)^2) *
          Real.exp (-((2*m)*(t-v))))
    /- UNIVERSAL STANDARD Sobolev continuous-representative and Bochner
       Fubini interfaces. `rep` is the canonical H² -> C⁰ pointwise
       representative (valid for d <= 3). Using `rep` avoids asserting that
       arbitrary Lp.coeFn choices work jointly for all time parameters. -/
    (rep : H → X → ℝ)
    (hCanonicalRep : ∀ z : H, ∀ᵐ x ∂μ,
      (embed z x : ℝ) = rep z x)
    (hStdSpatialOps : ∀ᵐ x ∂μ,
      (∀ z w : H, rep (z - w) x = rep z x - rep w x) ∧
      (∀ z w : H, rep (prod z w) x = rep z x * rep w x) ∧
      (∀ z : H, rep (expH z) x = Real.exp (-(rep z x))))
    (hPointwiseBochner :
      ∀ (t : ℝ) (k : ℝ → H), 0 ≤ t →
        Integrable k (volume.restrict (Set.Ioc (0 : ℝ) t)) →
        ∀ᵐ x ∂μ,
          (embed (∫ v in (0 : ℝ)..t, k v) x : ℝ) =
          ∫ v, rep (k v) x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hInitialRep : ∀ᵐ x ∂μ, rep Y0 x =
      Real.exp (s * gamma1 x * u x 0) / R0 x)
    (hPrimitiveRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      rep (∫ q in (0 : ℝ)..t, aH q) x =
        ReservoirSeismicityControl.srReciprocalPrimitive
          (fun q => gamma2 x q * Rstar x) t)
    /- Joint representatives of the PHYSICAL A3 coefficient and forcing,
       obtained by the standard time/space Fubini and Sobolev factor rules.
       They concern a and b, NOT the solution Y or its regularity. -/
    (hPrimitiveJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (∫ q in (0 : ℝ)..v, aH q) x =
        ReservoirSeismicityControl.srReciprocalPrimitive
          (fun q => gamma2 x q * Rstar x) v)
    (hForcingJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (bH v) x =
          gamma2 x v * Real.exp (s * gamma1 x * u x v)) :
    let F := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
    let Fhom := E0 + E1 * (2*m)⁻¹ + E2 * (((2*m)/2)⁻¹)^2
    let Ybound := Cprod * MY0 * Fhom + Cprod * MB * F / m
    ∀ t, 0 ≤ t → ∃ y : H,
      embed y = physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp t ∧
      ‖y‖ ≤ Ybound := by
  dsimp only
  intro t ht
  let A : ℝ → H := fun q => ∫ v in (0 : ℝ)..q, aH v
  let E : ℝ → H := fun v => expH (A t - A v)
  let K : ℝ → H := fun v => prod (E v) (bH v)
  let H0 : H := prod (expH (A t)) Y0
  have hCandidate := a7_M1_causal_H2_candidate_uniform_from_coefficients
    aH bH Y0 expH prod hExp hProdCont
    m Cprod MB MY0 E0 E1 E2
    hm hCprod hMB hMY0 hE0 hE1 hE2
    hY0 ha hbMeas hbBound hProdBound hDecay t ht
  rcases hCandidate with ⟨y, hyFormula, hyBound⟩
  have hKint : Integrable K
       (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have hk := a7_physical_kernel_measurable_integrable_of_coefficient
      aH bH expH prod hExp hProdCont t (2*m) Cprod MB E0 E1 E2
      ht (by positivity) hCprod hMB hE0 hE1 hE2
      (ha t ht) (hbMeas t ht) (hbBound t ht) hProdBound
      (fun v hv hvt => hDecay t v hv.le hvt)
    dsimp only at hk
    exact hk.2.2
  have hEmbedInt : embed (∫ v in (0 : ℝ)..t, K v) =
      ∫ v, embed (K v)
         ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    rw [intervalIntegral.integral_of_le ht]
    exact (ContinuousLinearMap.integral_comp_comm embed hKint).symm
  have hEmbedFormula : embed y = embed H0 +
      ∫ v, embed (K v) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have h : y = H0 + ∫ v in (0 : ℝ)..t, K v := by
      simpa only [H0, K, E, A] using hyFormula
    rw [h, map_add, hEmbedInt]
  have hHomRep : ∀ᵐ x ∂μ,
      (embed H0 x : ℝ) =
        Real.exp (-ReservoirSeismicityControl.srReciprocalPrimitive
          (fun q => gamma2 x q * Rstar x) t) *
          (Real.exp (s * gamma1 x * u x 0) / R0 x) := by
    filter_upwards [hCanonicalRep H0, hStdSpatialOps,
      hPrimitiveRep t ht, hInitialRep]
      with x hcanon hops hprim hinit
    obtain ⟨_hsub, hprod, hexp⟩ := hops
    rw [hcanon, hprod (expH (A t)) Y0, hexp (A t), hprim, hinit]
  have hIntegralRep : ∀ᵐ x ∂μ,
      ((∫ v, embed (K v)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) x : ℝ) =
      ∫ v, rep (K v) x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have hBF := hPointwiseBochner t K ht hKint
    simpa only [hEmbedInt] using hBF
  have hActualRep := physical_signed_YL2_represents_actual_solution
    μ gamma1 Rstar R0 gamma2 u s hYLp t ht
  have hCausalRep : ∀ᵐ x ∂μ,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (K v) x =
          ReservoirSeismicityControl.srSignedDuhamelFactor
            (fun q => gamma2 x q * Rstar x) t v *
            (gamma2 x v * Real.exp (s * gamma1 x * u x v)) := by
    filter_upwards [hStdSpatialOps, hPrimitiveRep t ht,
      hPrimitiveJointRep t ht, hForcingJointRep t ht]
      with x hops hAt hAv hBv
    obtain ⟨hsub, hprod, hexp⟩ := hops
    filter_upwards [hAv, hBv] with v hav hbv
    change rep (prod (expH (A t - A v)) (bH v)) x = _
    rw [hprod (expH (A t - A v)) (bH v),
      hexp (A t - A v), hsub (A t) (A v), hAt, hav, hbv]
    unfold ReservoirSeismicityControl.srSignedDuhamelFactor
    congr 1
    congr 1
    ring
  have hIntegralScalar : ∀ᵐ x ∂μ,
      (∫ v, rep (K v) x
         ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
      ∫ v in (0 : ℝ)..t,
        ReservoirSeismicityControl.srSignedDuhamelFactor
          (fun q => gamma2 x q * Rstar x) t v *
          (gamma2 x v * Real.exp (s * gamma1 x * u x v)) := by
    filter_upwards [hCausalRep] with x hx
    rw [intervalIntegral.integral_of_le ht]
    exact integral_congr_ae hx
  have hExt : embed y =
      physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp t := by
    apply Lp.ext
    filter_upwards [hHomRep, hIntegralRep, hIntegralScalar, hActualRep,
      Lp.coeFn_add (embed H0)
        (∫ v, embed (K v) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))]
      with x hhom hbochner hscalar hactual hadd
    have hYpoint :
        (embed y x : ℝ) =
          (embed H0 x : ℝ) +
          ((∫ v, embed (K v)
             ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) x : ℝ) := by
      rw [hEmbedFormula, hadd]
      rfl
    calc
      (embed y x : ℝ) =
          (embed H0 x : ℝ) +
          ((∫ v, embed (K v)
             ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) x : ℝ) := hYpoint
      _ = Real.exp (-ReservoirSeismicityControl.srReciprocalPrimitive
            (fun q => gamma2 x q * Rstar x) t) *
            (Real.exp (s * gamma1 x * u x 0) / R0 x) +
          ∫ v in (0 : ℝ)..t,
            ReservoirSeismicityControl.srSignedDuhamelFactor
              (fun q => gamma2 x q * Rstar x) t v *
              (gamma2 x v * Real.exp (s * gamma1 x * u x v)) := by
          rw [hhom, hbochner, hscalar]
      _ = ReservoirSeismicityControl.srReciprocalExplicit
            (fun q => gamma2 x q * Rstar x)
            (fun q => gamma2 x q * Real.exp (s * gamma1 x * u x q))
            (Real.exp (s * gamma1 x * u x 0) / R0 x) t := by
          exact (ReservoirSeismicityControl.sr_signed_reciprocal_explicit_duhamel _ _ _ _).symm
      _ = (physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp t x : ℝ) :=
          hactual.symm
  exact ⟨y, hExt, hyBound⟩

#print axioms a7_M1_actual_signed_Y_uniform_H2_from_standard_results


/-- Actual physical seismicity rate from the *already established* physical
signed-Y M1 conclusion and the UNIVERSAL standard positive H² quotient rule.
The quotient theorem is quantified over ALL Sobolev numerators/denominators,
not over the physical R, and therefore does not assume H² regularity of R.
The signed pointwise R formula is the existing model definition. -/
theorem a7_M2_actual_signed_R_uniform_H2_from_verified_M1
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) (embed : H →L[ℝ] Lp ℝ 2 μ)
    (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hYLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ)
    (hRLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) μ)
    (N : ℝ → H) (MN Ybound Cquot ymin : ℝ)
    (hMN : 0 ≤ MN) (hCquot : 0 ≤ Cquot) (hymin : 0 < ymin)
    (hNnorm : ∀ t, 0 ≤ t → ‖N t‖ ≤ MN)
    (hNrep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      (embed (N t) x : ℝ) = Real.exp (s * gamma1 x * u x t))
    (hYpositive : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      ymin ≤ physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
    (hM1 : ∀ t, 0 ≤ t → ∃ y : H,
      embed y = physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp t ∧
      ‖y‖ ≤ Ybound)
    /- STANDARD weak H² positive quotient result, applicable to ANY
       numerator and ANY denominator bounded below by ymin. -/
    (quotH : H → H → H)
    (hQuotRep : ∀ n y : H,
      (∀ᵐ x ∂μ, ymin ≤ (embed y x : ℝ)) →
      ∀ᵐ x ∂μ,
        (embed (quotH n y) x : ℝ) =
          (embed n x : ℝ) / (embed y x : ℝ))
    (hQuotNorm : ∀ n y : H,
      (∀ᵐ x ∂μ, ymin ≤ (embed y x : ℝ)) →
      ‖quotH n y‖ ≤ Cquot * ‖n‖ * (1 + ‖y‖ + ‖y‖^2)) :
    ∀ t, 0 ≤ t → ∃ r : H,
      embed r = physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t ∧
      ‖r‖ ≤ Cquot * MN * (1 + Ybound + Ybound^2) := by
  intro t ht
  obtain ⟨y, hyRep, hyBound⟩ := hM1 t ht
  have hYexact : ∀ᵐ x ∂μ,
      (embed y x : ℝ) =
        physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t := by
    have h := physical_signed_YL2_represents_actual_solution
      μ gamma1 Rstar R0 gamma2 u s hYLp t ht
    simpa only [hyRep, physicalSignedYScalar] using h
  have hYmin : ∀ᵐ x ∂μ, ymin ≤ (embed y x : ℝ) := by
    filter_upwards [hYpositive t ht, hYexact] with x hpos hxe
    rw [hxe]
    exact hpos
  have hQuot := hQuotRep (N t) y hYmin
  have hActualR := physical_signed_RL2_represents_actual_solution
    μ gamma1 Rstar R0 gamma2 u s hRLp t ht
  have hRrep : embed (quotH (N t) y) =
      physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t := by
    apply Lp.ext
    filter_upwards [hQuot, hNrep t ht, hYexact, hActualR]
      with x hq hn hy hr
    calc
      (embed (quotH (N t) y) x : ℝ) =
        (embed (N t) x : ℝ) / (embed y x : ℝ) := hq
      _ = Real.exp (s * gamma1 x * u x t) *
            (physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)⁻¹ := by
          rw [hn, hy, div_eq_mul_inv]
      _ = (physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t x : ℝ) :=
          hr.symm
  have hYnonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hYboundNonneg : 0 ≤ Ybound := le_trans hYnonneg hyBound
  have hYsq : ‖y‖ ^ 2 ≤ Ybound ^ 2 := by
    calc
      ‖y‖ ^ 2 = ‖y‖ * ‖y‖ := pow_two _
      _ ≤ Ybound * ‖y‖ :=
        mul_le_mul_of_nonneg_right hyBound hYnonneg
      _ ≤ Ybound * Ybound :=
        mul_le_mul_of_nonneg_left hyBound hYboundNonneg
      _ = Ybound ^ 2 := (pow_two _).symm
  have hPoly : 1 + ‖y‖ + ‖y‖^2 ≤ 1 + Ybound + Ybound^2 := by
    linarith
  have hPolyPos : 0 ≤ 1 + ‖y‖ + ‖y‖^2 := by positivity
  have hRq : ‖quotH (N t) y‖ ≤
      Cquot * MN * (1 + Ybound + Ybound^2) := by
    calc
      ‖quotH (N t) y‖ ≤
          Cquot * ‖N t‖ * (1 + ‖y‖ + ‖y‖^2) :=
        hQuotNorm (N t) y hYmin
      _ ≤ Cquot * MN * (1 + ‖y‖ + ‖y‖^2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hNnorm t ht) hCquot) hPolyPos
      _ ≤ Cquot * MN * (1 + Ybound + Ybound^2) := by
        exact mul_le_mul_of_nonneg_left hPoly
          (mul_nonneg hCquot hMN)
  exact ⟨quotH (N t) y, hRrep, hRq⟩

#print axioms a7_M2_actual_signed_R_uniform_H2_from_verified_M1

end ReservoirSeismicityControl.Paper2026
