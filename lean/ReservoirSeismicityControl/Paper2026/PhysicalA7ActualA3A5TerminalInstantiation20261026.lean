import ReservoirSeismicityControl.Paper2026.PhysicalA7M1M2ActualSignedClosure20261026
import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualL2FromBox20261026
import ReservoirSeismicityControl.SeismicitySignedReciprocalUniformBox
import Mathlib.Tactic

/-!
# Physical A7: coefficient and initial-data instantiation of the passing M1/M2 closure

Theorems M1/M2 and their preceding kernel / Caratheodory proofs are frozen.
This theorem CONSTRUCTS (rather than postulates) their aH, bH, N, Y0,
forcing measurability and bounds, the scalar comparison Y-box,
physical-L² certificates, primitive identification and H² propagator decay.

External results are universally stated, STANDARD Sobolev calculus, continuous
point-evaluation/Bochner-Fubini, bounded measurable integration and scalar
integral comparison. No statement assumes that actual Y or R is H².

The base physical data are the H² classes of gamma1, R*, R0, gamma2(t),
and u(t), together with their physical representatives and the A3/A4/A5
bounds. Time continuity of the scalar coefficients is the already established
Caratheodory applicability condition, not a derivative assumption on Q.

The H² spaces can be instantiated for any n_d=1,2,3; H is generic only so
that the *standard* H² calculus may be supplied without reproving its theory.
For the current project's fully concrete graph set H = A7PhysicalH2 U
and embed = a7PhysicalH2Embedding U (3D case).
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
set_option maxHeartbeats 2500000

/-- Actual A3/A5 coefficients and their Sobolev representatives produce the
uniform H² bounds of the ACTUAL signed Y and R (A7). No Y/R H² hypothesis.
Standard analysis results are UNIVERSAL over arbitrary coefficients or Sobolev
functions, and are identified individually below. -/
theorem physical_A7_actual_A3_A5_terminal_instantiation
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    (embed : H →L[ℝ] Lp ℝ 2 μ)
    (rep : H → X → ℝ)
    (gamma1 Rstar R0 : X → ℝ)
    (gamma2 u : X → ℝ → ℝ) (s : ℝ)
    (hs : s = -1 ∨ s = 1)
    (g1H starH r0H : H) (g2H uH : ℝ → H)
    (prod : H → H → H) (expH : H → H) (quotH : H → H → H)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : H × H => prod z.1 z.2))
    (Cprod Mg1 Mstar Mr0 Mg2 Mu MN : ℝ)
    (hCprod : 0 ≤ Cprod) (hMg1 : 0 ≤ Mg1)
    (hMstar : 0 ≤ Mstar) (hMr0 : 0 ≤ Mr0)
    (hMg2 : 0 ≤ Mg2) (hMu : 0 ≤ Mu) (hMN : 0 ≤ MN)
    (hg1Norm : ‖g1H‖ ≤ Mg1)
    (hStarNorm : ‖starH‖ ≤ Mstar)
    (hr0Norm : ‖r0H‖ ≤ Mr0)
    (hg2Norm : ∀ t, 0 ≤ t → ‖g2H t‖ ≤ Mg2)
    (huNorm : ∀ t, 0 ≤ t → ‖uH t‖ ≤ Mu)
    (hg2Meas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable g2H (volume.restrict (Set.Ioc (0 : ℝ) t)))
    (huMeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable uH (volume.restrict (Set.Ioc (0 : ℝ) t)))
    /- Genuine A3/A4/A5 representatives on ONE spatial full-measure set;
       a coherent Sobolev version is standard on bounded Lipschitz regions. -/
    (hPhysicalReps : ∀ᵐ x ∂μ,
      rep g1H x = gamma1 x ∧
      rep starH x = Rstar x ∧
      rep r0H x = R0 x ∧
      (∀ t, 0 ≤ t →
        rep (g2H t) x = gamma2 x t ∧ rep (uH t) x = u x t))
    /- Universal H² Sobolev point representative and algebra operations. -/
    (hCanonicalRep : ∀ z : H, ∀ᵐ x ∂μ,
      (embed z x : ℝ) = rep z x)
    (hStdSpatialOps : ∀ᵐ x ∂μ,
      (∀ z w : H, rep (z-w) x = rep z x - rep w x) ∧
      (∀ z w : H, rep (prod z w) x = rep z x * rep w x) ∧
      (∀ z : H, rep (expH z) x = Real.exp (-(rep z x))) ∧
      (∀ c : ℝ, ∀ z : H, rep (c • z) x = c * rep z x))
    (hProdBound : ∀ y z, ‖prod y z‖ ≤ Cprod * ‖y‖ * ‖z‖)
    (Cembed : ℝ) (hCembed : 0 ≤ Cembed)
    (hStdEmbedSup : ∀ z : H, ∀ᵐ x ∂μ,
      |rep z x| ≤ Cembed * ‖z‖)
    /- Standard bounded-range smooth H² exponential estimate (all z). -/
    (hStdExpBound : ∀ z : H,
      ‖z‖ ≤ Cprod * Mg1 * Mu → ‖expH z‖ ≤ MN)
    /- Scalar comparison input is ONLY the A3/A4/A5 COEFFICIENT BOX,
       and the initial value. No positivity assumption on Y. -/
    (aMin aMax bMin bMax y0Min y0Max R0m : ℝ)
    (haMin : 0 < aMin) (haMax : 0 < aMax)
    (hbMin : 0 < bMin) (hy0Min : 0 < y0Min)
    (hR0m : 0 < R0m)
    (hR0Positive : ∀ᵐ x ∂μ, R0m ≤ R0 x)
    (hScalarA3A4A5 : ∀ᵐ x ∂μ,
      (∀ t, 0 ≤ t →
        aMin ≤ gamma2 x t * Rstar x ∧
        gamma2 x t * Rstar x ≤ aMax) ∧
      (∀ t, 0 ≤ t →
        bMin ≤ gamma2 x t * Real.exp (s * gamma1 x * u x t) ∧
        gamma2 x t * Real.exp (s * gamma1 x * u x t) ≤ bMax) ∧
      y0Min ≤ Real.exp (s * gamma1 x * u x 0) / R0 x ∧
      Real.exp (s * gamma1 x * u x 0) / R0 x ≤ y0Max ∧
      Continuous (fun t => gamma2 x t * Rstar x) ∧
      Continuous (fun t => gamma2 x t * Real.exp (s * gamma1 x * u x t)))
    /- GENERAL standard measurable Caratheodory-solution theorem, applied
       to the scalar physical coefficients; these two are measurability
       certificates, not claims about spatial derivatives of Y or R. -/
    (hYmeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    (hRmeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable
        (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t) μ)
    /- Standard positive Sobolev quotient, universally for ALL n,y. -/
    (hQuotRep0 : ∀ (n y : H),
      (∀ᵐ x ∂μ, R0m ≤ (embed y x : ℝ)) →
      ∀ᵐ x ∂μ,
        (embed (quotH n y) x : ℝ) =
          (embed n x : ℝ) / (embed y x : ℝ))
    (hQuotRepY : ∀ (n y : H),
      (∀ᵐ x ∂μ, min y0Min (bMin/aMax) ≤ (embed y x : ℝ)) →
      ∀ᵐ x ∂μ,
        (embed (quotH n y) x : ℝ) =
          (embed n x : ℝ) / (embed y x : ℝ))
    (Cquot0 CquotY : ℝ) (hCquot0 : 0 ≤ Cquot0)
    (hCquotY : 0 ≤ CquotY)
    (hQuotNorm0 : ∀ (n y : H),
      (∀ᵐ x ∂μ, R0m ≤ (embed y x : ℝ)) →
      ‖quotH n y‖ ≤
        Cquot0 * ‖n‖ * (1 + ‖y‖ + ‖y‖^2))
    (hQuotNormY : ∀ (n y : H),
      (∀ᵐ x ∂μ, min y0Min (bMin/aMax) ≤ (embed y x : ℝ)) →
      ‖quotH n y‖ ≤
        CquotY * ‖n‖ * (1 + ‖y‖ + ‖y‖^2))
    /- Four universally quantified STANDARD time/Sobolev theorems:
       bounded-measurable integration, integral growth, canonical
       representative-time Fubini and damped H² smooth composition. -/
    (hStdFiniteTimeIntegrable : ∀ (f : ℝ → H) (M t : ℝ),
      0 ≤ t →
      AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) t)) →
      (∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖f v‖ ≤ M) →
      IntervalIntegrable f volume 0 t)
    (hStdPrimitiveNorm : ∀ (f : ℝ → H) (M v t : ℝ),
      0 ≤ v → v ≤ t →
      IntervalIntegrable f volume 0 t →
      (∀ᵐ q ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖f q‖ ≤ M) →
      ‖(∫ q in (0 : ℝ)..t, f q) - (∫ q in (0 : ℝ)..v, f q)‖ ≤
        M * (t-v))
    (hStdTimeRepresentative : ∀ (f : ℝ → H) (g : X → ℝ → ℝ),
      (∀ t, 0 ≤ t → IntervalIntegrable f volume 0 t) →
      (∀ᵐ x ∂μ, ∀ q, 0 ≤ q → rep (f q) x = g x q) →
      ∀ᵐ x ∂μ, ∀ (v t : ℝ), 0 ≤ v → v ≤ t →
        rep (∫ q in (0 : ℝ)..t, f q) x =
          ∫ q in (0 : ℝ)..t, g x q ∧
        rep (∫ q in (0 : ℝ)..v, f q) x =
          ∫ q in (0 : ℝ)..v, g x q ∧
        rep ((∫ q in (0 : ℝ)..t, f q) -
          (∫ q in (0 : ℝ)..v, f q)) x =
          ∫ q in v..t, g x q)
    (hStdScalarIntegralLower : ∀ (f : ℝ → ℝ) (c v t : ℝ),
      Continuous f →
      (∀ q, 0 ≤ q → c ≤ f q) →
      0 ≤ v → v ≤ t →
      c*(t-v) ≤ ∫ q in v..t, f q)
    (E0 E1 E2 : ℝ) (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hStdDampedExp : ∀ (z : H) (lag : ℝ),
      0 ≤ lag →
      (∀ᵐ x ∂μ, aMin * lag ≤ rep z x) →
      ‖z‖ ≤ (Cprod * Mg2 * Mstar) * lag →
      ‖expH z‖ ≤
        (E0 + E1*lag + E2*lag^2) * Real.exp (-(aMin*lag)))
    /- GENERAL Bochner-L² Fubini theorem, NOT a hypothesis on Y. -/
    (hPointwiseBochner : ∀ (t : ℝ) (k : ℝ → H), 0 ≤ t →
      Integrable k (volume.restrict (Set.Ioc (0 : ℝ) t)) →
      ∀ᵐ x ∂μ,
        (embed (∫ v in (0 : ℝ)..t, k v) x : ℝ) =
          ∫ v, rep (k v) x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) :
    let MA := Cprod * Mg2 * Mstar
    let MB := Cprod * Mg2 * MN
    let MY0 := Cquot0 * MN * (1 + Mr0 + Mr0^2)
    let m := aMin / 2
    let F := E0 + E1*m⁻¹ + E2*((m/2)⁻¹)^2
    let Fhom := E0 + E1*(2*m)⁻¹ + E2*(((2*m)/2)⁻¹)^2
    let Ybound := Cprod * MY0 * Fhom + Cprod * MB * F/m
    let Rbound := CquotY * MN * (1+Ybound+Ybound^2)
    ∀ t, 0 ≤ t →
      ∃ y r : H,
        (∃ hYLp : ∀ q : ℝ, 0 ≤ q →
           MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x q)
             (2 : ENNReal) μ,
          embed y = physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp t) ∧
        (∃ hRLp : ∀ q : ℝ, 0 ≤ q →
           MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x q)
             (2 : ENNReal) μ,
          embed r = physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t) ∧
        ‖y‖ ≤ Ybound ∧ ‖r‖ ≤ Rbound := by
  dsimp only
  let MA : ℝ := Cprod*Mg2*Mstar
  let MB : ℝ := Cprod*Mg2*MN
  let MY0 : ℝ := Cquot0*MN*(1+Mr0+Mr0^2)
  let m : ℝ := aMin/2
  let F : ℝ := E0+E1*m⁻¹+E2*((m/2)⁻¹)^2
  let Fhom : ℝ := E0+E1*(2*m)⁻¹+E2*(((2*m)/2)⁻¹)^2
  let Ybound : ℝ := Cprod*MY0*Fhom+Cprod*MB*F/m
  let Rbound : ℝ := CquotY*MN*(1+Ybound+Ybound^2)
  let N : ℝ → H := fun t => expH ((-s) • prod g1H (uH t))
  let aH : ℝ → H := fun t => prod (g2H t) starH
  let bH : ℝ → H := fun t => prod (g2H t) (N t)
  let Y0 : H := quotH (N 0) r0H
  have hsabs : |s| = 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  have hNinput : ∀ t, 0 ≤ t → ‖(-s) • prod g1H (uH t)‖ ≤
      Cprod * Mg1 * Mu := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_neg, hsabs, one_mul]
    calc
      ‖prod g1H (uH t)‖ ≤ Cprod * ‖g1H‖ * ‖uH t‖ := hProdBound _ _
      _ ≤ Cprod * Mg1 * ‖uH t‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hg1Norm hCprod) (norm_nonneg _)
      _ ≤ Cprod * Mg1 * Mu := by
        exact mul_le_mul_of_nonneg_left (huNorm t ht)
          (mul_nonneg hCprod hMg1)
  have hNnorm : ∀ t, 0 ≤ t → ‖N t‖ ≤ MN := by
    intro t ht
    exact hStdExpBound _ (hNinput t ht)
  have hAnorm : ∀ t, 0 ≤ t → ‖aH t‖ ≤ MA := by
    intro t ht
    calc
      ‖aH t‖ ≤ Cprod * ‖g2H t‖ * ‖starH‖ := hProdBound _ _
      _ ≤ Cprod * Mg2 * ‖starH‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hg2Norm t ht) hCprod) (norm_nonneg _)
      _ ≤ MA := by
        exact mul_le_mul_of_nonneg_left hStarNorm
          (mul_nonneg hCprod hMg2)
  have hBnorm : ∀ t, 0 ≤ t → ‖bH t‖ ≤ MB := by
    intro t ht
    calc
      ‖bH t‖ ≤ Cprod * ‖g2H t‖ * ‖N t‖ := hProdBound _ _
      _ ≤ Cprod * Mg2 * ‖N t‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hg2Norm t ht) hCprod) (norm_nonneg _)
      _ ≤ MB := by
        exact mul_le_mul_of_nonneg_left (hNnorm t ht)
          (mul_nonneg hCprod hMg2)
  have hNcont : Continuous (fun z : H => expH ((-s) • prod g1H z)) := by
    have hP : Continuous (fun z : H => prod g1H z) :=
      hProdCont.comp (continuous_const.prodMk continuous_id)
    exact hExp.comp (continuous_const.smul hP)
  have hAcont : Continuous (fun z : H => prod z starH) :=
    hProdCont.comp (continuous_id.prodMk continuous_const)
  have hNmeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable N (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro t ht
    exact hNcont.comp_aestronglyMeasurable (huMeas t ht)
  have hAmeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable aH (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro t ht
    exact hAcont.comp_aestronglyMeasurable (hg2Meas t ht)
  have hBmeas : ∀ t, 0 ≤ t →
      AEStronglyMeasurable bH (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro t ht
    exact hProdCont.comp_aestronglyMeasurable
      ((hg2Meas t ht).prodMk (hNmeas t ht))
  have ha : ∀ t, 0 ≤ t → IntervalIntegrable aH volume 0 t := by
    intro t ht
    apply hStdFiniteTimeIntegrable aH MA t ht (hAmeas t ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hAnorm v hv.1.le
  have hbBound : ∀ t, 0 ≤ t →
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖bH v‖ ≤ MB := by
    intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hBnorm v hv.1.le
  have hRepA : ∀ᵐ x ∂μ, ∀ t, 0 ≤ t →
      rep (aH t) x = gamma2 x t * Rstar x := by
    filter_upwards [hPhysicalReps, hStdSpatialOps] with x hf hops
    obtain ⟨_hg1, hstar, _hr0, htime⟩ := hf
    obtain ⟨_hsub, hprod, _hexp, _hsmul⟩ := hops
    intro t ht
    change rep (prod (g2H t) starH) x = _
    rw [hprod, (htime t ht).1, hstar]
  have hRepN : ∀ᵐ x ∂μ, ∀ t, 0 ≤ t →
      rep (N t) x = Real.exp (s * gamma1 x * u x t) := by
    filter_upwards [hPhysicalReps, hStdSpatialOps] with x hf hops
    obtain ⟨hg1, _hs, _hr0, htime⟩ := hf
    obtain ⟨_hsub, hprod, hexp, hsmul⟩ := hops
    intro t ht
    change rep (expH ((-s) • prod g1H (uH t))) x = _
    rw [hexp, hsmul, hprod, hg1, (htime t ht).2]
    congr 1
    ring
  have hRepB : ∀ᵐ x ∂μ, ∀ t, 0 ≤ t →
      rep (bH t) x = gamma2 x t * Real.exp (s * gamma1 x * u x t) := by
    filter_upwards [hPhysicalReps, hStdSpatialOps, hRepN] with x hf hops hn
    obtain ⟨_hg1, _hs, _hr0, htime⟩ := hf
    obtain ⟨_hsub, hprod, _hexp, _hsmul⟩ := hops
    intro t ht
    change rep (prod (g2H t) (N t)) x = _
    rw [hprod, (htime t ht).1, hn t ht]
  have hR0lower : ∀ᵐ x ∂μ, R0m ≤ (embed r0H x : ℝ) := by
    filter_upwards [hPhysicalReps, hCanonicalRep r0H, hR0Positive]
      with x hf hcan hr0
    rw [hcan, hf.2.2.1]
    exact hr0
  have hY0NormRaw := hQuotNorm0 (N 0) r0H hR0lower
  have hMY0nonneg : 0 ≤ MY0 := by
    dsimp [MY0]
    positivity
  have hY0 : ‖Y0‖ ≤ MY0 := by
    have hn0 := hNnorm 0 (le_refl 0)
    have hrr : 0 ≤ ‖r0H‖ := norm_nonneg _
    have hPoly : 1 + ‖r0H‖ + ‖r0H‖^2 ≤ 1 + Mr0 + Mr0^2 := by
      have hrrMax : 0 ≤ Mr0 := hMr0
      have hsq : ‖r0H‖^2 ≤ Mr0^2 := by
        calc
          ‖r0H‖^2 = ‖r0H‖ * ‖r0H‖ := pow_two _
          _ ≤ Mr0 * ‖r0H‖ :=
            mul_le_mul_of_nonneg_right hr0Norm hrr
          _ ≤ Mr0 * Mr0 :=
            mul_le_mul_of_nonneg_left hr0Norm hrrMax
          _ = Mr0^2 := (pow_two _).symm
      linarith
    calc
      ‖Y0‖ ≤ Cquot0 * ‖N 0‖ * (1+‖r0H‖+‖r0H‖^2) := hY0NormRaw
      _ ≤ Cquot0 * MN * (1+‖r0H‖+‖r0H‖^2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn0 hCquot0) (by positivity)
      _ ≤ MY0 := by
        exact mul_le_mul_of_nonneg_left hPoly
          (mul_nonneg hCquot0 hMN)
  have hInitialRep : ∀ᵐ x ∂μ,
      rep Y0 x = Real.exp (s * gamma1 x * u x 0) / R0 x := by
    have hQ := hQuotRep0 (N 0) r0H hR0lower
    filter_upwards [hQ, hCanonicalRep Y0, hCanonicalRep (N 0),
      hCanonicalRep r0H, hRepN, hPhysicalReps]
      with x hq hy hn hr hnrep hphy
    change (embed Y0 x : ℝ) = _ at hq
    rw [←hy, hq, hn, hr, hnrep 0 (le_refl 0), hphy.2.2.1]
  have hNrep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      (embed (N t) x : ℝ) = Real.exp (s * gamma1 x * u x t) := by
    intro t ht
    filter_upwards [hCanonicalRep (N t), hRepN] with x hc hr
    rw [hc, hr t ht]
  have hYbox : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      min y0Min (bMin/aMax) ≤
        physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ∧
      physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t ≤
        y0Max + bMax/aMin := by
    intro t ht
    filter_upwards [hScalarA3A4A5] with x hx
    rcases hx with ⟨hAbox, hBbox, h0low, h0up, hacont, hbcont⟩
    have hInitialPos : 0 < Real.exp (s * gamma1 x * u x 0) / R0 x :=
      lt_of_lt_of_le hy0Min h0low
    have h := ReservoirSeismicityControl.sr_reciprocal_explicit_uniform_box
      (fun q => gamma2 x q * Rstar x)
      (fun q => gamma2 x q * Real.exp (s * gamma1 x * u x q))
      (Real.exp (s * gamma1 x * u x 0) / R0 x)
      aMin aMax bMin bMax hInitialPos haMin hbMin
      hacont hbcont hAbox hBbox t ht
    dsimp only [physicalSignedYScalar]
    constructor
    · exact (min_le_min_right (bMin/aMax) h0low).trans h.1
    · exact h.2.trans (by
        simpa only [add_comm] using
          (add_le_add_right h0up (bMax / aMin)))
  have hymin : 0 < min y0Min (bMin/aMax) :=
    ReservoirSeismicityControl.sr_reciprocal_uniform_lower_positive y0Min aMax bMin
      hy0Min haMax hbMin
  have hENonneg : 0 ≤ Cembed * MN := mul_nonneg hCembed hMN
  have hExpBound : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      Real.exp (s * gamma1 x * u x t) ≤ Cembed * MN := by
    intro t ht
    filter_upwards [hNrep t ht, hCanonicalRep (N t),
      hStdEmbedSup (N t)] with x hn hc he
    rw [← hc, hn] at he
    exact (le_abs_self _).trans
      (he.trans (mul_le_mul_of_nonneg_left (hNnorm t ht) hCembed))
  obtain ⟨hYLp, hRLp⟩ := physical_signed_actual_Y_R_memLp_from_uniform_box
    μ gamma1 Rstar R0 gamma2 u s
    (min y0Min (bMin/aMax)) (y0Max+bMax/aMin) (Cembed*MN)
    hymin hENonneg hYmeas hRmeas hYbox hExpBound
  have hMA : 0 ≤ MA := by dsimp [MA]; positivity
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hMAself : ∀ t, 0 ≤ t →
      ∀ᵐ q ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), ‖aH q‖ ≤ MA := by
    intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact hAnorm q hq.1.le
  have hAintegrals := hStdTimeRepresentative aH
    (fun x q => gamma2 x q * Rstar x) ha hRepA
  have hPrimitiveRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      rep (∫ q in (0 : ℝ)..t, aH q) x =
        ReservoirSeismicityControl.srReciprocalPrimitive
          (fun q => gamma2 x q * Rstar x) t := by
    intro t ht
    filter_upwards [hAintegrals] with x h
    change rep (∫ q in (0 : ℝ)..t, aH q) x =
      ∫ q in (0 : ℝ)..t, gamma2 x q * Rstar x
    exact (h 0 t (le_refl 0) ht).1
  have hPrimitiveJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (∫ q in (0 : ℝ)..v, aH q) x =
          ReservoirSeismicityControl.srReciprocalPrimitive
            (fun q => gamma2 x q * Rstar x) v := by
    intro t ht
    filter_upwards [hAintegrals] with x h
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    change rep (∫ q in (0 : ℝ)..v, aH q) x =
      ∫ q in (0 : ℝ)..v, gamma2 x q * Rstar x
    exact (h v t hv.1.le hv.2).2.1
  have hForcingJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂μ,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (bH v) x =
          gamma2 x v * Real.exp (s * gamma1 x * u x v) := by
    intro t ht
    filter_upwards [hRepB] with x hb
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hb v hv.1.le
  have hDecay : ∀ t v, 0 ≤ v → v ≤ t →
      ‖expH ((∫ q in (0 : ℝ)..t, aH q) -
        (∫ q in (0 : ℝ)..v, aH q))‖ ≤
        (E0 + E1 * (t-v) + E2 * (t-v)^2) *
          Real.exp (-((2*m)*(t-v))) := by
    intro t v hv hvt
    have ht : 0 ≤ t := hv.trans hvt
    have hlag : 0 ≤ t-v := sub_nonneg.mpr hvt
    have hNorm : ‖(∫ q in (0 : ℝ)..t, aH q) -
          (∫ q in (0 : ℝ)..v, aH q)‖ ≤ MA*(t-v) :=
      hStdPrimitiveNorm aH MA v t hv hvt (ha t ht)
        (hMAself t ht)
    have hLower : ∀ᵐ x ∂μ,
        aMin*(t-v) ≤
          rep ((∫ q in (0 : ℝ)..t, aH q) -
            (∫ q in (0 : ℝ)..v, aH q)) x := by
      filter_upwards [hAintegrals, hScalarA3A4A5] with x hint hx
      obtain ⟨haBound, _hbBound, _hinit0, _hinit1, hacont, _hbcont⟩ := hx
      have hscalar := hStdScalarIntegralLower
        (fun q => gamma2 x q * Rstar x) aMin v t hacont
        (fun q hq => (haBound q hq).1) hv hvt
      rw [(hint v t hv hvt).2.2]
      exact hscalar
    have hD := hStdDampedExp
      ((∫ q in (0 : ℝ)..t, aH q) -
        (∫ q in (0 : ℝ)..v, aH q)) (t-v)
      hlag hLower hNorm
    have hmrel : 2*m = aMin := by dsimp [m]; ring
    simpa only [hmrel] using hD
  have hm : 0 < m := by dsimp [m]; positivity
  have hYBoundNonneg : 0 ≤ MY0 := hMY0nonneg
  have hM1 := a7_M1_actual_signed_Y_uniform_H2_from_standard_results
    μ embed gamma1 Rstar R0 gamma2 u s hYLp
    aH bH Y0 expH prod hExp hProdCont
    m Cprod MB MY0 E0 E1 E2 hm hCprod
    hMB hYBoundNonneg hE0 hE1 hE2
    hY0 ha hBmeas hbBound hProdBound hDecay
    rep hCanonicalRep
    (by
      filter_upwards [hStdSpatialOps] with x hx
      exact ⟨hx.1, hx.2.1, hx.2.2.1⟩)
    hPointwiseBochner hInitialRep hPrimitiveRep
    hPrimitiveJointRep hForcingJointRep
  dsimp only at hM1
  have hM1' : ∀ q, 0 ≤ q → ∃ y : H,
      embed y = physicalSignedYL2 μ gamma1 Rstar R0 gamma2 u s hYLp q ∧
      ‖y‖ ≤ Ybound := by
    simpa only [Ybound, F, Fhom] using hM1
  have hM2 := a7_M2_actual_signed_R_uniform_H2_from_verified_M1
    μ embed gamma1 Rstar R0 gamma2 u s hYLp hRLp N
    MN Ybound CquotY (min y0Min (bMin/aMax))
    hMN hCquotY hymin hNnorm hNrep
    (fun t ht => (hYbox t ht).mono (fun x hx => hx.1))
    hM1' quotH
    hQuotRepY
    hQuotNormY
  intro t ht
  obtain ⟨y, hy, hYnorm⟩ := hM1' t ht
  obtain ⟨r, hr, hRnorm⟩ := hM2 t ht
  exact ⟨y, r, ⟨hYLp, hy⟩, ⟨hRLp, hr⟩, hYnorm, hRnorm⟩

#print axioms physical_A7_actual_A3_A5_terminal_instantiation

end ReservoirSeismicityControl.Paper2026
