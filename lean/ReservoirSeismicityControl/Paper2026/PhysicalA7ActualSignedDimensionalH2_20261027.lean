import ReservoirSeismicityControl.Paper2026.PhysicalA7DimensionalWeakH2_20261027
import ReservoirSeismicityControl.Paper2026.PhysicalA7M1M2ActualSignedClosure20261026
import Mathlib.Tactic

/-!
# Actual signed seismicity rate in the dimension-parametric physical H² space

This is the direct, concrete dimensional instantiation of the ALREADY PASSED
physical A7-M1/M2 theorems. The spatial Sobolev space is the actual closed
weak-derivative graph over `Fin n_d → ℝ`; it has `1+n_d+n_d²` L² entries.

The theorem does not assume H² regularity of the actual signed reciprocal or
seismicity rate. It derives both from the previously proved signed Duhamel
estimate and positive quotient argument. Its external premises are the same
*universal* classical Sobolev composition/product/quotient and Bochner/Fubini
results required by the existing physical 3D theorem. No foundational PDE or
Sobolev theory is reproved here.

This does not yet establish the separate compact-cutoff-to-Neumann graph lift
used in A10; that elliptic result must be applied with the same local geometry.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

set_option maxHeartbeats 1500000

/-- Uniform local H² for the **actual** signed physical SR for all paper
spatial dimensions. Neither actual Y nor actual R is assumed to lie in H²;
we instantiate both passing M1 and M2 theorems in the concrete n_d-jet graph.

The spatial operations and Bochner/Fubini identities below are *general*
standard analysis principles on the local H² space, not assumptions that the
physical seismicity rate already possesses the desired regularity. -/
theorem a7_actual_signed_SR_dimensional_H2_of_standard_results
    {n_d : ℕ} (hd : PaperSpatialDimension n_d)
    (U : Set (PaperSpatial n_d))
    (gamma1 Rstar R0 : PaperSpatial n_d → ℝ)
    (gamma2 u : PaperSpatial n_d → ℝ → ℝ) (s : ℝ)
    (hYLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) (volume.restrict U))
    (hRLp : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x => physicalSignedRScalar gamma1 Rstar R0 gamma2 u s x t)
        (2 : ENNReal) (volume.restrict U))
    (aH bH : ℝ → A7DimensionalH2 n_d U)
    (Y0 : A7DimensionalH2 n_d U)
    (expH : A7DimensionalH2 n_d U → A7DimensionalH2 n_d U)
    (prod : A7DimensionalH2 n_d U → A7DimensionalH2 n_d U →
      A7DimensionalH2 n_d U)
    (hExp : Continuous expH)
    (hProdCont : Continuous (fun z : A7DimensionalH2 n_d U ×
      A7DimensionalH2 n_d U => prod z.1 z.2))
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
    (rep : A7DimensionalH2 n_d U → PaperSpatial n_d → ℝ)
    (hCanonicalRep : ∀ z : A7DimensionalH2 n_d U,
      ∀ᵐ x ∂(volume.restrict U),
      (a7DimensionalH2Embedding n_d U z x : ℝ) = rep z x)
    (hStdSpatialOps : ∀ᵐ x ∂(volume.restrict U),
      (∀ z w : A7DimensionalH2 n_d U,
        rep (z - w) x = rep z x - rep w x) ∧
      (∀ z w : A7DimensionalH2 n_d U,
        rep (prod z w) x = rep z x * rep w x) ∧
      (∀ z : A7DimensionalH2 n_d U,
        rep (expH z) x = Real.exp (-(rep z x))))
    (hPointwiseBochner :
      ∀ (t : ℝ) (k : ℝ → A7DimensionalH2 n_d U), 0 ≤ t →
        Integrable k (volume.restrict (Set.Ioc (0 : ℝ) t)) →
        ∀ᵐ x ∂(volume.restrict U),
          (a7DimensionalH2Embedding n_d U
            (∫ v in (0 : ℝ)..t, k v) x : ℝ) =
          ∫ v, rep (k v) x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hInitialRep : ∀ᵐ x ∂(volume.restrict U), rep Y0 x =
      Real.exp (s * gamma1 x * u x 0) / R0 x)
    (hPrimitiveRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict U),
      rep (∫ q in (0 : ℝ)..t, aH q) x =
        ReservoirSeismicityControl.srReciprocalPrimitive
          (fun q => gamma2 x q * Rstar x) t)
    (hPrimitiveJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict U),
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (∫ q in (0 : ℝ)..v, aH q) x =
          ReservoirSeismicityControl.srReciprocalPrimitive
            (fun q => gamma2 x q * Rstar x) v)
    (hForcingJointRep : ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict U),
      ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        rep (bH v) x =
          gamma2 x v * Real.exp (s * gamma1 x * u x v))
    (N : ℝ → A7DimensionalH2 n_d U) (MN Cquot ymin : ℝ)
    (hMN : 0 ≤ MN) (hCquot : 0 ≤ Cquot) (hymin : 0 < ymin)
    (hNnorm : ∀ t, 0 ≤ t → ‖N t‖ ≤ MN)
    (hNrep : ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict U),
      (a7DimensionalH2Embedding n_d U (N t) x : ℝ) =
        Real.exp (s * gamma1 x * u x t))
    (hYpositive : ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict U),
      ymin ≤ physicalSignedYScalar gamma1 Rstar R0 gamma2 u s x t)
    (quotH : A7DimensionalH2 n_d U → A7DimensionalH2 n_d U →
      A7DimensionalH2 n_d U)
    (hQuotRep : ∀ n y : A7DimensionalH2 n_d U,
      (∀ᵐ x ∂(volume.restrict U),
        ymin ≤ (a7DimensionalH2Embedding n_d U y x : ℝ)) →
      ∀ᵐ x ∂(volume.restrict U),
        (a7DimensionalH2Embedding n_d U (quotH n y) x : ℝ) =
          (a7DimensionalH2Embedding n_d U n x : ℝ) /
          (a7DimensionalH2Embedding n_d U y x : ℝ))
    (hQuotNorm : ∀ n y : A7DimensionalH2 n_d U,
      (∀ᵐ x ∂(volume.restrict U),
        ymin ≤ (a7DimensionalH2Embedding n_d U y x : ℝ)) →
      ‖quotH n y‖ ≤ Cquot * ‖n‖ * (1 + ‖y‖ + ‖y‖^2)) :
    let μ : Measure (PaperSpatial n_d) := volume.restrict U
    let F : ℝ := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
    let Fhom : ℝ := E0 + E1 * (2*m)⁻¹ + E2 * (((2*m)/2)⁻¹)^2
    let Ybound : ℝ := Cprod * MY0 * Fhom + Cprod * MB * F / m
    ∀ t : ℝ, 0 ≤ t →
      ∃ r : A7DimensionalH2 n_d U,
        a7DimensionalH2Embedding n_d U r =
          physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t ∧
        ‖r‖ ≤ Cquot * MN * (1 + Ybound + Ybound^2) := by
  let μ : Measure (PaperSpatial n_d) := volume.restrict U
  let F : ℝ := E0 + E1 * m⁻¹ + E2 * ((m/2)⁻¹)^2
  let Fhom : ℝ := E0 + E1 * (2*m)⁻¹ + E2 * (((2*m)/2)⁻¹)^2
  let Ybound : ℝ := Cprod * MY0 * Fhom + Cprod * MB * F / m
  have hM1 := a7_M1_actual_signed_Y_uniform_H2_from_standard_results
    μ (a7DimensionalH2Embedding n_d U)
    gamma1 Rstar R0 gamma2 u s hYLp
    aH bH Y0 expH prod hExp hProdCont
    m Cprod MB MY0 E0 E1 E2
    hm hCprod hMB hMY0 hE0 hE1 hE2
    hY0 ha hbMeas hbBound hProdBound hDecay
    rep hCanonicalRep hStdSpatialOps hPointwiseBochner
    hInitialRep hPrimitiveRep hPrimitiveJointRep hForcingJointRep
  dsimp only at hM1
  change ∀ t : ℝ, 0 ≤ t → ∃ r : A7DimensionalH2 n_d U,
    a7DimensionalH2Embedding n_d U r =
      physicalSignedRL2 μ gamma1 Rstar R0 gamma2 u s hRLp t ∧
    ‖r‖ ≤ Cquot * MN * (1 + Ybound + Ybound^2)
  exact a7_M2_actual_signed_R_uniform_H2_from_verified_M1
    μ (a7DimensionalH2Embedding n_d U)
    gamma1 Rstar R0 gamma2 u s hYLp hRLp
    N MN Ybound Cquot ymin hMN hCquot hymin
    hNnorm hNrep hYpositive hM1
    quotH hQuotRep hQuotNorm

#print axioms a7_actual_signed_SR_dimensional_H2_of_standard_results

end ReservoirSeismicityControl.Paper2026
