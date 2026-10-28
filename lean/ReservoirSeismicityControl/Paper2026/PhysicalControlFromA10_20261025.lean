import ReservoirSeismicityControl.Paper2026.PhysicalA10CompleteControlInputs20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA14NormalizedRate
import ReservoirSeismicityControl.Paper2026.PositiveDemandPhysicalRates
import ReservoirSeismicityControl.Paper2026.PositiveDemandPhysicalBounds
import Mathlib.Tactic

/-!
# A10 to the actual normalized control certificates (21), (22), (28), (29)

This module consumes the previously proved A10 *certificate*, not separate
hypotheses for each Psi bound or derivative. In the unconstrained case it uses
A12 + A14, and in the constrained case it uses B16/B18 + B19. The only
regularity/physical assumptions retained are those required by the existing
upstream theorems, including SR representation and positive-time rate bounds.

The unconstrained A14 theorem internally requests an all-real-time box; we
supply it by the nonnegative-time extension R(max t 0) of the physical SR.
This changes nothing for physical t > 0. No Qdot assumption is introduced.

The external MIMO super-twisting stability result is not formalized here.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix BigOperators
set_option maxHeartbeats 2000000

/-- The three established outputs of the *single* A10 certificate, in the
shape accepted by A14 and B19. No independent postulates about Psi are added. -/
private theorem A10_controls_three_components
    {u r : ℕ}
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lpsi LpsiRate : ℝ)
    (hA10 : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t ∧
        ‖psi t‖ ≤ Lpsi ∧ ‖psiRate t‖ ≤ LpsiRate) :
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psi t‖ ≤ Lpsi) ∧
    (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖psiRate t‖ ≤ LpsiRate) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hA10] with t ht
    exact ht.1
  · filter_upwards [hA10] with t ht
    exact ht.2.1
  · filter_upwards [hA10] with t ht
    exact ht.2.2

/-- Equations (21) and (22), by *application* of the established physical
A12 and A14 theorems. SR pointwise bounds are only required for nonnegative
times, with a harmless clipped extension when calling the old A14 interface.
The regional Psi certificate is precisely the result proved in the previous
A10 application module. -/
theorem paper_A10_to_actual_A12_A14_certificates
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, μ (well j) < ⊤)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(μ.restrict (well j)),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical (max τ 0) x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (γmin γmax Rlower Rmax Cγ CR M : ℝ)
    (hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγorder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hRpos : ∀ s, 0 ≤ s → ∀ j,
      ∀ᵐ x ∂(μ.restrict (well j)),
        Rlower ≤ Rphysical s x ∧ Rphysical s x ≤ Rmax)
    (hint : ∀ s, 0 ≤ s → ∀ j, IntegrableOn
      (fun x => γ₁ x * Rphysical s x) (well j) μ)
    (hCγ : 0 ≤ Cγ) (hM : 0 ≤ M) (hK : ‖Kγ‖ ≤ Cγ)
    (hgeometry : ∀ j : Fin w,
      ((μ.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        μ.real (well j) ≤ M)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lpsi LpsiRate : ℝ)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hA10 : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t ∧
        ‖psi t‖ ≤ Lpsi ∧ ‖psiRate t‖ ≤ LpsiRate) :
    let Rclip : ℝ → X → ℝ := fun s x => Rphysical (max s 0) x
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let normalization := (β₀ / β) * ((lo + hi) / 2)
    let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
    let C := paperA12FullNominalRightInverse
      (paperA12FullNominalMatrix assignment β₀ volume)
    let Lgain := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (paperA14FullPhysicalRateMatrix assignment β normalization volume
        (fun _ => 1)) * M * ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C
    let gain := paperA14ActualGainCLM μ well γ₁ Rclip assignment
      β β₀ normalization volume
    δB < 1 ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
            (paperA12FullPhysicalMatrix μ well γ₁ Rclip assignment
              β normalization volume t * C)‖ ≤ δB) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖deriv (fun s => Ring.inverse (gain s) (psi s)) t‖ ≤
          (1 / (1 - δB)) * LpsiRate +
            (1 / (1 - δB)) *
              (Lgain * ((1 / (1 - δB)) * Lpsi))) := by
  classical
  let Rclip : ℝ → X → ℝ := fun s x => Rphysical (max s 0) x
  let lo := γmin * Rlower
  let hi := γmax * Rmax
  let normalization := (β₀ / β) * ((lo + hi) / 2)
  let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
  let C := paperA12FullNominalRightInverse
    (paperA12FullNominalMatrix assignment β₀ volume)
  let Lgain := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
    (paperA14FullPhysicalRateMatrix assignment β normalization volume
      (fun _ => 1)) * M * ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C
  let gain := paperA14ActualGainCLM μ well γ₁ Rclip assignment
    β β₀ normalization volume
  change δB < 1 ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
            (paperA12FullPhysicalMatrix μ well γ₁ Rclip assignment
              β normalization volume t * C)‖ ≤ δB) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖deriv (fun s => Ring.inverse (gain s) (psi s)) t‖ ≤
          (1 / (1 - δB)) * LpsiRate +
            (1 / (1 - δB)) *
              (Lgain * ((1 / (1 - δB)) * Lpsi)))
  have hRclip : ∀ s j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rlower ≤ Rclip s x ∧ Rclip s x ≤ Rmax := by
    intro s j
    exact hRpos (max s 0) (le_max_right s 0) j
  have hintClip : ∀ s j, IntegrableOn
      (fun x => γ₁ x * Rclip s x) (well j) μ := by
    intro s j
    exact hint (max s 0) (le_max_right s 0) j
  have hC : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t :=
    (A10_controls_three_components psi psiRate Lpsi LpsiRate hA10).1
  have hPsi : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psi t‖ ≤ Lpsi :=
    (A10_controls_three_components psi psiRate Lpsi LpsiRate hA10).2.1
  have hPsiRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖psiRate t‖ ≤ LpsiRate :=
    (A10_controls_three_components psi psiRate Lpsi LpsiRate hA10).2.2
  have hA14 := paper_A14_actual_normalized_rate_bound_from_A3_ae
    μ well hs hfinite γ₁ Rclip R Rdot Kγ hrep hSRDeriv
    assignment β β₀ volume γmin γmax Rlower Rmax Cγ CR M
    hSRRate hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
    hvolume hcovered hpositive hγ hRclip hintClip
    hCγ hM hK hgeometry
    psi psiRate Lpsi LpsiRate hLpsi hLpsiRate
    hPsi hPsiRate hC
  have hA12 (t : ℝ) := paper_A12_full_physical_opNorm_from_A3
    μ well γ₁ Rclip assignment β β₀ volume
    γmin γmax Rlower Rmax t
    hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
    hvolume hcovered hfinite hpositive hγ (hRclip t) (hintClip t)
  refine ⟨(hA12 0).2.1, ?_, ?_⟩
  · intro t ht
    exact (hA12 t).2.2
  · exact hA14

/-- Equations (28) and (29) for the actual well sensitivities, with the
contraction computed from B16's *finite vertex tests* rather than assumed.
The Psi hypotheses are replaced by the single already established A10
certificate. This also recovers the exact nullspace allocation identities.
-/
theorem paper_A10_to_actual_B18_B19_certificates
    {X : Type*} [MeasurableSpace X] {u r w nr k : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (measure : Measure X) (well : Fin w → Set X)
    (hs : ∀ j, MeasurableSet (well j))
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        Rmin j ≤ Rphysical t x ∧ Rphysical t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * Rphysical t x) (well j) measure)
    (R_L2 Rdot : ℝ → Lp ℝ 2 measure)
    (Kγ : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (Cγ CR Mh : ℝ)
    (hCγ : 0 ≤ Cγ) (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ j τ, ∀ᵐ x ∂(measure.restrict (well j)),
      ((Kγ (R_L2 τ)) x : ℝ) = γ₁ x * Rphysical (max τ 0) x)
    (hSRDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R_L2 (Rdot t) t)
    (hSRRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖Rdot t‖ ≤ CR)
    (hgeometry : ∀ j : Fin w,
      ((measure.real (well j)) ^ (1 / (2 : ℝ)) * (Cγ * CR)) /
        measure.real (well j) ≤ Mh)
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Sum (Fin u) (Fin r)) ℝ)
    (K : Matrix (Fin nr) (Fin nr) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ) (μB16 Mvertex : ℝ)
    (hWN : W * N = 0)
    (hBJ : (B₀ * N) * J = 1)
    (hWK : (W * W.transpose) * K = 1)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hB₀SR : ∀ i j, B₀ (Sum.inr i) j =
      srNominalMatrix wellRegion β₀ volume i j)
    (hα : ((β₀ / β) - 1) ^ 2 < 1)
    (hμ : 0 < μB16) (hM : 0 < Mvertex) (hμM : μB16 ≤ Mvertex)
    (hB16Vertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ v : Fin r → ℝ,
        μB16 * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveB16SymBlock wellRegion β β₀ volume (N * J) hV).mulVec v) i)
    (hTVertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveB16Action wellRegion β β₀ volume (N * J)
            hV xᵤ xᵣ i) ^ 2) ≤
          Mvertex ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)))
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (Lpsi LpsiRate : ℝ)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hA10 : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt psi (psiRate t) t ∧
        ‖psi t‖ ≤ Lpsi ∧ ‖psiRate t‖ ≤ LpsiRate)
    (FD : V →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → V)
    (LD LDRate : ℝ)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hD : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖DRate t‖ ≤ LDRate)
    (hDDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt D (DRate t) t) :
    let α := β₀ / β
    let κ := ReservoirSeismicityControl.paperPhysicalDemandScale α μB16 Mvertex
    let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin α μB16 Mvertex
    let C := N * J
    let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
      measure well γ₁ Rphysical
    let Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ := fun i j => B₀ (Sum.inl i) j
    let LB := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume
          (fun _ => 0) α 0) +
      ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
        (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) *
          max 0 (γmax * Rmax)
    δ < 1 ∧
      (∀ t,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C t‖ ≤ δ) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖deriv (fun s : ℝ =>
          Ring.inverse
            (positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C s)
            (ReservoirSeismicityControl.paperDemandPsi psi
              (positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ)
              FD D s)) t‖ ≤
          (1 / (1 - δ)) *
            (LpsiRate +
              (ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
                (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh) *
                (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
          (1 / (1 - δ)) *
            ((ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
                (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh *
                  ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C) *
              ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD))))) := by
  classical
  let α := β₀ / β
  let κ := ReservoirSeismicityControl.paperPhysicalDemandScale α μB16 Mvertex
  let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin α μB16 Mvertex
  let C := N * J
  let h := ReservoirSeismicityControl.paperNonnegativeTimeWellSensitivities
    measure well γ₁ Rphysical
  let Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ := fun i j => B₀ (Sum.inl i) j
  let LB := ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (positiveDemandWellMatrix Bᵤ₀ wellRegion β volume
        (fun _ => 0) α 0) +
    ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
      (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) *
        max 0 (γmax * Rmax)
  change δ < 1 ∧
      (∀ t,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
            EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C t‖ ≤ δ) ∧
      (∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        ‖deriv (fun s : ℝ =>
          Ring.inverse
            (positiveDemandGainCLM Bᵤ₀ wellRegion β volume h α κ C s)
            (ReservoirSeismicityControl.paperDemandPsi psi
              (positiveDemandWellCLM Bᵤ₀ wellRegion β volume h α κ)
              FD D s)) t‖ ≤
          (1 / (1 - δ)) *
            (LpsiRate +
              (ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
                (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh) *
                (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
          (1 / (1 - δ)) *
            ((ReservoirSeismicityControl.paperMatrixEuclideanOpNorm
                (positiveDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * Mh *
                  ReservoirSeismicityControl.paperMatrixEuclideanOpNorm C) *
              ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD)))))
  have hB18 := positive_demand_B18_from_actual_sr_integrals
    measure well γ₁ Rphysical γmin γmax Rmax Rmin
    hfinite hpositive hγmin hRmin hγ hR hint
    B₀ W N J K wellRegion β β₀ volume μB16 Mvertex
    hWN hBJ hWK hβ hβ₀ hvol hB₀SR
    hα hμ hM hμM hB16Vertices hTVertices
  have hBounds := A10_controls_three_components
    psi psiRate Lpsi LpsiRate hA10
  rcases hB18 with ⟨hNullspace, hDemand, hδ, hContraction⟩
  have hB19 := positive_demand_B19_from_actual_sr_L2_ae
    measure well hs hfinite hpositive γ₁ Rphysical
    γmin γmax Rmax Rmin hγmin hRmin hγ hR hint
    R_L2 Rdot Kγ Cγ CR Mh hCγ hK hrep hSRDeriv hSRRate hgeometry
    Bᵤ₀ wellRegion β volume α κ C
    psi psiRate FD D DRate
    δ Lpsi LpsiRate LD LDRate
    hδ hLpsi hLpsiRate hLD hLDRate hMh
    hBounds.2.1 hBounds.2.2 hD hDRate hBounds.1 hDDeriv hContraction
  exact ⟨hδ, hContraction, hB19⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_to_actual_A12_A14_certificates
#print axioms ReservoirSeismicityControl.Paper2026.paper_A10_to_actual_B18_B19_certificates
