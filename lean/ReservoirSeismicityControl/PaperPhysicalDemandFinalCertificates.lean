import ReservoirSeismicityControl.PaperPhysicalEuclideanDemandBridge
import ReservoirSeismicityControl.PaperActualDemandGain

/-!
# Stage 56 — Physical demand-gain certificates for Theorem 2

Appendix B's finite vertex hypotheses imply the strict Euclidean contraction
of the *actual* physical allocated gain B(h(t)) C_W.  Combining this with
Stage 55 gives the a.e. normalized-perturbation derivative bound with no
independent gain-contraction or matrix-representation hypotheses.

This is a certificate for the hypotheses of the cited MIMO stability theorem,
not a formal proof of that external theorem or of the full PDE-ODE dynamics.
The hypotheses on regional perturbations and sensitivity derivatives are the
analytic inputs from Appendix A. No bound on Qdot or Qddot is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The explicit scaling used by the weighted demand-controller proof. -/
noncomputable def paperPhysicalDemandScale (α μ M : ℝ) : ℝ :=
  (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)

/-- The explicit contraction margin used in Appendix B. -/
noncomputable def paperPhysicalDemandMargin (α μ M : ℝ) : ℝ :=
  Real.sqrt (max (1 - (1 - (α - 1) ^ 2) / 4)
    (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2)))

/-- The finite vertex conditions of Appendix B prove strict contraction for
`B(h(t)) C_W` itself, with the exact Euclidean CLM from Stage 55.
The pressure-row identities are consequences of `B₀ * C = I`. -/
theorem paper_physical_demand_contraction_from_vertices
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (lo hi : Fin w → ℝ) (h : ℝ → Fin w → ℝ)
    (α μ M : ℝ)
    (hBC : B₀ * C = 1)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hlo : ∀ t j, lo j ≤ h t j)
    (hhi : ∀ t j, h t j ≤ hi j)
    (hvertexCoercive : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    let κ := paperPhysicalDemandScale α μ M
    let δ := paperPhysicalDemandMargin α μ M
    δ < 1 ∧
      ∀ t : ℝ,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          paperPhysicalGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h α κ C t‖ ≤ δ := by
  classical
  let κ := paperPhysicalDemandScale α μ M
  let δ := paperPhysicalDemandMargin α μ M
  have hcoercive (s : ℝ) (v : Fin r → ℝ) :
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        ∑ i : Fin r, v i *
          ((paperPhysicalSRSRBlock wellRegion β volume (h s) C).mulVec v) i :=
    paper_physical_sr_vertex_coercivity wellRegion β volume C
      lo hi (h s) μ (hlo s) (hhi s) hvertexCoercive v
  have hfull (s : ℝ) (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) :
      (∑ i : Fin r,
         (((paperPhysicalSRPressureBlock wellRegion β volume (h s) C).mulVec xᵤ) i +
           ((paperPhysicalSRSRBlock wellRegion β volume (h s) C).mulVec xᵣ) i) ^ 2) ≤
      M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
        (∑ i : Fin r, (xᵣ i) ^ 2)) := by
    exact paper_physical_sr_vertex_full_action_bound
      wellRegion β volume C lo hi (h s) M
      (hlo s) (hhi s) hvertexUpper xᵤ xᵣ
  have hpress (s : ℝ) (xᵤ : Fin u → ℝ) :
      (∑ i : Fin r,
         (((paperPhysicalSRPressureBlock wellRegion β volume (h s) C).mulVec xᵤ) i) ^ 2) ≤
      M ^ 2 * (∑ j : Fin u, (xᵤ j) ^ 2) :=
    paper_physical_sr_vertex_pressure_bound
      wellRegion β volume C lo hi (h s) M
      (hlo s) (hhi s) hvertexUpper xᵤ
  have hblock (s : ℝ) :
      δ < 1 ∧
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          Matrix.toEuclideanCLM (𝕜 := ℝ)
            (n := Sum (Fin u) (Fin r))
            (paperDemandBlockGainMatrix α κ
              (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
              (paperPhysicalSRSRBlock wellRegion β volume (h s) C))‖ ≤ δ := by
    have hc := paper_demand_block_opNorm_contraction
      (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
      (paperPhysicalSRSRBlock wellRegion β volume (h s) C)
      α μ M hα hμ hM hμM (hcoercive s) (hfull s) (hpress s)
    change δ < 1 ∧
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
         EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (n := Sum (Fin u) (Fin r))
          (paperDemandBlockGainMatrix α κ
            (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
            (paperPhysicalSRSRBlock wellRegion β volume (h s) C))‖ ≤ δ at hc
    exact hc
  have heq (s : ℝ) :
      paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume h α κ C s =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (n := Sum (Fin u) (Fin r))
        (paperDemandBlockGainMatrix α κ
          (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
          (paperPhysicalSRSRBlock wellRegion β volume (h s) C)) := by
    change paperMatrixToEuclideanCLM
      (paperPhysicalDemandWellMatrix (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume (h s) α κ * C) = _
    rw [paper_physical_demand_product_eq_block_of_nominal_right_inverse
      B₀ C wellRegion β volume (h s) α κ hBC]
    rfl
  change δ < 1 ∧ ∀ t,
    ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
        EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
      paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume h α κ C t‖ ≤ δ
  refine ⟨(hblock 0).1, ?_⟩
  intro t
  rw [heq t]
  exact (hblock t).2

/-- Appendix B conclusion for the actual physical gain and its normalized
perturbation. Neither contraction nor a representation derivative appears
as a separate hypothesis. The PDE-origin a.e. bounds remain explicit. -/
theorem paper_physical_theorem2_certificates_from_vertices_ae
    {u r w : ℕ} {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (lo hi : Fin w → ℝ) (h hRate : ℝ → Fin w → ℝ)
    (α μ M : ℝ)
    (psi psiRate : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)))
    (FD : R →L[ℝ] EuclideanSpace ℝ (Fin w))
    (D DRate : ℝ → R)
    (LB Lpsi LpsiRate LD LDRate Mh : ℝ)
    (hBC : B₀ * C = 1)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hlo : ∀ t j, lo j ≤ h t j)
    (hhi : ∀ t j, h t j ≤ hi j)
    (hvertexCoercive : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)))
    (hLB : 0 ≤ LB)
    (hLpsi : 0 ≤ Lpsi) (hLpsiRate : 0 ≤ LpsiRate)
    (hLD : 0 ≤ LD) (hLDRate : 0 ≤ LDRate) (hMh : 0 ≤ Mh)
    (hwellDeriv : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hwellRate : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       |hRate t j| ≤ Mh)
    (hpsi : ∀ᵐ t ∂paperPositiveTime, ‖psi t‖ ≤ Lpsi)
    (hpsiRate : ∀ᵐ t ∂paperPositiveTime, ‖psiRate t‖ ≤ LpsiRate)
    (hB : ∀ᵐ t ∂paperPositiveTime,
       ‖paperPhysicalWellCLM
         (fun i j => B₀ (Sum.inl i) j) wellRegion β volume h α
         (paperPhysicalDemandScale α μ M) t‖ ≤ LB)
    (hD : ∀ᵐ t ∂paperPositiveTime, ‖D t‖ ≤ LD)
    (hDRate : ∀ᵐ t ∂paperPositiveTime, ‖DRate t‖ ≤ LDRate)
    (hpsiDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt psi (psiRate t) t)
    (hDDeriv : ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt D (DRate t) t) :
    let κ := paperPhysicalDemandScale α μ M
    let δ := paperPhysicalDemandMargin α μ M
    δ < 1 ∧
      (∀ t, ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
             EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          paperPhysicalGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h α κ C t‖ ≤ δ) ∧
      (∀ᵐ t ∂paperPositiveTime,
        ‖deriv (fun s : ℝ =>
          Ring.inverse (paperPhysicalGainCLM
              (fun i j => B₀ (Sum.inl i) j)
              wellRegion β volume h α κ C s)
            (paperDemandPsi psi
              (paperPhysicalWellCLM
                (fun i j => B₀ (Sum.inl i) j)
                wellRegion β volume h α κ)
              FD D s)) t‖ ≤
          (1 / (1 - δ)) *
            (LpsiRate +
              (paperMatrixEuclideanOpNorm
                (paperPhysicalDemandRateGeometry
                  (fun i j => B₀ (Sum.inl i) j)
                  wellRegion β volume κ) * Mh) *
                  (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
          (1 / (1 - δ)) *
            ((paperMatrixEuclideanOpNorm
                (paperPhysicalDemandRateGeometry
                  (fun i j => B₀ (Sum.inl i) j)
                  wellRegion β volume κ) * Mh *
                paperMatrixEuclideanOpNorm C) *
              ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD))))) := by
  let κ := paperPhysicalDemandScale α μ M
  let δ := paperPhysicalDemandMargin α μ M
  have hcert := paper_physical_demand_contraction_from_vertices
    B₀ C wellRegion β volume lo hi h α μ M
    hBC hα hμ hM hμM hlo hhi hvertexCoercive hvertexUpper
  change δ < 1 ∧
    (∀ t, ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
      paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume h α κ C t‖ ≤ δ) at hcert
  have hrate := paper_physical_normalized_demand_rate_no_representation_assumptions_ae
    (fun i j => B₀ (Sum.inl i) j)
    wellRegion β volume h hRate α κ C psi psiRate FD D DRate
    δ LB Lpsi LpsiRate LD LDRate Mh
    hcert.1 hLB hLpsi hLpsiRate hLD hLDRate hMh
    hwellDeriv hwellRate hpsi hpsiRate hB hD hDRate
    hpsiDeriv hDDeriv hcert.2
  change δ < 1 ∧
    (∀ t, ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
      paperPhysicalGainCLM (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume h α κ C t‖ ≤ δ) ∧
    (∀ᵐ t ∂paperPositiveTime,
      ‖deriv (fun s : ℝ =>
        Ring.inverse (paperPhysicalGainCLM
          (fun i j => B₀ (Sum.inl i) j)
          wellRegion β volume h α κ C s)
        (paperDemandPsi psi
          (paperPhysicalWellCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h α κ)
          FD D s)) t‖ ≤
        (1 / (1 - δ)) *
          (LpsiRate +
            (paperMatrixEuclideanOpNorm
              (paperPhysicalDemandRateGeometry
                (fun i j => B₀ (Sum.inl i) j)
                wellRegion β volume κ) * Mh) *
                  (‖FD‖ * LD) + LB * (‖FD‖ * LDRate)) +
        (1 / (1 - δ)) *
          ((paperMatrixEuclideanOpNorm
             (paperPhysicalDemandRateGeometry
               (fun i j => B₀ (Sum.inl i) j)
               wellRegion β volume κ) * Mh *
              paperMatrixEuclideanOpNorm C) *
            ((1 / (1 - δ)) * (Lpsi + LB * (‖FD‖ * LD)))))
  exact ⟨hcert.1, hcert.2, hrate⟩

end ReservoirSeismicityControl
