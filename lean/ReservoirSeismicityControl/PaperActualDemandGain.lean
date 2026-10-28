import ReservoirSeismicityControl.PaperSensitivityVertexNorm

/-!
# Stage 48: the vertex certificate applies to the physical product B(h) C_W

The manuscript's Assumption A6 gives the single nominal right-inverse identity
`B₀ C_W = I`. Stage 45 identified the physical product with the weighted
non-diagonal block gain but requested its pressure-row identities separately.
We derive both pressure-row identities from `B₀ C_W = I`, then replace the
block gain in Stage 47's inverse certificate by the physical product itself.

The finite sensitivity-box hypotheses are exactly the vertex data already
used in Stages 46--47. No rate derivative of the physical well controls
and no new PDE hypothesis is introduced.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- The pressure-pressure rows of `B₀ C_W = I` are the first identity
required for the actual physical gain identification in Stage 45. -/
theorem paper_nominal_pressure_identity_from_full_right_inverse
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hBC : B₀ * C = 1)
    (i j : Fin u) :
    (∑ k : Fin w, B₀ (Sum.inl i) k * C k (Sum.inl j)) =
      if i = j then 1 else 0 := by
  classical
  have h := congrArg
    (fun A : Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ =>
      A (Sum.inl i) (Sum.inl j)) hBC
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- The pressure-seismicity cross rows vanish under the *same* nominal
right-inverse identity. They are not an additional A6 assumption. -/
theorem paper_nominal_pressure_zero_from_full_right_inverse
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hBC : B₀ * C = 1)
    (i : Fin u) (j : Fin r) :
    (∑ k : Fin w, B₀ (Sum.inl i) k * C k (Sum.inr j)) = 0 := by
  classical
  have h := congrArg
    (fun A : Matrix (Sum (Fin u) (Fin r)) (Sum (Fin u) (Fin r)) ℝ =>
      A (Sum.inl i) (Sum.inr j)) hBC
  simpa [Matrix.mul_apply] using h

/-- The physical, well-level gain `B(h) C_W` agrees with the full block gain
used in Appendix B, with *only* the original identity `B₀ C_W = I`.
The nominal pressure block is the restriction of `B₀` to pressure rows. -/
theorem paper_physical_demand_product_eq_block_of_nominal_right_inverse
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (h : Fin w → ℝ)
    (α κ : ℝ)
    (hBC : B₀ * C = 1) :
    paperPhysicalDemandWellMatrix
        (fun i j => B₀ (Sum.inl i) j) wellRegion β volume h α κ * C =
      paperDemandBlockGainMatrix α κ
        (paperPhysicalSRPressureBlock wellRegion β volume h C)
        (paperPhysicalSRSRBlock wellRegion β volume h C) := by
  exact paper_physical_demand_gain_eq_block
    (fun i j => B₀ (Sum.inl i) j)
    wellRegion β volume h C α κ
    (paper_nominal_pressure_identity_from_full_right_inverse B₀ C hBC)
    (paper_nominal_pressure_zero_from_full_right_inverse B₀ C hBC)

/-- Assumption A6's single nominal right-inverse identity and the finite
vertex conditions imply invertibility and the quantitative inverse bound
for the *actual physical product* `B(h(t)) C_W`.

This is the exact finite-dimensional controller gain from Appendix B, rather
than an abstract block matrix with independently assumed pressure identities.
The estimates on the well sensitivities themselves still come from Appendix A.2.
-/
theorem paper_physical_demand_product_inverse_from_vertices
    {u r w : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hBC : B₀ * C = 1)
    (lo hi : Fin w → ℝ) (h : ℝ → Fin w → ℝ)
    (α μ M : ℝ)
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
    (t : ℝ) (x : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) :
    let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
    let δ : ℝ := Real.sqrt ρ
    let Gphysical : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
         EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
       fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
         (n := Sum (Fin u) (Fin r))
         (paperPhysicalDemandWellMatrix
           (fun i j => B₀ (Sum.inl i) j)
           wellRegion β volume (h s) α κ * C)
    IsUnit (Gphysical t) ∧ ‖Ring.inverse (Gphysical t) x‖ ≤
      (1 / (1 - δ)) * ‖x‖ := by
  classical
  let κ : ℝ := (1 - (α - 1) ^ 2) * μ / (2 * M ^ 2)
  let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
    (1 - (1 - (α - 1) ^ 4) * μ ^ 2 / (4 * M ^ 2))
  let δ : ℝ := Real.sqrt ρ
  let Gphysical : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
       EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (n := Sum (Fin u) (Fin r))
      (paperPhysicalDemandWellMatrix
        (fun i j => B₀ (Sum.inl i) j)
        wellRegion β volume (h s) α κ * C)
  let Gblock : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
       EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (n := Sum (Fin u) (Fin r))
      (paperDemandBlockGainMatrix α κ
        (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
        (paperPhysicalSRSRBlock wellRegion β volume (h s) C))
  have heq (s : ℝ) : Gphysical s = Gblock s := by
    dsimp only [Gphysical, Gblock]
    rw [paper_physical_demand_product_eq_block_of_nominal_right_inverse
      B₀ C wellRegion β volume (h s) α κ hBC]
  have hcert := paper_physical_demand_gain_inverse_from_vertices
    wellRegion β volume C lo hi h α μ M
    hα hμ hM hμM hlo hhi hvertexCoercive hvertexUpper t x
  change IsUnit (Gblock t) ∧
    ‖Ring.inverse (Gblock t) x‖ ≤ (1 / (1 - δ)) * ‖x‖ at hcert
  change IsUnit (Gphysical t) ∧
    ‖Ring.inverse (Gphysical t) x‖ ≤ (1 / (1 - δ)) * ‖x‖
  rw [heq t]
  exact hcert

end ReservoirSeismicityControl
