import ReservoirSeismicityControl.Paper2026.PositiveDemandB16
import Mathlib.Tactic

/-!
# P5 / Appendix B: nominal rank certificates and constrained allocation

The manuscript constructs `C_W = N (B₀ N)⁺` and
`F_D = Wᵀ (W Wᵀ)⁻¹`, where the columns of `N` span the nullspace
of the demand matrix `W`. The full-row-rank tests in Assumption 6
ensure that `(B₀ N)⁺` and `(W Wᵀ)⁻¹` have the required RIGHT inverse
identities. Those finite-dimensional inverse-existence facts are treated
as *explicit certificates* in the precise matrix form used by Appendix B.

This file proves, from those certificates and `W N = 0`, the three
identities `B₀ C_W = I`, `W C_W = 0`, and `W F_D = I`. The final
proposition feeds the constructed `C_W` into the already verified
positive physical B16/B18 result, keeping the vertex tests visible.

This does NOT certify the rank of any particular numerical W, or
formalize the Moore--Penrose existence theorem. No PDE or new
control-stability theorem is being introduced.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped Matrix

/-- The `B₀ C_W = I` identity from the nullspace allocation and its
right-inverse certificate; it is not assumed independently. -/
theorem positive_allocation_nominal_right_inverse
    {m w k : ℕ}
    (B₀ : Matrix (Fin m) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Fin m) ℝ)
    (hBJ : (B₀ * N) * J = 1) :
    B₀ * (N * J) = 1 := by
  calc
    B₀ * (N * J) = (B₀ * N) * J := (Matrix.mul_assoc B₀ N J).symm
    _ = 1 := hBJ

/-- `W C_W = 0` follows from the null-space identity `W N = 0`. -/
theorem positive_allocation_nullspace
    {nr w k m : ℕ}
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Fin m) ℝ)
    (hWN : W * N = 0) :
    W * (N * J) = 0 := by
  calc
    W * (N * J) = (W * N) * J := (Matrix.mul_assoc W N J).symm
    _ = 0 := by rw [hWN]; simp

/-- `W F_D = I` from the explicitly checked Gram inverse, with
`F_D = Wᵀ (W Wᵀ)⁻¹` as in Appendix B. -/
theorem positive_allocation_demand_right_inverse
    {nr w : ℕ}
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (K : Matrix (Fin nr) (Fin nr) ℝ)
    (hWK : (W * W.transpose) * K = 1) :
    W * (W.transpose * K) = 1 := by
  calc
    W * (W.transpose * K) = (W * W.transpose) * K :=
      (Matrix.mul_assoc W W.transpose K).symm
    _ = 1 := hWK

/-- The actual control of equation (25), with arbitrary controller action
`z`, satisfies the demand exactly: `W (C_W z + F_D D) = D`.
This is the manuscript's displayed direct-multiplication step, not an
independent hypothesis about tracking. -/
theorem positive_allocation_exact_demand
    {nr w k m : ℕ}
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Fin m) ℝ)
    (K : Matrix (Fin nr) (Fin nr) ℝ)
    (hWN : W * N = 0)
    (hWK : (W * W.transpose) * K = 1)
    (z : Fin m → ℝ) (d : Fin nr → ℝ) :
    W.mulVec ((N * J).mulVec z + (W.transpose * K).mulVec d) = d := by
  calc
    W.mulVec ((N * J).mulVec z + (W.transpose * K).mulVec d) =
        (W * (N * J)).mulVec z + (W * (W.transpose * K)).mulVec d := by
      rw [Matrix.mulVec_add,
        Matrix.mulVec_mulVec z W (N * J),
        Matrix.mulVec_mulVec d W (W.transpose * K)]
    _ = d := by
      rw [positive_allocation_nullspace W N J hWN,
        positive_allocation_demand_right_inverse W K hWK]
      simp

/-- The physical B16 vertex checks and the two finite-dimensional rank
certificates yield both exact allocation identities and the B18 strict
contraction for the *constructed* `C_W = N J`. In an application,
`J = (B₀ N)⁺`, `K = (W Wᵀ)⁻¹` are verified by standard full-row-rank
linear algebra; the corresponding inverse identities remain visible
here and are not silently postulated for an arbitrary matrix. -/
theorem positive_demand_B16_from_allocation
    {u r w nr k : ℕ}
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (W : Matrix (Fin nr) (Fin w) ℝ)
    (N : Matrix (Fin w) (Fin k) ℝ)
    (J : Matrix (Fin k) (Sum (Fin u) (Fin r)) ℝ)
    (K : Matrix (Fin nr) (Fin nr) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β β₀ : ℝ) (volume : Fin r → ℝ)
    (lo hi : Fin w → ℝ) (h : ℝ → Fin w → ℝ)
    (μ M : ℝ)
    (hWN : W * N = 0)
    (hBJ : (B₀ * N) * J = 1)
    (hWK : (W * W.transpose) * K = 1)
    (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hvol : ∀ i, volume i ≠ 0)
    (hB₀SR : ∀ i j, B₀ (Sum.inr i) j =
      srNominalMatrix wellRegion β₀ volume i j)
    (hα : ((β₀ / β) - 1) ^ 2 < 1)
    (hμ : 0 < μ) (hM : 0 < M) (hμM : μ ≤ M)
    (hlo : ∀ t j, lo j ≤ h t j)
    (hhi : ∀ t j, h t j ≤ hi j)
    (hB16Vertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((positiveB16SymBlock wellRegion β β₀ volume (N * J) hV).mulVec v) i)
    (hTVertices : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (positiveB16Action wellRegion β β₀ volume (N * J)
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    let a := β₀ / β
    let κ := ReservoirSeismicityControl.paperPhysicalDemandScale a μ M
    let δ := ReservoirSeismicityControl.paperPhysicalDemandMargin a μ M
    W * (N * J) = 0 ∧
      W * (W.transpose * K) = 1 ∧
      δ < 1 ∧
      ∀ t : ℝ,
        ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
                EuclideanSpace ℝ (Sum (Fin u) (Fin r))) -
          positiveDemandGainCLM
            (fun i j => B₀ (Sum.inl i) j)
            wellRegion β volume h a κ (N * J) t‖ ≤ δ := by
  have hBC : B₀ * (N * J) = 1 := by
    calc
      B₀ * (N * J) = (B₀ * N) * J := (Matrix.mul_assoc B₀ N J).symm
      _ = 1 := hBJ
  have hWC : W * (N * J) = 0 := by
    calc
      W * (N * J) = (W * N) * J := (Matrix.mul_assoc W N J).symm
      _ = 0 := by rw [hWN]; simp
  have hWF : W * (W.transpose * K) = 1 := by
    calc
      W * (W.transpose * K) = (W * W.transpose) * K :=
        (Matrix.mul_assoc W W.transpose K).symm
      _ = 1 := hWK
  have hContraction := positive_demand_contraction_from_B16_vertices
    B₀ (N * J) wellRegion β β₀ volume lo hi h μ M
    hβ hβ₀ hvol hBC hB₀SR hα hμ hM hμM hlo hhi
    hB16Vertices hTVertices
  exact ⟨hWC, hWF, hContraction.1, hContraction.2⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_nominal_right_inverse
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_nullspace
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_demand_right_inverse
#print axioms ReservoirSeismicityControl.Paper2026.positive_allocation_exact_demand
#print axioms ReservoirSeismicityControl.Paper2026.positive_demand_B16_from_allocation
