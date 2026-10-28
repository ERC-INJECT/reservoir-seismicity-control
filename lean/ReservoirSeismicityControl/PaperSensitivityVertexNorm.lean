import ReservoirSeismicityControl.PaperSensitivityVertices
import ReservoirSeismicityControl.PaperDemandBlockGainBridge

/-!
# Stage 47: physical sensitivity-box vertex upper certificate

The physical SR block action is affine in the well sensitivities. Its squared
Euclidean norm is convex along every affine interpolation in the sensitivity
box. We therefore derive the uniform full-block bound required in Stage 44
from finitely many upper vertex certificates. Taking a zero SR input gives
the pressure-block estimate, so no second vertex bound is required.

The final theorem combines this estimate with Stage 46's vertex coercivity
certificate and Stage 44's inverse gain result for the demand controller.
No rate-derivative assumption on the well controls is used.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- Convexity of the square along a real interval. -/
theorem paper_convex_square (a b θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (θ * a + (1 - θ) * b) ^ 2 ≤ θ * a ^ 2 + (1 - θ) * b ^ 2 := by
  have hpos : 0 ≤ θ * (1 - θ) * (a - b) ^ 2 :=
    mul_nonneg (mul_nonneg hθ0 (sub_nonneg.mpr hθ1)) (sq_nonneg _)
  have hid :
      θ * a ^ 2 + (1 - θ) * b ^ 2 -
        (θ * a + (1 - θ) * b) ^ 2 =
          θ * (1 - θ) * (a - b) ^ 2 := by ring
  linarith

/-- A squared Euclidean action that is affine in the sensitivity vector
is convex in that vector. An upper certificate at each box vertex therefore
holds everywhere inside the box, including degenerate coordinate intervals. -/
theorem paper_affine_squared_action_vertex_upper
    {w r : ℕ} (lo hi h : Fin w → ℝ)
    (f : (Fin w → ℝ) → Fin r → ℝ) (bound : ℝ)
    (hlo : ∀ j, lo j ≤ h j) (hhi : ∀ j, h j ≤ hi j)
    (haff : ∀ x y θ i,
      f (fun j => θ * x j + (1 - θ) * y j) i =
        θ * f x i + (1 - θ) * f y i)
    (hvertex : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
        (∑ i : Fin r, (f hV i) ^ 2) ≤ bound) :
    (∑ i : Fin r, (f h i) ^ 2) ≤ bound := by
  classical
  apply paper_box_vertex_propagation lo hi h
    (fun z => (∑ i : Fin r, (f z i) ^ 2) ≤ bound)
    hlo hhi hvertex
  intro x y θ hθ0 hθ1 hx hy
  have hsq (i : Fin r) :
      (f (fun j => θ * x j + (1 - θ) * y j) i) ^ 2 ≤
        θ * (f x i) ^ 2 + (1 - θ) * (f y i) ^ 2 := by
    rw [haff x y θ i]
    exact paper_convex_square (f x i) (f y i) θ hθ0 hθ1
  calc
    (∑ i : Fin r,
        (f (fun j => θ * x j + (1 - θ) * y j) i) ^ 2) ≤
      ∑ i : Fin r, (θ * (f x i) ^ 2 + (1 - θ) * (f y i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact hsq i
    _ = θ * (∑ i : Fin r, (f x i) ^ 2) +
        (1 - θ) * (∑ i : Fin r, (f y i) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ θ * bound + (1 - θ) * bound := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hx hθ0
          · exact mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hθ1)
    _ = bound := by ring

/-- The physical SR-to-pressure allocation block is affine in the well
sensitivity vector, just like the SR-to-SR block verified in Stage 46. -/
theorem paper_physical_sr_pressure_block_affine
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h₀ h₁ : Fin w → ℝ) (θ : ℝ) :
    paperPhysicalSRPressureBlock wellRegion β volume
      (fun j => θ * h₀ j + (1 - θ) * h₁ j) C =
      θ • paperPhysicalSRPressureBlock wellRegion β volume h₀ C +
        (1 - θ) • paperPhysicalSRPressureBlock wellRegion β volume h₁ C := by
  classical
  ext i j
  simp only [paperPhysicalSRPressureBlock, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hmatrix := paper_physical_sr_well_affine
    wellRegion β volume h₀ h₁ θ
  have hentry (k : Fin w) :
      paperPhysicalSRWellMatrix wellRegion β volume
          (fun j => θ * h₀ j + (1 - θ) * h₁ j) i k =
        θ * paperPhysicalSRWellMatrix wellRegion β volume h₀ i k +
          (1 - θ) * paperPhysicalSRWellMatrix wellRegion β volume h₁ i k := by
    have he := congrArg (fun A : Matrix (Fin r) (Fin w) ℝ => A i k) hmatrix
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using he
  calc
    (∑ k : Fin w, paperPhysicalSRWellMatrix wellRegion β volume
          (fun j => θ * h₀ j + (1 - θ) * h₁ j) i k * C k (Sum.inl j)) =
      ∑ k : Fin w,
        (θ * paperPhysicalSRWellMatrix wellRegion β volume h₀ i k +
         (1 - θ) * paperPhysicalSRWellMatrix wellRegion β volume h₁ i k) *
          C k (Sum.inl j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hentry]
    _ = θ * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h₀ i k *
            C k (Sum.inl j)) +
        (1 - θ) * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h₁ i k *
            C k (Sum.inl j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- Matrix application preserves the stated affine interpolation. -/
theorem paper_matrix_affine_mulVec
    {a b : ℕ} (A₀ A₁ : Matrix (Fin a) (Fin b) ℝ)
    (θ : ℝ) (x : Fin b → ℝ) (i : Fin a) :
    ((θ • A₀ + (1 - θ) • A₁).mulVec x) i =
      θ * (A₀.mulVec x) i + (1 - θ) * (A₁.mulVec x) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ j : Fin b, (θ * A₀ i j + (1 - θ) * A₁ i j) * x j) =
      ∑ j : Fin b, (θ * (A₀ i j * x j) +
        (1 - θ) * (A₁ i j * x j)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = θ * (∑ j : Fin b, A₀ i j * x j) +
        (1 - θ) * (∑ j : Fin b, A₁ i j * x j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Full, unscaled SR row action on the pressure and SR output vectors.
The pressure-to-SR and SR-to-SR coupling are both retained. -/
noncomputable def paperPhysicalSRCombinedAction
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h : Fin w → ℝ) (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ) :
    Fin r → ℝ :=
  fun i =>
    ((paperPhysicalSRPressureBlock wellRegion β volume h C).mulVec xᵤ) i +
      ((paperPhysicalSRSRBlock wellRegion β volume h C).mulVec xᵣ) i

/-- The exact physical *combined* SR row action is affine in h. -/
theorem paper_physical_sr_combined_action_affine
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ)
    (h₀ h₁ : Fin w → ℝ) (θ : ℝ) (i : Fin r) :
    paperPhysicalSRCombinedAction wellRegion β volume C
       (fun j => θ * h₀ j + (1 - θ) * h₁ j) xᵤ xᵣ i =
      θ * paperPhysicalSRCombinedAction wellRegion β volume C h₀ xᵤ xᵣ i +
        (1 - θ) * paperPhysicalSRCombinedAction wellRegion β volume C
          h₁ xᵤ xᵣ i := by
  have hP := paper_physical_sr_pressure_block_affine
    wellRegion β volume C h₀ h₁ θ
  have hQ := paper_physical_sr_sr_block_affine
    wellRegion β volume C h₀ h₁ θ
  have hp := paper_matrix_affine_mulVec
    (paperPhysicalSRPressureBlock wellRegion β volume h₀ C)
    (paperPhysicalSRPressureBlock wellRegion β volume h₁ C) θ xᵤ i
  have hq := paper_matrix_affine_mulVec
    (paperPhysicalSRSRBlock wellRegion β volume h₀ C)
    (paperPhysicalSRSRBlock wellRegion β volume h₁ C) θ xᵣ i
  dsimp only [paperPhysicalSRCombinedAction]
  rw [hP, hQ, hp, hq]
  ring

/-- The *one* finite upper vertex certificate bounds the entire physical
SR row operator at all admissible sensitivity vectors. This is exactly the
`hfull` hypothesis of Stage 44. -/
theorem paper_physical_sr_vertex_full_action_bound
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (lo hi h : Fin w → ℝ) (M : ℝ)
    (hlo : ∀ j, lo j ≤ h j)
    (hhi : ∀ j, h j ≤ hi j)
    (hvertex : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
      (∑ i : Fin r,
        (paperPhysicalSRCombinedAction wellRegion β volume C
          h xᵤ xᵣ i) ^ 2) ≤
        M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
          (∑ i : Fin r, (xᵣ i) ^ 2)) := by
  intro xᵤ xᵣ
  apply paper_affine_squared_action_vertex_upper lo hi h
    (fun h' => paperPhysicalSRCombinedAction wellRegion β volume C h' xᵤ xᵣ)
    (M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
      (∑ i : Fin r, (xᵣ i) ^ 2))) hlo hhi
  · intro x y θ i
    exact paper_physical_sr_combined_action_affine
      wellRegion β volume C xᵤ xᵣ x y θ i
  · intro hV hv
    exact hvertex hV hv xᵤ xᵣ

/-- Stage 44's pressure-only upper estimate follows from the full SR row
vertex certificate by setting the SR input to zero. -/
theorem paper_physical_sr_vertex_pressure_bound
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (lo hi h : Fin w → ℝ) (M : ℝ)
    (hlo : ∀ j, lo j ≤ h j)
    (hhi : ∀ j, h j ≤ hi j)
    (hvertex : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2))) :
    ∀ xᵤ : Fin u → ℝ,
      (∑ i : Fin r,
        (((paperPhysicalSRPressureBlock wellRegion β volume h C).mulVec xᵤ) i) ^ 2)
        ≤ M ^ 2 * (∑ j : Fin u, (xᵤ j) ^ 2) := by
  intro xᵤ
  have hz := paper_physical_sr_vertex_full_action_bound
    wellRegion β volume C lo hi h M hlo hhi hvertex
    xᵤ (fun _ : Fin r => 0)
  simpa [paperPhysicalSRCombinedAction, Matrix.mulVec, dotProduct] using hz

/-- Direct Appendix B certificate for the *actual time-varying physical
sensitivity matrices*: finite vertex coercivity from Stage 46, and one
finite vertex upper bound from this stage, supply every matrix hypothesis of
Stage 44. The positive constants and the finite checks are precisely the
A6 data; no new physical bound is postulated. -/
theorem paper_physical_demand_gain_inverse_from_vertices
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
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
    let G : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
         EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
       fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
         (n := Sum (Fin u) (Fin r))
         (paperDemandBlockGainMatrix α κ
           (paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
           (paperPhysicalSRSRBlock wellRegion β volume (h s) C))
    IsUnit (G t) ∧ ‖Ring.inverse (G t) x‖ ≤
      (1 / (1 - δ)) * ‖x‖ := by
  classical
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
  exact paper_actual_demand_gain_inverse_certificate
    (fun s => paperPhysicalSRPressureBlock wellRegion β volume (h s) C)
    (fun s => paperPhysicalSRSRBlock wellRegion β volume (h s) C)
    α μ M hα hμ hM hμM hcoercive hfull hpress t x

end ReservoirSeismicityControl
