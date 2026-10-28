import ReservoirSeismicityControl.Paper2026.PhysicalA12FullGainBound
import ReservoirSeismicityControl.PaperGainContraction

/-!
# P4: the full physical inverse bound following (A12)

The previous, locally verified (A12) theorem proves the strict induced
Euclidean operator-norm margin for the actual spatial-integral gain.
Apply the existing Neumann-series inverse theorem directly to that gain.
No new inverse proof, rank premise, gain-contraction premise, or PDE assumption
is introduced. This is pointwise in time, as is the imported A3 certificate.

Still open: the physical a.e. gain derivative in (A14), and the P3 near/far
applicability obligations. The complete Theorems 1 and 2 remain open.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped Matrix

/-- The full pressure/SR gain obtained from the *physical* spatial well
integrals is invertible, with the exact inverse-action bound from (A12).
The contraction is derived from A3/A.2 spatial bounds and A4 geometry by
the previously verified theorem, not assumed separately. -/
theorem paper_A12_full_physical_inverse_from_A3
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (assignment : Fin w → Option (Sum (Fin u) (Fin r)))
    (β β₀ : ℝ) (volume : Sum (Fin u) (Fin r) → ℝ)
    (γmin γmax Rlower Rmax : ℝ) (t : ℝ)
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hβupper : β₀ < 2 * β)
    (hγmin : 0 < γmin) (hRlower : 0 < Rlower)
    (hγorder : γmin ≤ γmax) (hRorder : Rlower ≤ Rmax)
    (hvolume : ∀ k, 0 < volume k)
    (hcovered : ∀ k : Sum (Fin u) (Fin r),
      ∃ j : Fin w, assignment j = some k)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
      Rlower ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ j, IntegrableOn (fun x => γ₁ x * R t x) (well j) μ)
    (x : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) :
    let lo := γmin * Rlower
    let hi := γmax * Rmax
    let normalization := (β₀ / β) * ((lo + hi) / 2)
    let B := paperA12FullPhysicalMatrix μ well γ₁ R assignment
      β normalization volume t
    let B₀ := paperA12FullNominalMatrix assignment β₀ volume
    let G := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
      (B * paperA12FullNominalRightInverse B₀)
    let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
    IsUnit G ∧ ‖Ring.inverse G x‖ ≤ (1 / (1 - δB)) * ‖x‖ := by
  classical
  let lo := γmin * Rlower
  let hi := γmax * Rmax
  let normalization := (β₀ / β) * ((lo + hi) / 2)
  let B := paperA12FullPhysicalMatrix μ well γ₁ R assignment
    β normalization volume t
  let B₀ := paperA12FullNominalMatrix assignment β₀ volume
  let G : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Sum (Fin u) (Fin r))
      (B * paperA12FullNominalRightInverse B₀)
  let δB := max |β₀ / β - 1| ((hi - lo) / (lo + hi))
  change IsUnit G ∧ ‖Ring.inverse G x‖ ≤ (1 / (1 - δB)) * ‖x‖
  have hA12 := paper_A12_full_physical_opNorm_from_A3
    μ well γ₁ R assignment β β₀ volume γmin γmax Rlower Rmax t
    hβ hβ₀ hβupper hγmin hRlower hγorder hRorder
    hvolume hcovered hfinite hpositive hγ hR hint
  have hδ : δB < 1 := hA12.2.1
  have hclose :
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) - G‖ ≤ δB :=
    hA12.2.2
  let gain : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin u) (Fin r)) := fun _ => G
  have hcloseAll : ∀ s : ℝ,
      ‖(1 : EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
          EuclideanSpace ℝ (Sum (Fin u) (Fin r))) - gain s‖ ≤ δB := by
    intro s
    exact hclose
  constructor
  · exact ReservoirSeismicityControl.paper_gain_isUnit_of_contraction
      gain δB hδ hcloseAll t
  · exact ReservoirSeismicityControl.paper_gain_ringInverse_action_bound_of_contraction
      gain δB hδ hcloseAll t x

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A12_full_physical_inverse_from_A3
