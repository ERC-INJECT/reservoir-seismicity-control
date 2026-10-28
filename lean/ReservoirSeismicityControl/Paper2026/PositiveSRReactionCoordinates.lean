import ReservoirSeismicityControl.Paper2026.PositiveDemandP3A3Reaction
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (14): canonical SR output-coordinate injection

The manuscript places each signed, normalized regional SR reaction integral
in its own SR output slot and zero in all pressure slots. The accepted
physical SR reaction -> B19 theorem allowed arbitrary continuous linear
injections. This module fixes those injections to the literal coordinates
of (14), using Mathlib's standard Euclidean basis vectors.

This proves only the finite-dimensional output identification; it neither
assumes nor proves the still-open strong L² product rule or near/far PDE
estimates. The sign s occurs inside the physical regional reaction itself.
-/

namespace ReservoirSeismicityControl.Paper2026

open scoped BigOperators

/-- The *specific* injection for SR region i in Eq. (14).
It maps a scalar to the corresponding SR coordinate (and no pressure slot). -/
noncomputable def paperSRCoordinateEmbed {u r : ℕ} (i : Fin r) :
    ℝ →L[ℝ] EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (EuclideanSpace.single (Sum.inr i) (1 : ℝ))

/-- The injection really is the standard Euclidean coordinate injection. -/
theorem paper_sr_coordinate_embed_apply {u r : ℕ} (i : Fin r) (a : ℝ) :
    paperSRCoordinateEmbed (u := u) i a =
      EuclideanSpace.single (Sum.inr i) a := by
  classical
  change a • EuclideanSpace.single (Sum.inr i) (1 : ℝ) =
    EuclideanSpace.single (Sum.inr i) a
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
  split_ifs <;> simp

/-- Eq. (14): SR reaction contributions have no pressure coordinates. -/
theorem paper_sr_coordinate_pressure_zero {u r : ℕ}
    (v : Fin r → ℝ) (j : Fin u) :
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) i (v i)).ofLp
      (Sum.inl j) = 0 := by
  classical
  change (EuclideanSpace.proj (Sum.inl j))
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) i (v i)) = 0
  rw [map_sum]
  simp [paper_sr_coordinate_embed_apply, EuclideanSpace.single_apply]

/-- Eq. (14): SR output j is precisely its own normalized regional term. -/
theorem paper_sr_coordinate_sr_entry {u r : ℕ}
    (v : Fin r → ℝ) (j : Fin r) :
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) i (v i)).ofLp
      (Sum.inr j) = v j := by
  classical
  change (EuclideanSpace.proj (Sum.inr j))
    (∑ i : Fin r, paperSRCoordinateEmbed (u := u) i (v i)) = v j
  rw [map_sum]
  simp [paper_sr_coordinate_embed_apply, EuclideanSpace.single_apply]

/-- The actual Eq. (14) reaction vector is exactly the canonical sum. -/
theorem physical_sr_reaction_canonical_eq
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (μ : MeasureTheory.Measure X) (regions : Fin r → Set X)
    (gamma2 R : ℝ → X → ℝ) (Rstar : X → ℝ)
    (sign gamma10 R0star t : ℝ) :
    physicalSRFiniteReactionPsi μ regions gamma2 R Rstar
      sign gamma10 R0star (paperSRCoordinateEmbed (u := u)) t =
    ∑ i : Fin r, EuclideanSpace.single (Sum.inr i)
      (physicalSRRegionalReaction μ (regions i) gamma2 R Rstar
        sign gamma10 R0star t) := by
  classical
  simp only [physicalSRFiniteReactionPsi, paper_sr_coordinate_embed_apply]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_embed_apply
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_pressure_zero
#print axioms ReservoirSeismicityControl.Paper2026.paper_sr_coordinate_sr_entry
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_canonical_eq
