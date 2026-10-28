import ReservoirSeismicityControl.PressurePositiveSemigroupPartitions
import ReservoirSeismicityControl.PressurePhysicalNeumannGeneratorSelfAdjoint

/-!
# Step bound for the physical semigroup interface

This module specializes the abstract finite-partition result to the
`StronglyContinuousContractionSemigroup` interface already used in the
physical Neumann development.

`hSelf` (self-adjointness of every semigroup operator) is still an
EXPLICIT premise. The physical files currently establish self-adjointness
of the infinitesimal generator; converting that result into `hSelf`
is a separate outstanding proof step.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace BigOperators

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A direct wrapper around the verified semigroup interface.
This theorem does NOT derive `hSelf` from generator self-adjointness. -/
theorem pressure_C0_semigroup_partition_weighted_bound
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ t : NNReal, IsSelfAdjoint (S t))
    (n : ℕ) (τ step : ℕ → NNReal)
    (hτ0 : τ 0 = 0)
    (hStep : ∀ i < n, τ (i + 1) = τ i + step i)
    (q : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i < n, |q i| ≤ M)
    (f : H) :
    ‖∑ i ∈ Finset.range n,
        q i • (S (τ i) - S (τ (i + 1))) f‖ ≤ M * ‖f‖ := by
  exact pressure_semigroup_partition_weighted_bound
    (fun t => S t) (fun s t => S.add s t)
    hSelf (fun t x => S.norm_apply_le t x)
    S.zero n τ step hτ0 hStep q M hM hq f

end ReservoirSeismicityControl
