import ReservoirSeismicityControl.PressurePositiveSemigroupBochnerL1

/-!
# A5: Bochner convergence for finitely many well profiles

This applies the previously compiled, one-well Bochner L1 estimate to
finitely many wells. In particular, the wells may use different scalar
L1 approximations. No temporal derivative is assumed.

The underlying measure and time map are deliberately arbitrary: the physical
mild solution uses Lebesgue measure restricted to the observation interval
and the backward-time map s ↦ max(t-s, 0).
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped BigOperators

section MultiwellBochner

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [MeasurableSpace α]

/-- The Bochner forcing term for finitely many wells. -/
noncomputable def pressureMultiwellBochnerForcing
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure α) (τ : α → NNReal) (m : ℕ)
    (f : Fin m → H) (q : Fin m → α → ℝ) : H :=
  ∑ j : Fin m, pressureBochnerForcing S μ τ (f j) (q j)

/-- If every scalar rate converges in L1, the entire finite-well Bochner
forcing converges strongly in H. -/
theorem pressure_multiwell_bochner_tendsto_of_l1
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (μ : Measure α) (τ : α → NNReal) (m : ℕ)
    (f : Fin m → H) (q : ℕ → Fin m → α → ℝ)
    (r : Fin m → α → ℝ)
    (hq : ∀ k j, Integrable (q k j) μ)
    (hr : ∀ j, Integrable (r j) μ)
    (hqv : ∀ k j, Integrable (fun s => q k j s • S (τ s) (f j)) μ)
    (hrv : ∀ j, Integrable (fun s => r j s • S (τ s) (f j)) μ)
    (hL1 : ∀ j, Tendsto
      (fun k => ∫ s, |q k j s - r j s| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => pressureMultiwellBochnerForcing S μ τ m f (q k))
      atTop (𝓝 (pressureMultiwellBochnerForcing S μ τ m f r)) := by
  unfold pressureMultiwellBochnerForcing
  apply tendsto_finsetSum (Finset.univ : Finset (Fin m))
  intro j hj
  exact pressure_bochner_forcing_tendsto_of_l1 S μ τ (f j)
    (fun k => q k j) (r j)
    (fun k => hq k j) (hr j)
    (fun k => hqv k j) (hrv j) (hL1 j)

end MultiwellBochner

end ReservoirSeismicityControl
