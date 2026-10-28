import ReservoirSeismicityControl.PressurePositiveSemigroupBochnerMultiwell
import ReservoirSeismicityControl.PressurePositiveSemigroupA5StepLimit

/-!
# A5: the multiwell Bochner-to-generator bridge

The finite-step A5 estimate and the dual/Riesz strong-limit argument have
already been checked. This theorem uses the separately checked Bochner L1
stability estimate to *derive*, rather than assume, convergence of the
approximate pressures.

Two obligations are EXPLICIT hypotheses here, not proven in this module:
* constructing bounded interval-step approximants to bounded measurable rates;
* identifying each finite-step orbit-integral sum with the appropriate
  Bochner integral of its piecewise-constant rate.

The physical 3D identification remains another separate obligation.
No assumption on a time derivative or a spectral eigenbasis is introduced.
-/

namespace ReservoirSeismicityControl

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

section MultiwellBridge

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [MeasurableSpace α]

/-- The A5 bound for the *actual Bochner forcing*, provided a bounded
finite-step approximation has been constructed and identified with its
Bochner integral. Convergence of the pressure is proved from L1 convergence
of the scalar rates; it is NOT an extra hypothesis. -/
theorem pressure_multiwell_A5_of_bochner_step_approximation
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : H,
      (∀ v : H, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (n : ℕ → Fin m → ℕ)
    (τ h : ℕ → Fin m → ℕ → NNReal)
    (hτ0 : ∀ k j, τ k j 0 = 0)
    (hStep : ∀ k j i, i < n k j →
      τ k j (i + 1) = τ k j i + h k j i)
    (qStep : ℕ → Fin m → ℕ → ℝ)
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hqStep : ∀ k j i, i < n k j → |qStep k j i| ≤ M j)
    (f : Fin m → H)
    (μ : Measure α) (backwardTime : α → NNReal)
    (q : ℕ → Fin m → α → ℝ) (r : Fin m → α → ℝ)
    (hq : ∀ k j, Integrable (q k j) μ)
    (hr : ∀ j, Integrable (r j) μ)
    (hqv : ∀ k j,
      Integrable (fun s => q k j s • S (backwardTime s) (f j)) μ)
    (hrv : ∀ j,
      Integrable (fun s => r j s • S (backwardTime s) (f j)) μ)
    (hL1 : ∀ j, Tendsto
      (fun k => ∫ s, |q k j s - r j s| ∂μ) atTop (𝓝 0))
    (hIdentify : ∀ k,
      (pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k)
        (qStep k) f : H) =
      pressureMultiwellBochnerForcing S μ backwardTime m f (q k)) :
    ∃ hp : (S t (p₀ : H) +
        pressureMultiwellBochnerForcing S μ backwardTime m f r) ∈
          S.generatorDomain,
      ‖S.generator ⟨S t (p₀ : H) +
          pressureMultiwellBochnerForcing S μ backwardTime m f r, hp⟩‖ ≤
        ‖S.generator p₀‖ + ∑ j : Fin m, M j * ‖f j‖ := by
  have hBochner :
      Tendsto (fun k =>
        pressureMultiwellBochnerForcing S μ backwardTime m f (q k))
        atTop (𝓝 (pressureMultiwellBochnerForcing S μ backwardTime m f r)) :=
    pressure_multiwell_bochner_tendsto_of_l1 S μ backwardTime m f q r
      hq hr hqv hrv hL1
  have hPressure : Tendsto
      (fun k => S t (p₀ : H) +
        pressureMultiwellBochnerForcing S μ backwardTime m f (q k))
      atTop (𝓝 (S t (p₀ : H) +
        pressureMultiwellBochnerForcing S μ backwardTime m f r)) :=
    tendsto_const_nhds.add hBochner
  have hAsSum (k : ℕ) :
      ((⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
        pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k)
          (qStep k) f : S.generatorDomain) : H) =
      S t (p₀ : H) +
        pressureMultiwellBochnerForcing S μ backwardTime m f (q k) := by
    change S t (p₀ : H) +
      (pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k)
        (qStep k) f : H) = _
    rw [hIdentify k]
  have hLimit : Tendsto
      (fun k : ℕ =>
        ((⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
          pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k)
            (qStep k) f : S.generatorDomain) : H))
      atTop (𝓝 (S t (p₀ : H) +
        pressureMultiwellBochnerForcing S μ backwardTime m f r)) := by
    have hEqFun :
        (fun k : ℕ =>
          ((⟨S t (p₀ : H), S.operator_mem_generatorDomain p₀ t⟩ +
            pressureMultiwellStepDuhamelDomain S m (n k) (τ k) (h k)
              (qStep k) f : S.generatorDomain) : H)) =
        (fun k : ℕ => S t (p₀ : H) +
          pressureMultiwellBochnerForcing S μ backwardTime m f (q k)) := by
      funext k
      exact hAsSum k
    rw [hEqFun]
    exact hPressure
  exact pressure_multiwell_A5_of_step_limit S hSelf hGraph
    t p₀ m n τ h hτ0 hStep qStep M hM hqStep f _ hLimit

end MultiwellBridge

end ReservoirSeismicityControl
