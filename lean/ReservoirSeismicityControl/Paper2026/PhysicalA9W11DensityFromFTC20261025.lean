import ReservoirSeismicityControl.Paper2026.PhysicalA9VectorSobolevFTC20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9ApproximationTranslation20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9VectorL1Bridge20261025
import Mathlib.Tactic

/-!
# A9: ACTUAL projected Neumann convolution rate using the external Banach W1,1 density theorem

The previous PASSED modules prove full-line L1 for the physical projected
Neumann kernel and its positive-lag derivative, and the zero-trace Bochner
FTC. Here the *only* analytic input not formalized in Lean is the standard,
universal Banach-valued Sobolev W1,1 smooth-density theorem. It is supplied
as a theorem-level parameter, expressly for ALL L1 vector functions that
satisfy the interval FTC and causal zero extension, NOT as an assumption on
the physical well kernel or its convolution derivative.

This theorem CONSTRUCTS all eight formerly independent time-translated
convolution conditions and derives the physical projected convolution rate.
The positive-time homogeneous semigroup identity and identification with
actual pressure solution are separate physical obligations. No Qdot.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

set_option maxHeartbeats 2000000

/-- The precise universal, externally cited Banach-valued `W^{1,1}(ℝ;H)`
    smooth-density theorem, specialized only to the Hilbert target `L²(μ)`.

    The premise `∀ b>0, ∫₀ᵇ dk = k b`, together with the causal zero extension,
    guarantees that `dk` is the *weak derivative of `k` on the full line*.
    Thus this is standard Sobolev density, not a new physical hypothesis.

    In a future Mathlib release this can be proved from its abstract Bochner
    Sobolev density theorems; here it is an explicit cited analytic dependency.
-/
def PaperA9BanachW11Density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ (k dk : ℝ → Lp ℝ 2 μ),
    Integrable k (volume : Measure ℝ) →
    Integrable dk (volume : Measure ℝ) →
    (∀ s : ℝ, s ≤ 0 → k s = 0 ∧ dk s = 0) →
    (∀ b : ℝ, 0 < b →
      (∫ s in (0 : ℝ)..b, dk s) = k b) →
    ∃ f : ℕ → ℝ → Lp ℝ 2 μ,
      (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, ContDiff ℝ 1 (f n)) ∧
      (∀ n, Integrable (f n) (volume : Measure ℝ)) ∧
      (∀ n, Integrable (fun s => deriv (f n) s) (volume : Measure ℝ)) ∧
      Tendsto (fun n => ∫ s : ℝ, ‖f n s - k s‖) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => ∫ s : ℝ, ‖deriv (f n) s - dk s‖) atTop (𝓝 (0 : ℝ))

/-- From the universal cited W11-density theorem, our PASSED full-line
    integrability, physical zero trace/FTC, and bounded measurable well
    fluxes, derive the convolution derivative. No separate approximants,
    translated errors, or forcing derivative are assumed. -/
theorem paper_A9_vector_convolution_derivative_from_FTC_and_standard_density
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : ℕ}
    (q : Fin m → ℝ → ℝ)
    (kernel rate : Fin m → ℝ → Lp ℝ 2 μ)
    (hqLoc : ∀ j : Fin m, LocallyIntegrable (q j) volume)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (q j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |q j s| ≤ M j)
    (hKernelInt : ∀ j : Fin m,
      Integrable (kernel j) (volume : Measure ℝ))
    (hRateInt : ∀ j : Fin m,
      Integrable (rate j) (volume : Measure ℝ))
    (hCausal : ∀ (j : Fin m) (s : ℝ), s ≤ 0 →
      kernel j s = 0 ∧ rate j s = 0)
    (hFTC : ∀ (j : Fin m) (b : ℝ), 0 < b →
      (∫ s in (0 : ℝ)..b, rate j s) = kernel j b)
    (hDensity : PaperA9BanachW11Density μ)
    (t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∑ j : Fin m,
        ∫ s : ℝ, q j s • kernel j (τ - s))
      (∑ j : Fin m, ∫ s : ℝ, q j s • rate j (t - s)) t := by
  classical
  have hApprox : ∀ j : Fin m,
      ∃ f : ℕ → ℝ → Lp ℝ 2 μ,
        (∀ n, HasCompactSupport (f n)) ∧
        (∀ n, ContDiff ℝ 1 (f n)) ∧
        (∀ n, Integrable (f n) (volume : Measure ℝ)) ∧
        (∀ n, Integrable (fun s => deriv (f n) s) (volume : Measure ℝ)) ∧
        Tendsto (fun n => ∫ s : ℝ, ‖f n s - kernel j s‖)
          atTop (𝓝 (0 : ℝ)) ∧
        Tendsto (fun n => ∫ s : ℝ, ‖deriv (f n) s - rate j s‖)
          atTop (𝓝 (0 : ℝ)) := by
    intro j
    exact hDensity (kernel j) (rate j)
      (hKernelInt j) (hRateInt j) (hCausal j) (hFTC j)
  choose approx hCompact hSmooth hKnInt hKnRateInt hErrorValue hErrorRate using hApprox
  let kn : ℕ → Fin m → ℝ → Lp ℝ 2 μ := fun n j => approx j n
  let errValue : Fin m → ℕ → ℝ := fun j n =>
    ∫ s : ℝ, ‖kn n j s - kernel j s‖
  let errRate : Fin m → ℕ → ℝ := fun j n =>
    ∫ s : ℝ, ‖deriv (kn n j) s - rate j s‖
  have hM (j : Fin m) : 0 ≤ M j :=
    (abs_nonneg (q j 0)).trans (hqBound j 0)
  have hTranslate :=
    paper_A9_global_W11_density_disposes_of_translated_assumptions
      μ q kernel rate kn hqMeas M hqBound hKernelInt hRateInt
      (fun n j => hKnInt j n)
      (fun n j => hKnRateInt j n)
      errValue errRate
      (fun j n => le_refl _)
      (fun j n => le_refl _)
  obtain ⟨hIntValue, hIntKn, hIntRate, hIntKnRate,
          hDiffValueInt, hDiffValueMass,
          hDiffRateInt, hDiffRateMass⟩ := hTranslate
  have herrValue (j : Fin m) :
      Tendsto (errValue j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [errValue, kn] using hErrorValue j
  have herrRate (j : Fin m) :
      Tendsto (errRate j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [errRate, kn] using hErrorRate j
  exact paper_A9_vector_multiwell_rate_from_L1_kernel_approximation
    μ q kernel rate kn hqLoc
    (fun n j => hCompact j n) (fun n j => hSmooth j n)
    M hM hqBound errValue errRate herrValue herrRate
    hIntValue hIntKn hIntRate hIntKnRate
    hDiffValueInt hDiffValueMass hDiffRateInt hDiffRateMass t

/-- PHYSICAL NEUMANN SPECIALIZATION: the output is the actual far-projected
    A9 forcing convolution derivative. The kernel, rate, causal support,
    integrability and FTC follow from the proven physical semigroup/DG
    results, while the smooth approximation is obtained by instantiating
    only the universal cited Banach W11-density theorem above. -/
theorem paper_A9_physical_projected_convolution_rate_from_DG_and_density
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {m : ℕ}
    (orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (second : Fin m → ℝ → Lp ℝ 2 μ)
    (hOrbit : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      HasDerivAt
        (fun z => ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j z))
        (-(second j lag)) lag)
    (B₀ B₁ : Fin m → ℝ → ℝ)
    (hB₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₀ j lag)
    (hB₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag → 0 ≤ B₁ j lag)
    (hDG₀ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))‖
        ≤ B₀ j lag)
    (hDG₁ : ∀ (j : Fin m) (lag : ℝ), 0 < lag →
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag)‖
        ≤ B₁ j lag)
    (hB₀Int : ∀ j : Fin m,
      Integrable (B₀ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₁Int : ∀ j : Fin m,
      Integrable (B₁ j) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hB₀Zero : ∀ j : Fin m,
      Tendsto (B₀ j) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hOrbitMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag)))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (hSecondMeas : ∀ j : Fin m,
      AEStronglyMeasurable
        (fun lag => ReservoirSeismicityControl.paperFarLpProjection μ far hfar (second j lag))
        (volume.restrict (Set.Ioi (0 : ℝ))))
    (qext : Fin m → ℝ → ℝ)
    (hqLoc : ∀ j : Fin m, LocallyIntegrable (qext j) volume)
    (hqMeas : ∀ j : Fin m,
      AEStronglyMeasurable (qext j) (volume : Measure ℝ))
    (M : Fin m → ℝ)
    (hqBound : ∀ (j : Fin m) (s : ℝ), |qext j s| ≤ M j)
    (hDensity : PaperA9BanachW11Density μ) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
      else 0
    let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
      if 0 < lag then -(P (second j lag)) else 0
    ∀ t : ℝ,
      HasDerivAt
        (fun τ : ℝ => ∑ j : Fin m,
          ∫ s : ℝ, qext j s • kernel j (τ - s))
        (∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)) t := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let kernel : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j lag))
    else 0
  let rate : Fin m → ℝ → Lp ℝ 2 μ := fun j lag =>
    if 0 < lag then -(P (second j lag)) else 0
  change ∀ t : ℝ,
      HasDerivAt
        (fun τ : ℝ => ∑ j : Fin m,
          ∫ s : ℝ, qext j s • kernel j (τ - s))
        (∑ j : Fin m, ∫ s : ℝ, qext j s • rate j (t - s)) t
  obtain ⟨hKernelInt, hRateInt, _hValueInt, _hRateConvInt,
          _hDerivative, _hTrace, hZero⟩ :=
    paper_A9_physical_projected_vector_full_line_certificate
      μ far hfar V E hsep orbit second hOrbit B₀ B₁
      hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas qext hqMeas M hqBound
  have hFTC : ∀ (j : Fin m) (b : ℝ), 0 < b →
      (∫ s in (0 : ℝ)..b, rate j s) = kernel j b :=
    paper_A9_physical_projected_vector_FTC_from_DG
      μ far hfar V E hsep orbit second hOrbit B₀ B₁
      hB₀ hB₁ hDG₀ hDG₁ hB₀Int hB₁Int hB₀Zero
      hOrbitMeas hSecondMeas
  intro t
  exact paper_A9_vector_convolution_derivative_from_FTC_and_standard_density
    μ qext kernel rate hqLoc hqMeas M hqBound
    hKernelInt hRateInt hZero hFTC hDensity t

#print axioms paper_A9_vector_convolution_derivative_from_FTC_and_standard_density
#print axioms paper_A9_physical_projected_convolution_rate_from_DG_and_density

end ReservoirSeismicityControl.Paper2026
