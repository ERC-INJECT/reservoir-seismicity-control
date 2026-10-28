import ReservoirSeismicityControl.Paper2026.PhysicalA9ScalarTruncationLimit
import ReservoirSeismicityControl.Paper2026.PhysicalA9TruncatedMildProjection
import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9Reflection
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Appendix A.3 (A9) — actual far-projected L² generator forcing to zero lag

The already compiled `PhysicalA9TruncatedMildProjection` works only for a
positive-lag truncated generator integral; the already compiled
`PhysicalA9ScalarTruncationLimit` removes that truncation *after scalar
pairing*. The missing vector-valued bridge is that the **projected**
forcing, unlike the unprojected generator forcing, is Bochner integrable
right down to the zero-lag boundary.

This result uses the positive-lag off-diagonal `B₀` envelope from (A8),
its L¹ property (a cited semigroup applicability input), a.e. strong
measurability, and the bounded physical well flux from Assumption 1.
It does NOT require differentiation of `Q`, it does not claim the
unprojected generator integral is integrable at lag zero, and it does
NOT yet identify the integral with `P_far (A p(t))`. That final identity
has to come from the existing physical A5 mild-solution construction.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology

/-- For the physical Neumann generator orbit, the sharp far-projected
finite-well forcing is Bochner integrable on `(0,t]`, and its
positive-lag truncated integrals converge **strongly in L²** to the full
far-projected integral as the lag cutoff tends to zero.

The projected-orbit envelope and measurability premises are precisely
the a.e. consequences of the external off-diagonal analytic-semigroup
bounds used in (A8). They are not assumptions about the desired limit. -/
theorem paper_A9_physical_projected_full_generator_limit
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Q : Fin n → ℝ → ℝ)
    (t : ℝ) (ht : 0 < t)
    (B₀ : Fin n → ℝ → ℝ) (M : Fin n → ℝ)
    (hM : ∀ j : Fin n, 0 ≤ M j)
    (hB₀Integrable : ∀ j : Fin n,
      Integrable (B₀ j) ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
    (hQmeas : ∀ j : Fin n,
      AEStronglyMeasurable (Q j)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hQ : ∀ j : Fin n,
      ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
        |Q j s| ≤ M j)
    (hOrbitMeas : ∀ j : Fin n,
      AEStronglyMeasurable
        (fun s : ℝ => ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s))))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)))
    (hOrbitEnvelope : ∀ j : Fin n,
      ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
        ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
          (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))‖ ≤
            B₀ j (t - s)) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let F : ℝ → Lp ℝ 2 μ := fun s => ∑ j : Fin n, (Q j s) •
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
    Integrable F ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)) ∧
      Tendsto
        (fun ε : ℝ => ∫ s in Set.Ioc (0 : ℝ) (t - ε), F s)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ s in Set.Ioc (0 : ℝ) t, F s)) := by
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)
  let F : ℝ → Lp ℝ 2 μ := fun s => ∑ j : Fin n, (Q j s) •
    P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))
  change Integrable F ν ∧
    Tendsto (fun ε : ℝ => ∫ s in Set.Ioc (0 : ℝ) (t - ε), F s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s in Set.Ioc (0 : ℝ) t, F s))
  have hEach (j : Fin n) :
      Integrable (fun s : ℝ => (Q j s) •
        P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))) ν := by
    have hLag := (paper_A9_lag_reflection (B₀ j) t ht.le
      (hB₀Integrable j)).1
    have hEnvelope : Integrable (fun s : ℝ => M j * B₀ j (t - s)) ν :=
      hLag.const_mul (M j)
    apply hEnvelope.mono' ((hQmeas j).smul (hOrbitMeas j))
    filter_upwards [hQ j, hOrbitEnvelope j] with s hQs hOs
    have hbound :
        ‖(Q j s) • P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
          (orbit j (t - s)))‖ ≤ M j * B₀ j (t - s) := by
      calc
        _ = |Q j s| * ‖P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit j (t - s)))‖ := by
                simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ M j * ‖P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep
              (orbit j (t - s)))‖ :=
                mul_le_mul_of_nonneg_right hQs (norm_nonneg _)
        _ ≤ M j * B₀ j (t - s) :=
                mul_le_mul_of_nonneg_left hOs (hM j)
    first
    | exact hbound
    | simpa only [Pi.smul_apply] using hbound
    | simpa using hbound
  have hF : Integrable F ν := by
    change Integrable (fun s : ℝ => ∑ j : Fin n, (Q j s) •
      P (ReservoirSeismicityControl.pressureWeakNeumannOperator V E hsep (orbit j (t - s)))) ν
    exact integrable_finset_sum Finset.univ (fun j _ => hEach j)
  have hIcc : IntegrableOn F (Set.Icc (0 : ℝ) t) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 hF
  have hContinuous : ContinuousOn
      (fun u : ℝ => ∫ s in Set.Ioc (0 : ℝ) u, F s)
      (Set.Icc (0 : ℝ) t) :=
    intervalIntegral.continuousOn_primitive hIcc
  have hsub0 : Tendsto (fun ε : ℝ => t - ε)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    have hzero : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_zero] using (tendsto_const_nhds.sub hzero :
      Tendsto (fun ε : ℝ => t - ε) (𝓝[>] (0 : ℝ)) (𝓝 (t - 0)))
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < t :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds) (Iio_mem_nhds ht)
  have hinside : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      t - ε ∈ Set.Icc (0 : ℝ) t := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεt hεpos
    exact ⟨sub_nonneg.mpr hεt.le, sub_le_self _ hεpos.le⟩
  have hsub : Tendsto (fun ε : ℝ => t - ε)
      (𝓝[>] (0 : ℝ)) (𝓝[Set.Icc (0 : ℝ) t] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsub0, hinside⟩
  have hPrimitive : Tendsto
      (fun u : ℝ => ∫ s in Set.Ioc (0 : ℝ) u, F s)
      (𝓝[Set.Icc (0 : ℝ) t] t)
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) t, F s)) :=
    (hContinuous t ⟨ht.le, le_rfl⟩).tendsto
  refine ⟨hF, ?_⟩
  exact hPrimitive.comp hsub

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_projected_full_generator_limit
