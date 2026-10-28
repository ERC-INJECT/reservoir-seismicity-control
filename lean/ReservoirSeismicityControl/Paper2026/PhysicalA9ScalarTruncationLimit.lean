import ReservoirSeismicityControl.Paper2026.PhysicalA9TruncatedScalarCausal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): removal of the positive-lag truncation, scalar level

The preceding compiled theorem identifies the *truncated* finite-well
mild-pressure observation with a scalar causal kernel convolution.
This theorem removes that truncation using continuity of the Lebesgue
integral in its upper endpoint. The only analytical premise is the
integrability of each actual frozen-observation scalar kernel times its
well flux on (0,t], which is the standard bounded-input A8 applicability
condition. No derivative of the well flux is used.

This does NOT identify the limit of the unprojected generator integral;
that integral may not converge strongly without projection. Nor does it
prove differentiation in observation time or full equation (A9).
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped InnerProductSpace BigOperators Topology

/-- The finite-well, physical frozen-observation causal integral is the
limit of its positive-lag truncations. The integrands are precisely those
of `paper_A9_physical_truncated_SR_scalar_causal`.

This uses only `IntegrableOn` and continuity of an integral primitive;
no differentiation or uniform convergence of the flux is assumed. -/
theorem paper_A9_physical_scalar_truncation_limit
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (V : Submodule ℝ (Lp ℝ 2 μ))
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsep : ∀ f : Lp ℝ 2 μ,
      (∀ v : V, ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ = 0) → f = 0)
    {n : ℕ} (orbit : Fin n → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V E)
    (Q : Fin n → ℝ → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hScalar : ∀ j : Fin n,
      Integrable (fun s : ℝ => Q j s *
        paperSRFarSmoothKernel μ region hregion Kγ R
          gamma10 R0star cutoff V E hsep orbit t j (t - s))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t))) :
    Tendsto
      (fun ε : ℝ => ∫ s in Set.Ioc (0 : ℝ) (t - ε),
        ∑ j : Fin n, Q j s *
          paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t j (t - s))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) t,
        ∑ j : Fin n, Q j s *
          paperSRFarSmoothKernel μ region hregion Kγ R
            gamma10 R0star cutoff V E hsep orbit t j (t - s))) := by
  let F : ℝ → ℝ := fun s => ∑ j : Fin n, Q j s *
    paperSRFarSmoothKernel μ region hregion Kγ R
      gamma10 R0star cutoff V E hsep orbit t j (t - s)
  have hF : IntegrableOn F (Set.Ioc (0 : ℝ) t) volume := by
    change Integrable (fun s : ℝ => ∑ j : Fin n, Q j s *
      paperSRFarSmoothKernel μ region hregion Kγ R
        gamma10 R0star cutoff V E hsep orbit t j (t - s))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t))
    exact integrable_finset_sum Finset.univ (fun j _ => hScalar j)
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
  change Tendsto
      (fun ε : ℝ => ∫ s in Set.Ioc (0 : ℝ) (t - ε), F s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) t, F s))
  exact hPrimitive.comp hsub

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_physical_scalar_truncation_limit
