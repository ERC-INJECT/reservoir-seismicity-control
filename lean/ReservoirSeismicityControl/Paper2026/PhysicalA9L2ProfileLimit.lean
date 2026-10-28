import ReservoirSeismicityControl.Paper2026.PhysicalA9SmoothProfileGeneratorCausal
import ReservoirSeismicityControl.PaperA5ProfileStability
import ReservoirSeismicityControl.PressurePositiveSemigroupA5ForwardPhysical
import ReservoirSeismicityControl.PaperA5CausalLocalIntegrability
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Appendix A.3 (A9): passing from smooth wells to actual L² well profiles

This is the *generator-profile* limit, not yet the off-diagonal
identification of the resulting limit with an integral of the positive-lag
physical kernel. Its role is to remove the unwanted `f_j ∈ D(A)` restriction
from the already compiled smooth-well causal formula.

For each arbitrary L² well source, choose generator-domain approximations
using density (already provided by the physical A5 semigroup). The sharp A5
profile stability theorem bounds the difference of the *actual* generator
images by ∑ M_j ‖f_j-f_j,n‖, without differentiating Q. Thus the far
projections of the already verified smooth-well causal expressions converge
in L² exactly to the far projection of the physical mild-solution generator.

The remaining equation that identifies this LIMIT with the physical
positive-lag Bochner integral requires the externally cited off-diagonal
Davies--Gaffney envelope and its applicability to localized sources. No
such equation is taken as a hypothesis in this theorem.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace

set_option maxHeartbeats 2000000

/-- The physical far-projected generator for arbitrary fixed L² wells is the
strong L² limit of smooth-well causal-generator formulas.

`hSelf`, `hGraph` are the Neumann realization assumptions established by A5.
`hBound` is the existing measurable/bounded-well-rate assumption A1.
The approximating profiles are *constructed* using domain density; their
existence is not an extra manuscript hypothesis. No derivative of Q is used.
-/
theorem paper_A9_L2_wells_smooth_causal_limit_is_physical_generator
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSelf : ∀ s : NNReal, IsSelfAdjoint (S s))
    (hGraph : ∀ u g : Lp ℝ 2 μ,
      (∀ v : Lp ℝ 2 μ, ∀ hv : v ∈ S.generatorDomain,
        ⟪u, S.generator ⟨v, hv⟩⟫_ℝ = ⟪g, v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = g)
    (t : NNReal) (p₀ : S.generatorDomain)
    (m : ℕ) (f : Fin m → Lp ℝ 2 μ) (q : Fin m → ℝ → ℝ)
    (hq : ∀ j : Fin m, Integrable (q j)
      (volume.restrict (Set.Ico 0 (t : ℝ))))
    (M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hBound : ∀ j : Fin m,
      ∀ᵐ s ∂(volume.restrict (Set.Ico 0 (t : ℝ))),
        |q j s| ≤ M j) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
    ∃ fApprox : ℕ → Fin m → S.generatorDomain,
      (∀ j : Fin m, Tendsto
        (fun n : ℕ => (fApprox n j : Lp ℝ 2 μ))
        atTop (𝓝 (f j))) ∧
      Tendsto
        (fun n : ℕ => P (S t (S.generator p₀)) +
          ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
            q j s • P (S (Real.toNNReal ((t : ℝ) - s))
              (S.generator (fApprox n j))))
        atTop
        (𝓝 (P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hp⟩))) := by
  classical
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  have hInterval (j : Fin m) :
      IntervalIntegrable (q j) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le
      (NNReal.coe_nonneg t)).2 (hq j)
  obtain ⟨hpPhys, _⟩ := ReservoirSeismicityControl.pressure_multiwell_A5_measurable_forward
    S hSelf hGraph t p₀ m f q hq M hM hBound
  have hSeq (j : Fin m) :
      ∃ a : ℕ → Lp ℝ 2 μ,
        (∀ n, a n ∈ S.generatorDomain) ∧
        Tendsto a atTop (𝓝 (f j)) := by
    exact mem_closure_iff_seq_limit.mp (S.dense_generatorDomain (f j))
  let fApprox (n : ℕ) (j : Fin m) : S.generatorDomain :=
    ⟨(hSeq j).choose n, (hSeq j).choose_spec.1 n⟩
  have hApproxLimit (j : Fin m) :
      Tendsto (fun n : ℕ => (fApprox n j : Lp ℝ 2 μ))
        atTop (𝓝 (f j)) :=
    (hSeq j).choose_spec.2
  let error (n : ℕ) : ℝ :=
    ∑ j : Fin m, M j * ‖(fApprox n j : Lp ℝ 2 μ) - f j‖
  have hErrEach (j : Fin m) :
      Tendsto (fun n : ℕ => ‖(fApprox n j : Lp ℝ 2 μ) - f j‖)
        atTop (𝓝 0) := by
    have hdiff := (hApproxLimit j).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f j) atTop (𝓝 (f j)))
    simpa only [sub_self, norm_zero] using hdiff.norm
  have hErr : Tendsto error atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n : ℕ => ∑ j : Fin m,
          M j * ‖(fApprox n j : Lp ℝ 2 μ) - f j‖)
        atTop (𝓝 (∑ j : Fin m, (0 : ℝ))) := by
      apply tendsto_finsetSum Finset.univ
      intro j _
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (hErrEach j) :
          Tendsto (fun n : ℕ =>
            M j * ‖(fApprox n j : Lp ℝ 2 μ) - f j‖)
            atTop (𝓝 (M j * 0)))
    simpa only [error, Finset.sum_const_zero] using hsum
  have hSmooth (n : ℕ) :=
    paper_A9_smooth_wells_projected_full_causal_generator
      μ far hfar S t p₀ m (fApprox n) q hq
  let causal (n : ℕ) : Lp ℝ 2 μ :=
    P (S t (S.generator p₀)) +
      ∑ j : Fin m, ∫ s in (0 : ℝ)..(t : ℝ),
        q j s • P (S (Real.toNNReal ((t : ℝ) - s))
          (S.generator (fApprox n j)))
  have hIdent (n : ℕ) :
      causal n =
        P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
            (fun j => (fApprox n j : Lp ℝ 2 μ)) q,
          (hSmooth n).choose⟩) := by
    exact (hSmooth n).choose_spec.symm
  have hStable (n : ℕ) :
      ‖S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m
            (fun j => (fApprox n j : Lp ℝ 2 μ)) q,
          (hSmooth n).choose⟩ -
        S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpPhys⟩‖ ≤
        error n := by
    have hRegular (j : Fin m) : IntervalIntegrable
        (fun s : ℝ => q j s •
          S (Real.toNNReal ((t : ℝ) - s))
            (fApprox n j : Lp ℝ 2 μ)) volume 0 (t : ℝ) :=
      ReservoirSeismicityControl.pressure_A5_forward_orbit_intervalIntegrable
        S t (q j) (fApprox n j : Lp ℝ 2 μ) (hInterval j)
    have hOriginal (j : Fin m) : IntervalIntegrable
        (fun s : ℝ => q j s •
          S (Real.toNNReal ((t : ℝ) - s)) (f j)) volume 0 (t : ℝ) :=
      ReservoirSeismicityControl.pressure_A5_forward_orbit_intervalIntegrable
        S t (q j) (f j) (hInterval j)
    simpa only [error] using
      (ReservoirSeismicityControl.pressure_A5_forward_generator_profile_stability
        S hSelf hGraph t p₀ m
        (fun j => (fApprox n j : Lp ℝ 2 μ)) f q hq M hM hBound
        hRegular hOriginal (hSmooth n).choose hpPhys)
  have hLimit : Tendsto causal atTop
      (𝓝 (P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
        ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpPhys⟩))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hBoundApprox (n : ℕ) :
        ‖causal n - P (S.generator ⟨S t (p₀ : Lp ℝ 2 μ) +
          ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q, hpPhys⟩)‖ ≤
          ‖P‖ * error n := by
      rw [hIdent n, ← map_sub]
      exact (P.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hStable n) (norm_nonneg P))
    have hScaled : Tendsto (fun n : ℕ => ‖P‖ * error n)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hErr :
          Tendsto (fun n : ℕ => ‖P‖ * error n)
            atTop (𝓝 (‖P‖ * 0)))
    exact squeeze_zero (fun n => norm_nonneg _) hBoundApprox hScaled
  refine ⟨hpPhys, fApprox, hApproxLimit, ?_⟩
  exact hLimit

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_L2_wells_smooth_causal_limit_is_physical_generator
