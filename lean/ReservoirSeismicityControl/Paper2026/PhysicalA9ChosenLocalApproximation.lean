import ReservoirSeismicityControl.Paper2026.PhysicalA9L2ProfileLimit
import Mathlib.Tactic

/-!
Appendix A.3 (A9): choice-preserving version of the verified A5 L² well-profile limit.

The previous L²-limit theorem constructs a *particular* sequence using
unrestricted generator-domain density. Off-diagonal bounds do not apply to
arbitrarily chosen approximants, since their approximation errors can
spread into the far region. Here we expose the approximation sequence as
data and prove that A5 stability works for ANY choice, including ones
whose *differences* from the physical well sources stay in a near collar.
For manuscript A1, the mean-zero well profile is f_j = B_j/β - c_j, so the
centered smooth approximant must be φ_{j,n} - c_j with φ_{j,n} compactly
supported in U_j. The difference then stays in U_j, although neither
centered profile is supported only near the well. Existing 3D interior
smooth-density results and the cited local elliptic inclusion for compactly
supported smooth tests furnish the required external applicability step.
This physical specialization is NOT asserted by this theorem.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace

set_option maxHeartbeats 2000000

/-- Unlike the existential density version, this theorem accepts ANY
chosen generator-domain approximations converging in L². Consequently it
can be applied to approximants with *localized approximation errors* once
standard interior density and domain inclusion are instantiated in U_j.
The proof reuses the established A5 profile-stability estimate and the
previously compiled smooth-well causal identity. It does not assume any
far-kernel convergence or differentiate the well fluxes. -/
theorem paper_A9_chosen_local_approximants_smooth_causal_limit
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
        |q j s| ≤ M j)
    (fApprox : ℕ → Fin m → S.generatorDomain)
    (hApproxLimit : ∀ j : Fin m, Tendsto
      (fun n : ℕ => (fApprox n j : Lp ℝ 2 μ))
      atTop (𝓝 (f j))) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    ∃ hp : (S t (p₀ : Lp ℝ 2 μ) +
      ReservoirSeismicityControl.pressureA5ForwardDuhamel S t m f q) ∈ S.generatorDomain,
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
  exact ⟨hpPhys, hLimit⟩

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_chosen_local_approximants_smooth_causal_limit
