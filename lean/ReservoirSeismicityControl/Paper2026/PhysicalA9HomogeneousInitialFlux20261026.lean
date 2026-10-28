import ReservoirSeismicityControl.Paper2026.PhysicalA9MildValueAndHomogeneousOrbit20261025
import ReservoirSeismicityControl.Paper2026.PhysicalA9SmoothedGeneratorRate20261025
import Mathlib.Tactic

/-!
# A9 homogeneous pressure derivative from physical initial flux compatibility

No assumption that `S.generator p₀` belongs to `S.generatorDomain` is made.
The *initial pressure rate* `pt0` belongs to the generator domain, exactly as
required by Appendix A.1. The well profiles can be L² elements outside D(A).

Use p_t(0) = S.generator p₀ + ∑ Q_j(0) f_j to split the homogeneous term
into one regular semigroup orbit and finitely many analytic-smoothed well
orbits. Its rate is bounded by semigroup contraction and the standard
positive-lag far-field DG bounds. No Qdot occurs.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace BigOperators
set_option maxHeartbeats 2000000

/-- Any analytic-smoothed L² orbit has the positive-time derivative given by
its genuine generator (no assumption f ∈ D(A)). -/
theorem paper_A9_positive_time_semigroup_orbit_derivative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun τ : ℝ => S (Real.toNNReal τ) f)
      (S.generator ⟨S (Real.toNNReal t) f, hSmooth f t ht⟩) t := by
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hta : 0 < t - a := by dsimp [a]; linarith
  let u : S.generatorDomain := ⟨S (Real.toNNReal a) f, hSmooth f a ha⟩
  have htranslate : HasDerivAt (fun s : ℝ => s - a) 1 t := by
    convert (hasDerivAt_id t).sub_const a using 1 <;> simp
  have hd : HasDerivAt
      (fun s : ℝ => S (Real.toNNReal (s - a)) (u : Lp ℝ 2 μ))
      (S (Real.toNNReal (t - a)) (S.generator u)) t := by
    have h := (S.hasDerivAt_operator_toNNReal u hta).scomp t htranslate
    simpa only [Function.comp_def, one_smul] using h
  have htime (s : ℝ) (hs : a < s) :
      Real.toNNReal (s - a) + Real.toNNReal a = Real.toNNReal s := by
    have hsa : 0 ≤ s - a := by linarith
    have hs0 : 0 ≤ s := by linarith
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ hsa,
      Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hs0]
    ring
  have hsame :
      (⟨S (Real.toNNReal t) f, hSmooth f t ht⟩ : S.generatorDomain) =
        ⟨S (Real.toNNReal (t - a)) (u : Lp ℝ 2 μ),
          S.operator_mem_generatorDomain u (Real.toNNReal (t - a))⟩ := by
    apply Subtype.ext
    change S (Real.toNNReal t) f =
      S (Real.toNNReal (t - a)) (S (Real.toNNReal a) f)
    rw [← S.add_apply, htime t (by dsimp [a]; linarith)]
  have hgen : S.generator
      ⟨S (Real.toNNReal t) f, hSmooth f t ht⟩ =
        S (Real.toNNReal (t - a)) (S.generator u) := by
    rw [hsame, S.generator_operator]
  have hlocal :
      (fun s : ℝ => S (Real.toNNReal s) f) =ᶠ[𝓝 t]
        (fun s : ℝ => S (Real.toNNReal (s - a)) (u : Lp ℝ 2 μ)) := by
    have hAt : t ∈ Set.Ioi a := by
      change a < t
      linarith only [hta]
    filter_upwards [isOpen_Ioi.mem_nhds hAt] with s hs
    change S (Real.toNNReal s) f =
      S (Real.toNNReal (s - a)) (S (Real.toNNReal a) f)
    rw [← S.add_apply, htime s hs]
  rw [hgen]
  exact hd.congr_of_eventuallyEq hlocal

/-- Physical positive-time homogeneous far rate, with the initial flux
endpoint retained explicitly. The bound uses *only* the initial rate's graph
norm and uniform physical far-field generator bounds for L² wells. -/
theorem paper_A9_physical_homogeneous_rate_from_initial_flux_and_DG
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (p₀ pt0 : S.generatorDomain)
    {m : ℕ} (f : Fin m → Lp ℝ 2 μ) (Q0 : Fin m → ℝ)
    (hInitial : (pt0 : Lp ℝ 2 μ) =
      S.generator p₀ + ∑ i : Fin m, (Q0 i) • f i)
    (M : Fin m → ℝ)
    (hFarDG : ∀ (i : Fin m) (t : ℝ) (ht : 0 < t),
      ‖ReservoirSeismicityControl.paperFarLpProjection μ far hfar
        (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)‖ ≤ M i) :
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    let wellRate : Fin m → ℝ → Lp ℝ 2 μ := fun i t =>
      if ht : 0 < t then
        P (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)
      else 0
    let rate : ℝ → Lp ℝ 2 μ := fun t =>
      -(P (S (Real.toNNReal t) (S.generator pt0))) +
        ∑ i : Fin m, (Q0 i) • wellRate i t
    let Ch : ℝ := ‖P‖ * ‖S.generator pt0‖ +
      ∑ i : Fin m, |Q0 i| * M i
    (∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => if hτ : 0 ≤ τ then
          -(P (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀))) else 0)
        (rate t) t) ∧
    (∀ t : ℝ, 0 < t → ‖rate t‖ ≤ Ch) := by
  classical
  let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
  let wellRate : Fin m → ℝ → Lp ℝ 2 μ := fun i t =>
    if ht : 0 < t then
      P (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)
    else 0
  let rate : ℝ → Lp ℝ 2 μ := fun t =>
    -(P (S (Real.toNNReal t) (S.generator pt0))) +
      ∑ i : Fin m, (Q0 i) • wellRate i t
  let Ch : ℝ := ‖P‖ * ‖S.generator pt0‖ +
    ∑ i : Fin m, |Q0 i| * M i
  change (∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => if hτ : 0 ≤ τ then
          -(P (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀))) else 0)
        (rate t) t) ∧
    (∀ t : ℝ, 0 < t → ‖rate t‖ ≤ Ch)
  have hInitial' : S.generator p₀ =
      (pt0 : Lp ℝ 2 μ) - ∑ i : Fin m, (Q0 i) • f i := by
    rw [hInitial]
    abel
  have hExpr :
      (fun τ : ℝ => -(P (S (Real.toNNReal τ) (S.generator p₀)))) =
      (fun τ : ℝ => -(P (S (Real.toNNReal τ) (pt0 : Lp ℝ 2 μ))) +
        ∑ i : Fin m, (Q0 i) • P (S (Real.toNNReal τ) (f i))) := by
    funext τ
    rw [hInitial']
    simp only [map_sub, map_sum, map_smul, neg_sub]
    abel
  constructor
  · intro t ht
    have hPt : HasDerivAt
        (fun τ : ℝ => -(P (S (Real.toNNReal τ) (pt0 : Lp ℝ 2 μ))))
        (-(P (S (Real.toNNReal t) (S.generator pt0)))) t := by
      exact (P.hasFDerivAt.comp_hasDerivAt t
        (S.hasDerivAt_operator_toNNReal pt0 ht)).neg
    have hWell (i : Fin m) : HasDerivAt
        (fun τ : ℝ => P (S (Real.toNNReal τ) (f i)))
        (wellRate i t) t := by
      have hd := paper_A9_positive_time_semigroup_orbit_derivative
        μ S hSmooth (f i) t ht
      have hp := P.hasFDerivAt.comp_hasDerivAt t hd
      change HasDerivAt
        (fun τ : ℝ => P (S (Real.toNNReal τ) (f i)))
        (P (S.generator ⟨S (Real.toNNReal t) (f i), hSmooth (f i) t ht⟩)) t at hp
      simpa only [wellRate, dif_pos ht] using hp
    have hSum : HasDerivAt
        (fun τ : ℝ => ∑ i : Fin m,
          (Q0 i) • P (S (Real.toNNReal τ) (f i)))
        (∑ i : Fin m, (Q0 i) • wellRate i t) t := by
      apply HasDerivAt.fun_sum
      intro i _
      exact (hWell i).fun_const_smul (Q0 i)
    have hRaw : HasDerivAt
        (fun τ : ℝ => -(P (S (Real.toNNReal τ) (S.generator p₀))))
        (rate t) t := by
      rw [hExpr]
      exact hPt.add hSum
    have hlocal :
        (fun τ : ℝ => if hτ : 0 ≤ τ then
          -(P (S (⟨τ, hτ⟩ : NNReal) (S.generator p₀))) else 0) =ᶠ[𝓝 t]
        (fun τ : ℝ => -(P (S (Real.toNNReal τ) (S.generator p₀)))) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
      change (0 : ℝ) < τ at hτ
      have hNN : (⟨τ, hτ.le⟩ : NNReal) = Real.toNNReal τ := by
        apply NNReal.coe_injective
        change τ = (Real.toNNReal τ : ℝ)
        exact (Real.coe_toNNReal _ hτ.le).symm
      simpa only [dif_pos hτ.le, hNN]
    exact hRaw.congr_of_eventuallyEq hlocal
  · intro t ht
    have hPtBound :
        ‖P (S (Real.toNNReal t) (S.generator pt0))‖ ≤
          ‖P‖ * ‖S.generator pt0‖ := by
      calc
        _ ≤ ‖P‖ * ‖S (Real.toNNReal t) (S.generator pt0)‖ := P.le_opNorm _
        _ ≤ ‖P‖ * ‖S.generator pt0‖ :=
          mul_le_mul_of_nonneg_left (S.norm_apply_le _ _) (norm_nonneg _)
    have hSumBound :
        ‖∑ i : Fin m, (Q0 i) • wellRate i t‖ ≤
          ∑ i : Fin m, |Q0 i| * M i := by
      calc
        _ ≤ ∑ i : Fin m, ‖(Q0 i) • wellRate i t‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin m, |Q0 i| * M i := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Real.norm_eq_abs]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa only [wellRate, dif_pos ht] using hFarDG i t ht
    calc
      ‖rate t‖ ≤
          ‖P (S (Real.toNNReal t) (S.generator pt0))‖ +
            ‖∑ i : Fin m, (Q0 i) • wellRate i t‖ := by
              dsimp only [rate]
              simpa only [norm_neg] using
                (norm_add_le (-(P (S (Real.toNNReal t) (S.generator pt0))))
                  (∑ i : Fin m, (Q0 i) • wellRate i t))
      _ ≤ Ch := by
        dsimp only [Ch]
        exact add_le_add hPtBound hSumBound

#print axioms paper_A9_positive_time_semigroup_orbit_derivative
#print axioms paper_A9_physical_homogeneous_rate_from_initial_flux_and_DG

end ReservoirSeismicityControl.Paper2026
