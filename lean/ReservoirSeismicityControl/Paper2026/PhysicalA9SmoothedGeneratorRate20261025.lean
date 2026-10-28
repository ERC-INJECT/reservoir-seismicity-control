import ReservoirSeismicityControl.Paper2026.PhysicalA9ClosedAnalyticKernel20261025
import MarkovProcess.Semigroup.Generator
import Mathlib.Tactic

/-!
# A9: positive-lag derivative of the actual generator orbit

This proves the rate of the smoothed generator orbit using two applications of
positive-time generator-domain smoothing and the already-proved semigroup
orbit derivative.  In particular the derivative is NOT assumed; no bounded
well-rate derivative is involved.

The sole analytic semigroup prerequisite is the familiar positive-time
smoothing property S(t)H ⊆ D(generator) for t>0.  The preceding physical A9
closed-kernel theorem obtains this property for actual L² wells from the
bounded analytic extension, graph closedness and domain approximation.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace

set_option maxHeartbeats 2000000

/-- Differentiate the generator of an analytic semigroup orbit directly from
positive-time smoothing.  This is stronger than differentiability of a
particular far-field observation: it gives the full-space vector derivative.
The proof uses the fixed splitting a=t/3 to stay inside the positive-time
neighbourhood, so it never differentiates the unbounded generator itself. -/
theorem paper_A9_actual_generator_orbit_rate_from_positive_smoothing
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    let a : ℝ := t / 3
    let u : S.generatorDomain :=
      ⟨S (Real.toNNReal a) f, hSmooth f a (by dsimp [a]; linarith)⟩
    let v : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (S.generator u),
        hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
    HasDerivAt
      (fun s : ℝ => if hs : 0 < s then
        S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩
        else 0)
      (S (Real.toNNReal (t - 2 * a)) (S.generator v)) t := by
  let a : ℝ := t / 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hta : 0 < t - 2 * a := by dsimp [a]; linarith
  let u : S.generatorDomain :=
    ⟨S (Real.toNNReal a) f, hSmooth f a ha⟩
  let v : S.generatorDomain :=
    ⟨S (Real.toNNReal a) (S.generator u), hSmooth (S.generator u) a ha⟩
  change HasDerivAt
    (fun s : ℝ => if hs : 0 < s then
      S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0)
    (S (Real.toNNReal (t - 2 * a)) (S.generator v)) t
  have hd : HasDerivAt
      (fun s : ℝ => S (Real.toNNReal (s - 2 * a)) (v : Lp ℝ 2 μ))
      (S (Real.toNNReal (t - 2 * a)) (S.generator v)) t := by
    have hOrbit := S.hasDerivAt_operator_toNNReal v hta
    have hTranslate : HasDerivAt (fun s : ℝ => s - 2 * a) 1 t := by
      convert (hasDerivAt_id t).sub_const (2 * a) using 1 <;> simp
    simpa only [Function.comp_def, one_smul] using hOrbit.scomp t hTranslate
  have hLocal :
      (fun s : ℝ => if hs : 0 < s then
        S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0)
      =ᶠ[𝓝 t]
      (fun s : ℝ => S (Real.toNNReal (s - 2 * a)) (v : Lp ℝ 2 μ)) := by
    have hneigh : t ∈ Set.Ioi (2 * a) := by
      change 2 * a < t
      linarith
    filter_upwards [isOpen_Ioi.mem_nhds hneigh] with s hs
    change 2 * a < s at hs
    have hspos : 0 < s := by linarith only [hs, ha]
    have hsa : 0 ≤ s - a := by linarith only [hs, ha]
    have hs2a : 0 ≤ s - 2 * a := by linarith only [hs]
    have htime1 : Real.toNNReal s =
        Real.toNNReal (s - a) + Real.toNNReal a := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ (le_of_lt hspos),
        Real.coe_toNNReal _ hsa, Real.coe_toNNReal _ ha.le]
      ring
    have htime2 : Real.toNNReal (s - a) =
        Real.toNNReal (s - 2 * a) + Real.toNNReal a := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hsa,
        Real.coe_toNNReal _ hs2a, Real.coe_toNNReal _ ha.le]
      ring
    have hsame :
        (⟨S (Real.toNNReal s) f, hSmooth f s hspos⟩ : S.generatorDomain) =
        ⟨S (Real.toNNReal (s - a)) (u : Lp ℝ 2 μ),
          S.operator_mem_generatorDomain u (Real.toNNReal (s - a))⟩ := by
      apply Subtype.ext
      change S (Real.toNNReal s) f =
        S (Real.toNNReal (s - a)) (S (Real.toNNReal a) f)
      rw [htime1, S.add_apply]
    have hgen :
        S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hspos⟩ =
          S (Real.toNNReal (s - 2 * a)) (v : Lp ℝ 2 μ) := by
      rw [hsame, S.generator_operator]
      change S (Real.toNNReal (s - a)) (S.generator u) =
        S (Real.toNNReal (s - 2 * a))
          (S (Real.toNNReal a) (S.generator u))
      rw [htime2, S.add_apply]
    simpa only [dif_pos hspos] using hgen
  exact hd.congr_of_eventuallyEq hLocal

/-- Projecting the physical generator derivative introduces no extra
regularity hypothesis. The derivative's sign is the sign of the physical
positive Neumann operator A=-generator, not the semigroup generator. -/
theorem paper_A9_projected_positive_generator_rate_from_smoothing
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℝ 2 μ))
    (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
      S (Real.toNNReal s) x ∈ S.generatorDomain)
    (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    let a : ℝ := t / 3
    let u : S.generatorDomain :=
      ⟨S (Real.toNNReal a) f, hSmooth f a (by dsimp [a]; linarith)⟩
    let v : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (S.generator u),
        hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
    HasDerivAt
      (fun s : ℝ => if hs : 0 < s then
        -(P (S.generator ⟨S (Real.toNNReal s) f,
          hSmooth f s hs⟩)) else 0)
      (-(P (S (Real.toNNReal (t - 2 * a)) (S.generator v)))) t := by
  let a : ℝ := t / 3
  have ha : 0 < a := by dsimp [a]; linarith
  let u : S.generatorDomain := ⟨S (Real.toNNReal a) f, hSmooth f a ha⟩
  let v : S.generatorDomain :=
    ⟨S (Real.toNNReal a) (S.generator u), hSmooth (S.generator u) a ha⟩
  change HasDerivAt
    (fun s : ℝ => if hs : 0 < s then
      -(P (S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩)) else 0)
    (-(P (S (Real.toNNReal (t - 2 * a)) (S.generator v)))) t
  have hraw := paper_A9_actual_generator_orbit_rate_from_positive_smoothing
    μ S hSmooth f t ht
  change HasDerivAt
    (fun s : ℝ => if hs : 0 < s then
      S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0)
    (S (Real.toNNReal (t - 2 * a)) (S.generator v)) t at hraw
  have hcomp := P.hasFDerivAt.comp_hasDerivAt t hraw
  change HasDerivAt
    (fun s : ℝ => P (if hs : 0 < s then
      S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0))
    (P (S (Real.toNNReal (t - 2 * a)) (S.generator v))) t at hcomp
  have hneg := hcomp.neg
  have heq :
      (fun s : ℝ => -P (if hs : 0 < s then
        S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0)) =
      (fun s : ℝ => if hs : 0 < s then
        -(P (S.generator ⟨S (Real.toNNReal s) f,
          hSmooth f s hs⟩)) else 0) := by
    funext s
    by_cases hs : 0 < s
    · simp only [dif_pos hs]
    · simp only [dif_neg hs, map_zero, neg_zero]
  change HasDerivAt
    (fun s : ℝ => -P (if hs : 0 < s then
      S.generator ⟨S (Real.toNNReal s) f, hSmooth f s hs⟩ else 0))
    (-(P (S (Real.toNNReal (t - 2 * a)) (S.generator v)))) t at hneg
  rw [heq] at hneg
  exact hneg

/-- Physical specialization: construct the canonical weak-Neumann orbit for
actual L² well profiles and DERIVE its far-projected lag derivative. The
positive-time smoothing assumption is the standard analytic semigroup
regularization, not a derivative-of-observation assumption.

The canonical orbit value and its generator identification are obtained from
our already passing A5/closed-kernel theorem. No unproved equality between
different pressure paths or generator realizations is introduced. -/
theorem paper_A9_canonical_L2_well_projected_lag_rate_from_smoothing
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (far : Set X) (hfar : MeasurableSet far)
    {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (j : U →L[ℝ] Lp ℝ 2 μ)
    (B₁ Eform : U →L[ℝ] U →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : U, B₁ x y = ⟪j x, j y⟫_ℝ + Eform x y)
    (hE : ∀ x : U, 0 ≤ Eform x x)
    (hSym₁ : ∀ x y : U, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    let S := ReservoirSeismicityControl.pressureNeumannGeneratedSemigroupOfDenseEmbedding
      j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
    let V : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range j.toLinearMap
    let Ew := ReservoirSeismicityControl.pressureA5CanonicalRangeEnergy j Eform hjinj
    let hsep := ReservoirSeismicityControl.pressure_A5_canonical_range_separates j hjinj hjDense
    let P := ReservoirSeismicityControl.paperFarLpProjection μ far hfar
    ∀ (m : ℕ) (f : Fin m → Lp ℝ 2 μ)
      (g : ℕ → Fin m → S.generatorDomain)
      (hg : ∀ i : Fin m, Tendsto
        (fun n : ℕ => (g n i : Lp ℝ 2 μ)) atTop (𝓝 (f i)))
      (T : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hAnalytic : ∀ (lag : ℝ), 0 < lag → ∀ u : S.generatorDomain,
        S (Real.toNNReal lag) (S.generator u) = T lag (u : Lp ℝ 2 μ))
      (Tfar : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
      (hFar : ∀ (lag : ℝ), 0 < lag → ∀ u : S.generatorDomain,
        P (S (Real.toNNReal lag) (S.generator u)) =
          Tfar lag (u : Lp ℝ 2 μ))
      (hSmooth : ∀ (x : Lp ℝ 2 μ) (s : ℝ), 0 < s →
        S (Real.toNNReal s) x ∈ S.generatorDomain),
      ∃ orbit : Fin m → ℝ → ReservoirSeismicityControl.pressureWeakNeumannDomain V Ew,
        (∀ (i : Fin m) (lag : ℝ), 0 < lag →
          (((orbit i lag : V) : Lp ℝ 2 μ)) =
            S (Real.toNNReal lag) (f i) ∧
          P (ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i lag)) =
            -(Tfar lag (f i))) ∧
        (∀ (i : Fin m) (lag : ℝ) (hlag : 0 < lag),
          let a : ℝ := lag / 3
          let u : S.generatorDomain :=
            ⟨S (Real.toNNReal a) (f i),
              hSmooth (f i) a (by dsimp [a]; linarith)⟩
          let v : S.generatorDomain :=
            ⟨S (Real.toNNReal a) (S.generator u),
              hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
          HasDerivAt
            (fun τ : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator
              V Ew hsep (orbit i τ))
            (-(S (Real.toNNReal (lag - 2 * a)) (S.generator v))) lag) ∧
        (∀ (i : Fin m) (lag : ℝ) (hlag : 0 < lag),
          let a : ℝ := lag / 3
          let u : S.generatorDomain :=
            ⟨S (Real.toNNReal a) (f i),
              hSmooth (f i) a (by dsimp [a]; linarith)⟩
          let v : S.generatorDomain :=
            ⟨S (Real.toNNReal a) (S.generator u),
              hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
          HasDerivAt
            (fun τ : ℝ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator
              V Ew hsep (orbit i τ)))
            (-(P (S (Real.toNNReal (lag - 2 * a)) (S.generator v)))) lag) := by
  classical
  intro S V Ew hsep P m f g hg T hAnalytic Tfar hFar hSmooth
  obtain ⟨orbit, hOrbitValue⟩ :=
    paper_A9_canonical_physical_L2_kernel_from_closed_smoothing
      μ far hfar j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense
      m f g hg T hAnalytic Tfar hFar
  have hActualValue (i : Fin m) (s : ℝ) (hs : 0 < s) :
      ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i s) =
        -(S.generator ⟨S (Real.toNNReal s) (f i),
          hSmooth (f i) s hs⟩) := by
    have hc := (hOrbitValue i s hs).1
    have hdom : (((orbit i s : V) : Lp ℝ 2 μ)) ∈ S.generatorDomain := by
      rw [hc]
      exact hSmooth (f i) s hs
    have hweak :=
      ReservoirSeismicityControl.pressure_A5_canonical_range_operator_eq_neg_generator
        j B₁ Eform hB₁ hForm₁ hE hSym₁ hjinj hjDense (orbit i s) hdom
    have hsame :
        (⟨(((orbit i s : V) : Lp ℝ 2 μ)), hdom⟩ : S.generatorDomain) =
        (⟨S (Real.toNNReal s) (f i), hSmooth (f i) s hs⟩ :
          S.generatorDomain) := Subtype.ext hc
    calc
      ReservoirSeismicityControl.pressureWeakNeumannOperator V Ew hsep (orbit i s) =
        -(S.generator ⟨(((orbit i s : V) : Lp ℝ 2 μ)), hdom⟩) := hweak
      _ = -(S.generator ⟨S (Real.toNNReal s) (f i),
            hSmooth (f i) s hs⟩) := by rw [hsame]
  have hFullRate (i : Fin m) (lag : ℝ) (hlag : 0 < lag) :
      let a : ℝ := lag / 3
      let u : S.generatorDomain :=
        ⟨S (Real.toNNReal a) (f i),
          hSmooth (f i) a (by dsimp [a]; linarith)⟩
      let v : S.generatorDomain :=
        ⟨S (Real.toNNReal a) (S.generator u),
          hSmooth (S.generator u) a (by dsimp [a]; linarith)⟩
      HasDerivAt
        (fun τ : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator
          V Ew hsep (orbit i τ))
        (-(S (Real.toNNReal (lag - 2 * a)) (S.generator v))) lag := by
    let a : ℝ := lag / 3
    have ha : 0 < a := by dsimp [a]; linarith
    let u : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (f i), hSmooth (f i) a ha⟩
    let v : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (S.generator u), hSmooth (S.generator u) a ha⟩
    change HasDerivAt
      (fun τ : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator
        V Ew hsep (orbit i τ))
      (-(S (Real.toNNReal (lag - 2 * a)) (S.generator v))) lag
    have hraw := paper_A9_actual_generator_orbit_rate_from_positive_smoothing
      μ S hSmooth (f i) lag hlag
    change HasDerivAt
      (fun τ : ℝ => if hτ : 0 < τ then
        S.generator ⟨S (Real.toNNReal τ) (f i), hSmooth (f i) τ hτ⟩
        else 0)
      (S (Real.toNNReal (lag - 2 * a)) (S.generator v)) lag at hraw
    have hneg := hraw.neg
    have hlocal :
        (fun τ : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator
          V Ew hsep (orbit i τ)) =ᶠ[𝓝 lag]
        (fun τ : ℝ => -(if hτ : 0 < τ then
          S.generator ⟨S (Real.toNNReal τ) (f i), hSmooth (f i) τ hτ⟩
          else 0)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hlag] with τ hτ
      change 0 < τ at hτ
      simpa [hτ] using (hActualValue i τ hτ)
    exact hneg.congr_of_eventuallyEq hlocal
  refine ⟨orbit, hOrbitValue, ?_, ?_⟩
  · exact hFullRate
  · intro i lag hlag
    have hraw := hFullRate i lag hlag
    let a : ℝ := lag / 3
    have ha : 0 < a := by dsimp [a]; linarith
    let u : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (f i), hSmooth (f i) a ha⟩
    let v : S.generatorDomain :=
      ⟨S (Real.toNNReal a) (S.generator u), hSmooth (S.generator u) a ha⟩
    change HasDerivAt
      (fun τ : ℝ => ReservoirSeismicityControl.pressureWeakNeumannOperator
        V Ew hsep (orbit i τ))
      (-(S (Real.toNNReal (lag - 2 * a)) (S.generator v))) lag at hraw
    have hp := P.hasFDerivAt.comp_hasDerivAt lag hraw
    change HasDerivAt
      (fun τ : ℝ => P (ReservoirSeismicityControl.pressureWeakNeumannOperator
        V Ew hsep (orbit i τ)))
      (P (-(S (Real.toNNReal (lag - 2 * a)) (S.generator v)))) lag at hp
    simpa only [map_neg] using hp

#print axioms paper_A9_actual_generator_orbit_rate_from_positive_smoothing
#print axioms paper_A9_projected_positive_generator_rate_from_smoothing
#print axioms paper_A9_canonical_L2_well_projected_lag_rate_from_smoothing

end ReservoirSeismicityControl.Paper2026
