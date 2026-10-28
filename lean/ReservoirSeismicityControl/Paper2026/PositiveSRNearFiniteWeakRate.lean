import ReservoirSeismicityControl.Paper2026.PositivePressureNearFiniteDerivative
import ReservoirSeismicityControl.Paper2026.PositiveSRNearWeakBound
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: finite SR near-field weak-rate expression

For each SR region the previously verified `paper_sr_near_weak_rate_rhs_bound`
bounds the TWO terms in (A.3), with the actual time-dependent normalized SR
weight. We assemble those expressions in the paper's canonical SR coordinates.
No independent bound on the finite SR near rate is postulated.

IMPORTANT: this is a bound on the proposed WEAK derivative expression, not a
proof that the observation itself has this weak derivative. The cited weak
integration-by-parts/product rule, the local H² -> D(A) applicability and
far-field Davies--Gaffney applicability remain open, as recorded in the ledger.
In particular there is NO differentiation of A p or of Q in this module.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The SR-coordinate part of the weak near-field A.3 rate expression,
with exactly the same sign as the diffusion part of the paper's Psi. -/
noncomputable def paperPhysicalSRNearWeakRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X) (regions : Fin r → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R Rdot : ℝ → Lp ℝ 2 mu) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hWeightD : ∀ i t, paperSRNearDiffusionWeight mu (regions i)
      (hMeas i) Kgamma R gamma10 R0star cutoff t ∈ D)
    (Ap pressureRate : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  ∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i
    (-(⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
         Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
       ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
         Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
         pressureRate t⟫_ℝ))

/-- The paper's A.3 bounds give the finite-dimensional near SR *rate
expression* bound. The only near elliptic conditions are on the actual
localized SR weights. The strong Rdot bounds are those already proved in P2.
No separate SR near rate-vector estimate is assumed. -/
theorem paper_physical_sr_near_weak_rate_finite_bound
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X) (regions : Fin r → Set X)
    (hMeas : ∀ i, MeasurableSet (regions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R Rdot : ℝ → Lp ℝ 2 mu)
    (gamma10 R0star Cgamma CR MR : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hCgamma : 0 ≤ Cgamma) (hK : ‖Kgamma‖ ≤ Cgamma)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hWeightD : ∀ i t, paperSRNearDiffusionWeight mu (regions i)
      (hMeas i) Kgamma R gamma10 R0star cutoff t ∈ D)
    (CAw : Fin r → ℝ) (CAp CPt : ℝ)
    (hAw : ∀ i t, ‖A ⟨paperSRNearDiffusionWeight mu (regions i)
      (hMeas i) Kgamma R gamma10 R0star cutoff t,
      hWeightD i t⟩‖ ≤ CAw i)
    (Ap pressureRate : ℝ → Lp ℝ 2 mu)
    (hAp : ∀ t, ‖Ap t‖ ≤ CAp)
    (hpRate : ∀ t, ‖pressureRate t‖ ≤ CPt) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖paperPhysicalSRNearWeakRate (u := u) (r := r) mu regions hMeas
          Kgamma R Rdot gamma10 R0star cutoff D A hWeightD
          Ap pressureRate t‖ ≤
        ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
          ((‖cutoff‖ *
            (|1 / (gamma10 * R0star * mu.real (regions i))| *
              (Cgamma * CR))) * CAp + CAw i * CPt) := by
  classical
  let B : Fin r → ℝ := fun i =>
    (‖cutoff‖ *
      (|1 / (gamma10 * R0star * mu.real (regions i))| *
        (Cgamma * CR))) * CAp + CAw i * CPt
  have hRegion (i : Fin r) :
      ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
        |⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
            Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
          ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
              Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
            pressureRate t⟫_ℝ| ≤ B i := by
    exact paper_sr_near_weak_rate_rhs_bound mu (regions i) (hMeas i)
      Kgamma R Rdot gamma10 R0star Cgamma CR MR cutoff
      hCgamma hK hR hderiv hrate D A (hWeightD i) (CAw i) CAp CPt
      (hAw i) Ap pressureRate hAp hpRate
  have hAll : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ∀ i : Fin r,
        |⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
            Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
          ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
              Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
            pressureRate t⟫_ℝ| ≤ B i := by
    have hFinite (s : Finset (Fin r)) :
        ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ∀ i ∈ s,
          |⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
              Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
            ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
                Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
              pressureRate t⟫_ℝ| ≤ B i := by
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with t
          simp
      | @insert a s ha ih =>
          filter_upwards [hRegion a, ih] with t hat hst i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hat
          · exact hst i his
    filter_upwards [hFinite Finset.univ] with t ht i
    exact ht i (Finset.mem_univ i)
  filter_upwards [hAll] with t ht
  let q : Fin r → ℝ := fun i =>
    -(⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
        Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
      ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
        Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
        pressureRate t⟫_ℝ)
  have hq (i : Fin r) : |q i| ≤ B i := by
    change abs (-(⟪cutoff (paperSRDiffusionWeightRate mu (regions i) (hMeas i)
          Kgamma Rdot gamma10 R0star t), Ap t⟫_ℝ +
        ⟪A ⟨paperSRNearDiffusionWeight mu (regions i) (hMeas i)
          Kgamma R gamma10 R0star cutoff t, hWeightD i t⟩,
          pressureRate t⟫_ℝ)) ≤ B i
    rw [abs_neg]
    exact ht i
  change ‖∑ i : Fin r, paperSRCoordinateEmbed (u := u) (r := r) i (q i)‖ ≤ _
  calc
    _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i (q i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * |q i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        (paperSRCoordinateEmbed (u := u) (r := r) i).le_opNorm (q i)
    _ ≤ ∑ i : Fin r, ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ * B i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hq i) (norm_nonneg _)


/-- Complete *candidate* near-field rate of the physical perturbation (14).
The pressure contribution is an already verified strong a.e. derivative;
for the moving SR contribution, the paper's weak product-rule applicability
remains to be justified. This definition itself assumes no derivative. -/
noncomputable def paperPhysicalFiniteNearWeakRate
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X)
    (pressureRegions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pressureRegions i))
    (hpFin : ∀ i, mu (pressureRegions i) ≠ ⊤)
    (srRegions : Fin r → Set X)
    (hsMeas : ∀ i, MeasurableSet (srRegions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R Rdot : ℝ → Lp ℝ 2 mu) (gamma10 R0star : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hPressureWeightD : ∀ i, paperPressureNearWeight mu
      (pressureRegions i) (hpMeas i) (hpFin i) cutoff ∈ D)
    (hSRWeightD : ∀ i t, paperSRNearDiffusionWeight mu
      (srRegions i) (hsMeas i) Kgamma R gamma10 R0star cutoff t ∈ D)
    (Ap pressureRate : ℝ → Lp ℝ 2 mu) (t : ℝ) :
    EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
  paperPhysicalPressureNearRate (u := u) (r := r) mu
    pressureRegions hpMeas hpFin cutoff D A hPressureWeightD pressureRate t +
  paperPhysicalSRNearWeakRate (u := u) (r := r) mu
    srRegions hsMeas Kgamma R Rdot gamma10 R0star cutoff
    D A hSRWeightD Ap pressureRate t

/-- Assemble the independently verified fixed-pressure derivative and
physical SR weak-rate RHS bounds into one quantitative estimate in the
canonical output coordinates. NO derivative of the moving SR observation
is claimed. Domain and generator bounds are exactly the applicability
conditions of Appendix A.3's cited local elliptic theorem. -/
theorem paper_physical_finite_near_weak_rate_bound
    {X : Type*} [MeasurableSpace X] {u r : ℕ}
    (mu : Measure X)
    (pressureRegions : Fin u → Set X)
    (hpMeas : ∀ i, MeasurableSet (pressureRegions i))
    (hpFin : ∀ i, mu (pressureRegions i) ≠ ⊤)
    (srRegions : Fin r → Set X)
    (hsMeas : ∀ i, MeasurableSet (srRegions i))
    (Kgamma : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (R Rdot : ℝ → Lp ℝ 2 mu)
    (gamma10 R0star Cgamma CR MR : ℝ)
    (cutoff : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hCgamma : 0 ≤ Cgamma) (hK : ‖Kgamma‖ ≤ Cgamma)
    (hR : ∀ t, ‖R t‖ ≤ MR)
    (hRderiv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt R (Rdot t) t)
    (hRrate : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime), ‖Rdot t‖ ≤ CR)
    (D : Submodule ℝ (Lp ℝ 2 mu))
    (A : D →ₗ[ℝ] Lp ℝ 2 mu)
    (hSymm : ∀ a b : D,
      ⟪A a, (b : Lp ℝ 2 mu)⟫_ℝ = ⟪(a : Lp ℝ 2 mu), A b⟫_ℝ)
    (pressure pressureRate : ℝ → Lp ℝ 2 mu)
    (hpD : ∀ t, pressure t ∈ D)
    (hPressureWeightD : ∀ i, paperPressureNearWeight mu
      (pressureRegions i) (hpMeas i) (hpFin i) cutoff ∈ D)
    (hSRWeightD : ∀ i t, paperSRNearDiffusionWeight mu
      (srRegions i) (hsMeas i) Kgamma R gamma10 R0star cutoff t ∈ D)
    (CAwPressure : Fin u → ℝ) (CAwSR : Fin r → ℝ)
    (CAp CPt : ℝ)
    (hAwPressure : ∀ i, ‖A ⟨paperPressureNearWeight mu
      (pressureRegions i) (hpMeas i) (hpFin i) cutoff,
      hPressureWeightD i⟩‖ ≤ CAwPressure i)
    (hAwSR : ∀ i t, ‖A ⟨paperSRNearDiffusionWeight mu
      (srRegions i) (hsMeas i) Kgamma R gamma10 R0star cutoff t,
      hSRWeightD i t⟩‖ ≤ CAwSR i)
    (hpDeriv : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt pressure (pressureRate t) t)
    (hPt : ∀ t, ‖pressureRate t‖ ≤ CPt)
    (hAp : ∀ t, ‖A ⟨pressure t, hpD t⟩‖ ≤ CAp) :
    ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      HasDerivAt
        (paperPhysicalPressureNearPsi (u := u) (r := r) mu
          pressureRegions hpMeas hpFin cutoff
          (fun τ => A ⟨pressure τ, hpD τ⟩))
        (paperPhysicalPressureNearRate (u := u) (r := r) mu
          pressureRegions hpMeas hpFin cutoff D A hPressureWeightD
          pressureRate t) t ∧
      ‖paperPhysicalFiniteNearWeakRate (u := u) (r := r) mu
          pressureRegions hpMeas hpFin srRegions hsMeas
          Kgamma R Rdot gamma10 R0star cutoff D A
          hPressureWeightD hSRWeightD
          (fun τ => A ⟨pressure τ, hpD τ⟩) pressureRate t‖ ≤
        (∑ i : Fin u,
          ‖paperPressureCoordinateEmbed (u := u) (r := r) i‖ *
            (CAwPressure i * CPt)) +
        (∑ i : Fin r,
          ‖paperSRCoordinateEmbed (u := u) (r := r) i‖ *
            ((‖cutoff‖ *
              (|1 / (gamma10 * R0star * mu.real (srRegions i))| *
                (Cgamma * CR))) * CAp + CAwSR i * CPt)) := by
  classical
  have hPtAE : ∀ᵐ t ∂(ReservoirSeismicityControl.paperPositiveTime),
      ‖pressureRate t‖ ≤ CPt := Filter.Eventually.of_forall hPt
  have hPressure := paper_physical_pressure_near_finite_derivative_ae
    (u := u) (r := r) mu pressureRegions hpMeas hpFin
    cutoff D A hSymm pressure pressureRate hpD
    hPressureWeightD CAwPressure CPt hAwPressure hpDeriv hPtAE
  have hSR := paper_physical_sr_near_weak_rate_finite_bound
    (u := u) (r := r) mu srRegions hsMeas Kgamma R Rdot
    gamma10 R0star Cgamma CR MR cutoff hCgamma hK hR
    hRderiv hRrate D A hSRWeightD CAwSR CAp CPt
    hAwSR (fun τ => A ⟨pressure τ, hpD τ⟩) pressureRate hAp hPt
  filter_upwards [hPressure, hSR] with t htP htSR
  constructor
  · exact htP.1
  · change ‖paperPhysicalPressureNearRate (u := u) (r := r)
        mu pressureRegions hpMeas hpFin cutoff D A hPressureWeightD pressureRate t +
      paperPhysicalSRNearWeakRate (u := u) (r := r) mu srRegions hsMeas
        Kgamma R Rdot gamma10 R0star cutoff D A hSRWeightD
        (fun τ => A ⟨pressure τ, hpD τ⟩) pressureRate t‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add htP.2 htSR)

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_sr_near_weak_rate_finite_bound

#print axioms ReservoirSeismicityControl.Paper2026.paper_physical_finite_near_weak_rate_bound
