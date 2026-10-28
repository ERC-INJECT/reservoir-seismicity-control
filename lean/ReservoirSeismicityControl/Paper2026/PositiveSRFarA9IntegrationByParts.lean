import ReservoirSeismicityControl.Paper2026.PositiveSRFarA9ZeroBoundary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# P3 / Appendix A.3 (A9): actual smooth-flux integration by parts

This module proves the displayed integration-by-parts identity in the paper
for smooth well fluxes Q, with the kernel's zero-lag endpoint obtained from
the previously verified A8 -> A9 zero extension.

The kernel is differentiated in its lag (not observation time), with
`d/ds K(t-s) = -K'(t-s)` on the interior of the causal interval.
The result removes Q' from the resulting *formula*. Extension from smooth
fluxes to general bounded measurable Q and identification of the physical
far observation with the mild semigroup formula are distinct P3 obligations.
No Davies--Gaffney or semigroup theorem is reproved.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory

/-- The exact paper (A9) integration-by-parts identity for a causal
    kernel with K(0)=0 and a smooth input. Its derivative in the convolution
    is the LAG derivative, as in (A8). -/
theorem paper_A9_smooth_flux_integration_by_parts
    (K KRate Q QRate : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hKzero : K 0 = 0)
    (hKcont : ContinuousOn (fun s : ℝ => K (t - s)) (Set.uIcc 0 t))
    (hQcont : ContinuousOn Q (Set.uIcc 0 t))
    (hKderiv : ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt (fun x : ℝ => K (t - x)) (-KRate (t - s)) s)
    (hQderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt Q (QRate s) s)
    (hKint : IntervalIntegrable
      (fun s : ℝ => -KRate (t - s)) volume 0 t)
    (hQint : IntervalIntegrable QRate volume 0 t) :
    (∫ s in (0 : ℝ)..t, K (t - s) * QRate s) =
      -(K t * Q 0) +
        ∫ s in (0 : ℝ)..t, KRate (t - s) * Q s := by
  have hKinterior :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) t) (max (0 : ℝ) t),
        HasDerivAt (fun x : ℝ => K (t - x)) (-KRate (t - s)) s := by
    simpa only [min_eq_left ht, max_eq_right ht] using hKderiv
  have hQinterior :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) t) (max (0 : ℝ) t),
        HasDerivAt Q (QRate s) s := by
    simpa only [min_eq_left ht, max_eq_right ht] using hQderiv
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := (0 : ℝ)) (b := t)
      (u := fun s : ℝ => K (t - s)) (v := Q)
      (u' := fun s : ℝ => -KRate (t - s)) (v' := QRate)
      hKcont hQcont hKinterior hQinterior hKint hQint
  have hnegative :
      (∫ s in (0 : ℝ)..t, (-KRate (t - s)) * Q s) =
        -(∫ s in (0 : ℝ)..t, KRate (t - s) * Q s) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  calc
    (∫ s in (0 : ℝ)..t, K (t - s) * QRate s) =
        K (t - t) * Q t - K (t - 0) * Q 0 -
          (∫ s in (0 : ℝ)..t, (-KRate (t - s)) * Q s) := hparts
    _ = -(K t * Q 0) +
        ∫ s in (0 : ℝ)..t, KRate (t - s) * Q s := by
          rw [sub_self, sub_zero, hKzero, hnegative]
          ring

/-- Apply A9's proved zero-lag extension to the smooth-input formula.
    No independent physical K(0)=0 hypothesis appears. -/
theorem paper_A9_smooth_flux_zero_extension
    (K KRate Q QRate : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hKcont : ContinuousOn
      (fun s : ℝ => paperA9ZeroLagExtension K (t - s)) (Set.uIcc 0 t))
    (hQcont : ContinuousOn Q (Set.uIcc 0 t))
    (hKderiv : ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt (fun x : ℝ => paperA9ZeroLagExtension K (t - x))
        (-KRate (t - s)) s)
    (hQderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt Q (QRate s) s)
    (hKint : IntervalIntegrable
      (fun s : ℝ => -KRate (t - s)) volume 0 t)
    (hQint : IntervalIntegrable QRate volume 0 t) :
    (∫ s in (0 : ℝ)..t,
      paperA9ZeroLagExtension K (t - s) * QRate s) =
      -(paperA9ZeroLagExtension K t * Q 0) +
        ∫ s in (0 : ℝ)..t, KRate (t - s) * Q s := by
  exact paper_A9_smooth_flux_integration_by_parts
    (paperA9ZeroLagExtension K) KRate Q QRate t ht
    (paper_A9_zero_extension_at_zero K)
    hKcont hQcont hKderiv hQderiv hKint hQint

/-- The finite-well version is *exactly* the causal expression in the
    existing `paperFarCausalKernelRate`, with no Q' on the right. -/
theorem paper_A9_smooth_multiwell_causal_identity
    {n : ℕ} (K KRate Q QRate : Fin n → ℝ → ℝ)
    (t initial : ℝ) (ht : 0 ≤ t)
    (hKcont : ∀ j : Fin n, ContinuousOn
      (fun s : ℝ => paperA9ZeroLagExtension (K j) (t - s)) (Set.uIcc 0 t))
    (hQcont : ∀ j : Fin n, ContinuousOn (Q j) (Set.uIcc 0 t))
    (hKderiv : ∀ j : Fin n, ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt (fun x : ℝ => paperA9ZeroLagExtension (K j) (t - x))
        (-KRate j (t - s)) s)
    (hQderiv : ∀ j : Fin n, ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt (Q j) (QRate j s) s)
    (hKint : ∀ j : Fin n, IntervalIntegrable
      (fun s : ℝ => -KRate j (t - s)) volume 0 t)
    (hQint : ∀ j : Fin n, IntervalIntegrable (QRate j) volume 0 t) :
    initial + ∑ j : Fin n,
        (∫ s in (0 : ℝ)..t,
          paperA9ZeroLagExtension (K j) (t - s) * QRate j s) =
      ReservoirSeismicityControl.paperFarCausalKernelRate t initial
        (fun j lag => paperA9ZeroLagExtension (K j) lag) KRate Q := by
  have hsum :
      (∑ j : Fin n,
        ∫ s in (0 : ℝ)..t,
          paperA9ZeroLagExtension (K j) (t - s) * QRate j s) =
      ∑ j : Fin n,
        (-(paperA9ZeroLagExtension (K j) t * Q j 0) +
          ∫ s in (0 : ℝ)..t, KRate j (t - s) * Q j s) := by
    apply Finset.sum_congr rfl
    intro j _
    exact paper_A9_smooth_flux_zero_extension
      (K j) (KRate j) (Q j) (QRate j) t ht
      (hKcont j) (hQcont j) (hKderiv j) (hQderiv j)
      (hKint j) (hQint j)
  rw [hsum]
  simp only [intervalIntegral.integral_of_le ht, ReservoirSeismicityControl.paperFarCausalKernelRate]

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_integration_by_parts
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_flux_zero_extension
#print axioms ReservoirSeismicityControl.Paper2026.paper_A9_smooth_multiwell_causal_identity
