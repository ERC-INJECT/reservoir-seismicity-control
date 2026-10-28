import ReservoirSeismicityControl.Paper2026.PositiveDemandP3References
import Mathlib.Tactic

/-!
# P3 / Appendix A.3: signed SR reaction differentiation and bound

The signed SR perturbation has reaction integrand
  gamma2(t,x) * R(t,x) * (R(t,x) - Rstar(x)),
with the fixed SR normalization `-s/(gamma10 * R0star)`.

The two statements below verify exactly the pointwise product rule and
its absolute-value envelope used on printed page 27 of the manuscript.
They require only the time derivatives and bounds in Assumption 3 and (A7).

The next step is the spatial L1/L2 integral estimate and its differentiation
under the integral (the paper's cited standard analytic theorem). We do NOT
postulate a theorem asserting bounded regional reaction derivatives.
No spatial dimension or specific value of the SR sign is assumed here.
-/

namespace ReservoirSeismicityControl.Paper2026

/-- A.3, pointwise time derivative of the actual SR reaction integrand.
The background `Rstar` is time independent, exactly as in the paper. -/
theorem sr_reaction_integrand_hasDerivAt
    (gamma2 R : ℝ → ℝ) (Rstar gamma2Rate RRate t : ℝ)
    (hgamma : HasDerivAt gamma2 gamma2Rate t)
    (hR : HasDerivAt R RRate t) :
    HasDerivAt
      (fun τ => gamma2 τ * R τ * (R τ - Rstar))
      (gamma2Rate * R t * (R t - Rstar) +
        gamma2 t * (2 * R t - Rstar) * RRate) t := by
  have hconst : HasDerivAt (fun _ : ℝ => Rstar) 0 t :=
    hasDerivAt_const t Rstar
  convert (hgamma.mul hR).mul (hR.sub hconst) using 1 <;>
    (simp only [Pi.sub_apply, Pi.mul_apply] <;> ring)

/-- The exact *pointwise* envelope used in Appendix A.3 (before the
finite-volume/Hölder step). The SR sign does not enter the absolute bound. -/
theorem sr_reaction_integrand_rate_envelope
    (gamma2 gamma2Rate R Rstar RRate : ℝ)
    (G GRate RM RstarM RRateM : ℝ)
    (hG0 : 0 ≤ G) (hGRate0 : 0 ≤ GRate)
    (hRM0 : 0 ≤ RM) (hRstarM0 : 0 ≤ RstarM)
    (hG : |gamma2| ≤ G)
    (hGRate : |gamma2Rate| ≤ GRate)
    (hR : |R| ≤ RM)
    (hRstar : |Rstar| ≤ RstarM)
    (hRRate : |RRate| ≤ RRateM) :
    |gamma2Rate * R * (R - Rstar) +
        gamma2 * (2 * R - Rstar) * RRate| ≤
      GRate * RM * (RM + RstarM) +
        G * (2 * RM + RstarM) * RRateM := by
  have hRdiff : |R - Rstar| ≤ RM + RstarM := by
    calc
      |R - Rstar| ≤ |R| + |Rstar| := abs_sub _ _
      _ ≤ RM + RstarM := add_le_add hR hRstar
  have hR2diff : |2 * R - Rstar| ≤ 2 * RM + RstarM := by
    calc
      |2 * R - Rstar| ≤ |2 * R| + |Rstar| := abs_sub _ _
      _ = 2 * |R| + |Rstar| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * RM + RstarM :=
        add_le_add (mul_le_mul_of_nonneg_left hR (by norm_num)) hRstar
  have hGR : |gamma2Rate| * |R| ≤ GRate * RM := by
    calc
      |gamma2Rate| * |R| ≤ GRate * |R| :=
        mul_le_mul_of_nonneg_right hGRate (abs_nonneg _)
      _ ≤ GRate * RM := mul_le_mul_of_nonneg_left hR hGRate0
  have hpart1 :
      |gamma2Rate| * |R| * |R - Rstar| ≤
        GRate * RM * (RM + RstarM) := by
    calc
      _ ≤ GRate * RM * |R - Rstar| :=
        mul_le_mul_of_nonneg_right hGR (abs_nonneg _)
      _ ≤ GRate * RM * (RM + RstarM) :=
        mul_le_mul_of_nonneg_left hRdiff
          (mul_nonneg hGRate0 hRM0)
  have hsumNonneg : 0 ≤ 2 * RM + RstarM :=
    add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRM0) hRstarM0
  have hG2R : |gamma2| * |2 * R - Rstar| ≤
      G * (2 * RM + RstarM) := by
    calc
      _ ≤ G * |2 * R - Rstar| :=
        mul_le_mul_of_nonneg_right hG (abs_nonneg _)
      _ ≤ G * (2 * RM + RstarM) :=
        mul_le_mul_of_nonneg_left hR2diff hG0
  have hpart2 :
      |gamma2| * |2 * R - Rstar| * |RRate| ≤
        G * (2 * RM + RstarM) * RRateM := by
    calc
      _ ≤ G * (2 * RM + RstarM) * |RRate| :=
        mul_le_mul_of_nonneg_right hG2R (abs_nonneg _)
      _ ≤ G * (2 * RM + RstarM) * RRateM :=
        mul_le_mul_of_nonneg_left hRRate
          (mul_nonneg hG0 hsumNonneg)
  calc
    |gamma2Rate * R * (R - Rstar) +
        gamma2 * (2 * R - Rstar) * RRate| ≤
      |gamma2Rate * R * (R - Rstar)| +
        |gamma2 * (2 * R - Rstar) * RRate| := abs_add_le _ _
    _ = |gamma2Rate| * |R| * |R - Rstar| +
        |gamma2| * |2 * R - Rstar| * |RRate| := by
          simp only [abs_mul]
    _ ≤ GRate * RM * (RM + RstarM) +
          G * (2 * RM + RstarM) * RRateM :=
        add_le_add hpart1 hpart2

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_hasDerivAt
#print axioms ReservoirSeismicityControl.Paper2026.sr_reaction_integrand_rate_envelope
