import ReservoirSeismicityControl.Paper2026.PositiveSRReactionRate
import ReservoirSeismicityControl.SeismicityRateL2

/-!
# P3 / Appendix A.3: the actual A3 coefficient envelopes

The manuscript's Assumption 3 gives 0 <= gamma2 <= gamma2M,
|gamma2,t| <= Lgamma2t, 0 <= Rstar <= RstarM; Appendix A.2 (A7) gives
0 <= R <= RM. We specialize the already-verified pointwise reaction
inequalities to exactly those physical parameters.

In particular, the derivative envelope keeps |Rt(x,t)|, because (A7)
controls Rt in L2, NOT in L-infinity. The next, still open, step is the
paper's regional Holder estimate followed by its L2 applicability check.
No extra pointwise bound on Rt or time derivative of Q is introduced.
-/

namespace ReservoirSeismicityControl.Paper2026

/-- A3/A7 imply the three precise pointwise coefficient bounds used in
Appendix A.3. This instantiates the already proved logistic reaction
estimate rather than postulating an independent coefficient envelope. -/
theorem physical_sr_reaction_A3_three_coefficients
    (gamma2 gamma2Rate R Rstar : ℝ)
    (gamma2M Lgamma2t RM RstarM : ℝ)
    (hgamma20 : 0 ≤ gamma2) (hgamma2M : gamma2 ≤ gamma2M)
    (hgamma2Rate : |gamma2Rate| ≤ Lgamma2t)
    (hR0 : 0 ≤ R) (hRM : R ≤ RM)
    (hRstar0 : 0 ≤ Rstar) (hRstarM : Rstar ≤ RstarM) :
    |gamma2 * R * (R - Rstar)| ≤ gamma2M * RM * (RM + RstarM) ∧
    |gamma2Rate * R * (R - Rstar)| ≤ Lgamma2t * RM * (RM + RstarM) ∧
    |gamma2 * (2 * R - Rstar)| ≤ gamma2M * (2 * RM + RstarM) := by
  have hgamma2abs : |gamma2| ≤ gamma2M := by
    simpa [abs_of_nonneg hgamma20] using hgamma2M
  have hvalue :
      |gamma2 * R * (R - Rstar)| ≤
        gamma2M * RM * (RM + RstarM) :=
    ReservoirSeismicityControl.sr_reaction_pointwise_bound gamma2 R Rstar
      gamma2M RM RstarM hgamma2abs hR0 hRM hRstar0 hRstarM
  have hforcing :
      |gamma2Rate * R * (R - Rstar)| ≤
        Lgamma2t * RM * (RM + RstarM) :=
    ReservoirSeismicityControl.sr_reaction_pointwise_bound gamma2Rate R Rstar
      Lgamma2t RM RstarM hgamma2Rate hR0 hRM hRstar0 hRstarM
  have hmultAux := sr_reaction_integrand_rate_envelope
    gamma2 0 R Rstar 1 gamma2M 0 RM RstarM 1
    (le_trans hgamma20 hgamma2M) (by norm_num)
    (le_trans hR0 hRM) (le_trans hRstar0 hRstarM)
    hgamma2abs (by norm_num)
    (by simpa [abs_of_nonneg hR0] using hRM)
    (by simpa [abs_of_nonneg hRstar0] using hRstarM)
    (by norm_num)
  have hmult :
      |gamma2 * (2 * R - Rstar)| ≤
        gamma2M * (2 * RM + RstarM) := by
    simpa using hmultAux
  exact ⟨hvalue, hforcing, hmult⟩

/-- The precise A.3 pointwise rate inequality, with the L2-controlled
factor |Rt| retained. This does not assume an L-infinity bound on Rt.
The regional integral is treated using the paper's Holder step. -/
theorem physical_sr_reaction_A3_rate_envelope
    (gamma2 gamma2Rate R Rstar Rt : ℝ)
    (gamma2M Lgamma2t RM RstarM : ℝ)
    (hgamma20 : 0 ≤ gamma2) (hgamma2M : gamma2 ≤ gamma2M)
    (hgamma2Rate : |gamma2Rate| ≤ Lgamma2t)
    (hR0 : 0 ≤ R) (hRM : R ≤ RM)
    (hRstar0 : 0 ≤ Rstar) (hRstarM : Rstar ≤ RstarM) :
    |gamma2Rate * R * (R - Rstar) +
        gamma2 * (2 * R - Rstar) * Rt| ≤
      Lgamma2t * RM * (RM + RstarM) +
        gamma2M * (2 * RM + RstarM) * |Rt| := by
  obtain ⟨_, hforcing, hmult⟩ :=
    physical_sr_reaction_A3_three_coefficients
      gamma2 gamma2Rate R Rstar gamma2M Lgamma2t RM RstarM
      hgamma20 hgamma2M hgamma2Rate hR0 hRM hRstar0 hRstarM
  calc
    |gamma2Rate * R * (R - Rstar) +
        gamma2 * (2 * R - Rstar) * Rt| ≤
      |gamma2Rate * R * (R - Rstar)| +
        |gamma2 * (2 * R - Rstar) * Rt| := abs_add_le _ _
    _ = |gamma2Rate * R * (R - Rstar)| +
          |gamma2 * (2 * R - Rstar)| * |Rt| := by
      exact congrArg
        (fun x : ℝ => |gamma2Rate * R * (R - Rstar)| + x)
        (abs_mul (gamma2 * (2 * R - Rstar)) Rt)
    _ ≤ Lgamma2t * RM * (RM + RstarM) +
          gamma2M * (2 * RM + RstarM) * |Rt| :=
      add_le_add hforcing (mul_le_mul_of_nonneg_right hmult (abs_nonneg _))

end ReservoirSeismicityControl.Paper2026

#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_three_coefficients
#print axioms ReservoirSeismicityControl.Paper2026.physical_sr_reaction_A3_rate_envelope
