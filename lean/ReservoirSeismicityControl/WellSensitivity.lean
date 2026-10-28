import ReservoirSeismicityControl.DemandMatrixAction

/-!
# Finite well averages and sensitivity bounds (Appendix A.4)

This module connects the *finite-dimensional* matrix proof to the form of the
well-averaged seismicity sensitivities: a nonnegative, normalized weighted
average of local positive values `γ₁ R`.

It proves that uniform local positivity, upper bounds, and rate bounds pass
to the well averages. The weights may depend on the well, but are fixed in time.

IMPORTANT: These are finite weighted sums. They do not formalize integration
on three-dimensional well supports, the Neumann diffusion operator, or the
PDE estimates proving regularity of `R` and `R_t`. Those remain open.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- A finite spatially weighted well average. Row `i` contains the normalized
quadrature weights for well `i`. -/
def wellAverage {m n : ℕ}
    (w : Matrix (Fin m) (Fin n) ℝ)
    (field : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin n, w i j * field j

/-- Any normalized nonnegative well average preserves a pointwise interval. -/
theorem well_average_interval
    {m n : ℕ}
    (w : Matrix (Fin m) (Fin n) ℝ)
    (field : Fin n → ℝ)
    (lo hi : ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hnorm : ∀ i, (∑ j : Fin n, w i j) = 1)
    (hfield : ∀ j, lo ≤ field j ∧ field j ≤ hi)
    (i : Fin m) :
    lo ≤ wellAverage w field i ∧ wellAverage w field i ≤ hi := by
  change lo ≤ (∑ j : Fin n, w i j * field j) ∧
    (∑ j : Fin n, w i j * field j) ≤ hi
  constructor
  · calc
      lo = (∑ j : Fin n, w i j) * lo := by rw [hnorm i]; ring
      _ = ∑ j : Fin n, w i j * lo := by rw [Finset.sum_mul]
      _ ≤ ∑ j : Fin n, w i j * field j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hfield j).1 (hw i j)
  · calc
      (∑ j : Fin n, w i j * field j) ≤
          ∑ j : Fin n, w i j * hi := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hfield j).2 (hw i j)
      _ = (∑ j : Fin n, w i j) * hi := by rw [Finset.sum_mul]
      _ = hi := by rw [hnorm i]; ring

/-- Positive local `γ₁` and `R` values give bounds on their product. -/
theorem local_sr_sensitivity_interval
    {n : ℕ} (γ R : Fin n → ℝ)
    (γmin γmax Rmin Rmax : ℝ)
    (hγmin : 0 < γmin) (hRmin : 0 < Rmin)
    (hγ : ∀ j, γmin ≤ γ j ∧ γ j ≤ γmax)
    (hR : ∀ j, Rmin ≤ R j ∧ R j ≤ Rmax)
    (j : Fin n) :
    γmin * Rmin ≤ γ j * R j ∧ γ j * R j ≤ γmax * Rmax := by
  have hγ0 : 0 ≤ γ j := le_trans (le_of_lt hγmin) (hγ j).1
  have hR0 : 0 ≤ R j := le_trans (le_of_lt hRmin) (hR j).1
  have hRmax : 0 ≤ Rmax := le_trans hR0 (hR j).2
  constructor
  · have h1 : 0 ≤ (γ j - γmin) * R j :=
      mul_nonneg (sub_nonneg.mpr (hγ j).1) hR0
    have h2 : 0 ≤ γmin * (R j - Rmin) :=
      mul_nonneg (le_of_lt hγmin) (sub_nonneg.mpr (hR j).1)
    nlinarith only [h1, h2]
  · have h1 : 0 ≤ (γmax - γ j) * Rmax :=
      mul_nonneg (sub_nonneg.mpr (hγ j).2) hRmax
    have h2 : 0 ≤ γ j * (Rmax - R j) :=
      mul_nonneg hγ0 (sub_nonneg.mpr (hR j).2)
    nlinarith only [h1, h2]

/-- Finite-quadrature analogue of the positivity and boundedness of the
well sensitivities `h_j = |V_j*|⁻¹ ∫_(V_j*) γ₁ R`. -/
theorem well_sr_sensitivity_interval
    {m n : ℕ}
    (w : Matrix (Fin m) (Fin n) ℝ)
    (γ R : Fin n → ℝ)
    (γmin γmax Rmin Rmax : ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hnorm : ∀ i, (∑ j : Fin n, w i j) = 1)
    (hγmin : 0 < γmin) (hRmin : 0 < Rmin)
    (hγ : ∀ j, γmin ≤ γ j ∧ γ j ≤ γmax)
    (hR : ∀ j, Rmin ≤ R j ∧ R j ≤ Rmax)
    (i : Fin m) :
    γmin * Rmin ≤ wellAverage w (fun j => γ j * R j) i ∧
    wellAverage w (fun j => γ j * R j) i ≤ γmax * Rmax := by
  have hpoint : ∀ j, γmin * Rmin ≤ γ j * R j ∧
      γ j * R j ≤ γmax * Rmax := by
    intro j
    exact local_sr_sensitivity_interval γ R γmin γmax Rmin Rmax
      hγmin hRmin hγ hR j
  exact well_average_interval w (fun j => γ j * R j)
    (γmin * Rmin) (γmax * Rmax) hw hnorm hpoint i

/-- A normalized nonnegative average preserves a uniform absolute bound. -/
theorem well_average_abs_bound
    {m n : ℕ}
    (w : Matrix (Fin m) (Fin n) ℝ)
    (field : Fin n → ℝ) (L : ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hnorm : ∀ i, (∑ j : Fin n, w i j) = 1)
    (hfield : ∀ j, |field j| ≤ L)
    (i : Fin m) :
    |wellAverage w field i| ≤ L := by
  have hinterval : ∀ j, -L ≤ field j ∧ field j ≤ L := by
    intro j
    exact abs_le.mp (hfield j)
  exact abs_le.mpr
    (well_average_interval w field (-L) L hw hnorm hinterval i)

/-- If the nodal SR rates are bounded, the finite well-average rate
`∑ w_ij γ_j (R_t)_j` is uniformly bounded too. This statement concerns
the average of rates; identifying it with the derivative of the well
average in the PDE setting remains a separate analytic obligation. -/
theorem well_sr_rate_bound
    {m n : ℕ}
    (w : Matrix (Fin m) (Fin n) ℝ)
    (γ Rt : Fin n → ℝ) (γmax L : ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hnorm : ∀ i, (∑ j : Fin n, w i j) = 1)
    (hγ : ∀ j, 0 ≤ γ j ∧ γ j ≤ γmax)
    (hL : 0 ≤ L)
    (hRt : ∀ j, |Rt j| ≤ L)
    (i : Fin m) :
    |wellAverage w (fun j => γ j * Rt j) i| ≤ γmax * L := by
  have hlocal : ∀ j, |γ j * Rt j| ≤ γmax * L := by
    intro j
    rw [abs_mul, abs_of_nonneg (hγ j).1]
    exact (mul_le_mul_of_nonneg_left (hRt j) (hγ j).1).trans
      (mul_le_mul_of_nonneg_right (hγ j).2 hL)
  exact well_average_abs_bound w (fun j => γ j * Rt j) (γmax * L)
    hw hnorm hlocal i

end ReservoirSeismicityControl
