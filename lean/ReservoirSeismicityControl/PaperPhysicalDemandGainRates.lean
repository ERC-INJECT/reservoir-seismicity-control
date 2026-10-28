import ReservoirSeismicityControl.PaperPhysicalWellMatrixRates
import ReservoirSeismicityControl.PaperActualDemandGain
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.Matrix.Normed

/-!
# Stage 52: genuine matrix-valued derivatives of the physical demand gain

Stage 51 identifies the derivative of each well coefficient at regular times.
Here we assemble those scalar derivatives into the derivative of the *whole*
physical matrix `B(h(t))` and the allocated gain `B(h(t)) C_W`.  The argument
uses only the finitely many well means and constant demand allocator.  It is
valid almost everywhere, even for nonsmooth bounded well controls.

The final result is a precise entrywise upper bound for the gain derivative.
It is deliberately NOT claimed to be the Euclidean induced operator-norm
bound; that last estimate requires a matrix norm comparison.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix
open scoped Matrix.Norms.Elementwise

/-- An actual derivative of every scalar well mean gives an actual derivative
of the entire physical well matrix, including zero pressure-row rates. -/
theorem paper_physical_demand_matrix_hasDerivAt
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ) (t : ℝ)
    (hd : ∀ j : Fin w, HasDerivAt (fun s => h s j) (hRate t j) t) :
    HasDerivAt
      (fun s => paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h s) α κ)
      (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ) t := by
  apply (hasDerivAt_pi).2
  intro i
  apply (hasDerivAt_pi).2
  intro j
  cases i with
  | inl k =>
      simpa [paperPhysicalDemandWellMatrix] using
        (hasDerivAt_const t (α * Bᵤ₀ k j))
  | inr k =>
      change HasDerivAt
        (fun s : ℝ => κ * paperPhysicalSRWellMatrix
          wellRegion β volume (h s) k j)
        (κ * paperPhysicalSRWellMatrix
          wellRegion β volume (hRate t) k j) t
      exact (paper_physical_sr_entry_hasDerivAt
        wellRegion β volume h hRate t k j (hd j)).const_mul κ

/-- The actual derivative of the matrix is the explicitly computed physical
matrix, not a separately postulated candidate rate. -/
theorem paper_physical_demand_matrix_deriv
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ) (t : ℝ)
    (hd : ∀ j : Fin w, HasDerivAt (fun s => h s j) (hRate t j) t) :
    deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
      wellRegion β volume (h s) α κ) t =
      paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ := by
  exact (paper_physical_demand_matrix_hasDerivAt
    Bᵤ₀ wellRegion β volume h hRate α κ t hd).deriv

/-- Differentiation of the *allocated physical gain* `B(h(t)) C_W`.
The allocator is fixed, so no derivative of `C_W` or `Q` enters. -/
theorem paper_physical_demand_gain_hasDerivAt
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) (t : ℝ)
    (hd : ∀ j : Fin w, HasDerivAt (fun s => h s j) (hRate t j) t) :
    HasDerivAt
      (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (h s) α κ * C)
      (paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (hRate t) 0 κ * C) t := by
  let B : ℝ → Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    fun s => paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (h s) α κ
  let Bdot : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
    paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (hRate t) 0 κ
  have hB : HasDerivAt B Bdot t :=
    paper_physical_demand_matrix_hasDerivAt
      Bᵤ₀ wellRegion β volume h hRate α κ t hd
  have hentry (i : Sum (Fin u) (Fin r)) (k : Fin w) :
      HasDerivAt (fun s => B s i k) (Bdot i k) t :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i)) k
  apply (hasDerivAt_pi).2
  intro i
  apply (hasDerivAt_pi).2
  intro j
  change HasDerivAt
    (fun s : ℝ => ∑ k : Fin w, B s i k * C k j)
    (∑ k : Fin w, Bdot i k * C k j) t
  apply HasDerivAt.fun_sum
  intro k _
  exact (hentry i k).mul_const (C k j)

/-- The corresponding exact derivative identity for the physical gain. -/
theorem paper_physical_demand_gain_deriv
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ) (t : ℝ)
    (hd : ∀ j : Fin w, HasDerivAt (fun s => h s j) (hRate t j) t) :
    deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
      wellRegion β volume (h s) α κ * C) t =
      paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (hRate t) 0 κ * C := by
  exact (paper_physical_demand_gain_hasDerivAt
    Bᵤ₀ wellRegion β volume h hRate α κ C t hd).deriv

/-- The finitely many a.e. well-mean derivatives hold *simultaneously* at
almost every time. In particular there is one common null set on which
all entries of the physical gain may be differentiated. -/
theorem paper_physical_well_rates_common_ae
    {w : ℕ} (h hRate : ℝ → Fin w → ℝ)
    (hd : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t) :
    ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin w,
      HasDerivAt (fun s => h s j) (hRate t j) t := by
  exact Filter.eventually_all.mpr hd

/-- The physical demand gain has the displayed actual derivative for
almost every positive time. -/
theorem paper_physical_demand_gain_deriv_ae
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hd : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun s => h s j) (hRate t j) t) :
    ∀ᵐ t ∂paperPositiveTime,
      deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (h s) α κ * C) t =
      paperPhysicalDemandWellMatrix Bᵤ₀
        wellRegion β volume (hRate t) 0 κ * C := by
  filter_upwards [paper_physical_well_rates_common_ae h hRate hd] with t ht
  exact paper_physical_demand_gain_deriv
    Bᵤ₀ wellRegion β volume h hRate α κ C t ht

/-- An entry of the allocated gain rate is bounded by the finite sum of
absolute column contributions. This is an *entrywise* estimate, not an
operator-norm estimate. -/
theorem paper_physical_demand_gain_entry_rate_bound
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (t : ℝ) (hd : ∀ k : Fin w,
      HasDerivAt (fun s => h s k) (hRate t k) t)
    (i j : Sum (Fin u) (Fin r)) :
    |(deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
       wellRegion β volume (h s) α κ * C) t) i j| ≤
      ∑ k : Fin w,
        |(paperPhysicalDemandWellMatrix Bᵤ₀
           wellRegion β volume (hRate t) 0 κ) i k| * |C k j| := by
  rw [paper_physical_demand_gain_deriv
    Bᵤ₀ wellRegion β volume h hRate α κ C t hd]
  simp only [Matrix.mul_apply, dotProduct]
  calc
    |∑ k : Fin w,
       (paperPhysicalDemandWellMatrix Bᵤ₀
         wellRegion β volume (hRate t) 0 κ) i k * C k j| ≤
        ∑ k : Fin w, |(paperPhysicalDemandWellMatrix Bᵤ₀
          wellRegion β volume (hRate t) 0 κ) i k * C k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin w,
        |(paperPhysicalDemandWellMatrix Bᵤ₀
          wellRegion β volume (hRate t) 0 κ) i k| * |C k j| := by
      simp only [abs_mul]

end ReservoirSeismicityControl
