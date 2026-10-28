import ReservoirSeismicityControl.PaperPhysicalDemandGainRates
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Stage 53: genuine induced Euclidean gain-rate bounds

The physical SR sensitivity is linear in each well mean h_j.  In particular,
its *rate matrix* factors as a fixed geometry matrix times the diagonal
matrix of the actual scalar well-mean rates:

  B_rate(hdot) = B_rate(1) * diagonal(hdot).

Unlike an entrywise matrix estimate, this factorization supplies the actual
induced Euclidean (l2) operator norm via submultiplicativity.  The controller
allocator C_W is constant, hence

  norm_2(Gdot_W) <= norm_2(B_rate(1)) * sup_j |hdot_j| * norm_2(C_W).

The derivative is the actual derivative established in Stage 52.  Since the
individual rate estimates are a.e., the final statement is also a.e.

No derivative of Q is used.  The assumptions about the SR/L2 trajectory are
those already documented in Stage 50; the only analytic hypotheses in the
final theorem are the corresponding scalar differentiability and rate bounds.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The fixed well-geometry matrix used in the gain-rate factorization.
Its pressure block is zero, while its SR rows retain all regional supports,
physical volumes and the fixed scalar κ. -/
noncomputable def paperPhysicalDemandRateGeometry {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ) :
    Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ :=
  paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume (fun _ => 1) 0 κ

/-- Crucial physical factorization: each well-rate multiplies exactly one
column of the fixed spatial geometry matrix. No support or sign is discarded. -/
theorem paper_physical_demand_rate_geometry_factor
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ)
    (v : Fin w → ℝ) :
    paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume v 0 κ =
      paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
        Matrix.diagonal v := by
  classical
  ext i j
  cases i with
  | inl k =>
      simp [paperPhysicalDemandWellMatrix,
        paperPhysicalDemandRateGeometry, Matrix.mul_diagonal]
  | inr k =>
      by_cases hj : wellRegion j = some k
      · simp [paperPhysicalDemandWellMatrix, paperPhysicalSRWellMatrix,
          paperPhysicalDemandRateGeometry, Matrix.mul_diagonal, hj]
        ring
      · simp [paperPhysicalDemandWellMatrix, paperPhysicalSRWellMatrix,
          paperPhysicalDemandRateGeometry, Matrix.mul_diagonal, hj]

/-- The genuine induced Euclidean operator norm, written without choosing
an unrelated norm on the *type* of rectangular matrices. -/
noncomputable def paperMatrixEuclideanOpNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- Operator-norm bound supplied by the physical factorization and the
actual Euclidean matrix norm. The only scalar hypothesis is a uniform bound
on the well-average rates. -/
theorem paper_physical_demand_rate_opNorm_bound
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ) (κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (v : Fin w → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ j : Fin w, |v j| ≤ M) :
    paperMatrixEuclideanOpNorm
       (paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume v 0 κ * C) ≤
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M *
        paperMatrixEuclideanOpNorm C := by
  classical
  have hvnorm : ‖v‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).2
    intro j
    simpa [Real.norm_eq_abs] using hv j
  have hgeom : ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
          Matrix.diagonal v‖ ≤
        ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ * M := by
    calc
      ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
            Matrix.diagonal v‖ ≤
          ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ *
            ‖Matrix.diagonal v‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ *
            ‖v‖ := by rw [Matrix.l2_opNorm_diagonal]
      _ ≤ ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ * M :=
        mul_le_mul_of_nonneg_left hvnorm (norm_nonneg _)
  have hbound :
      ‖paperPhysicalDemandWellMatrix Bᵤ₀ wellRegion β volume v 0 κ * C‖ ≤
        ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ * M *
        ‖C‖ := by
    rw [paper_physical_demand_rate_geometry_factor]
    calc
      ‖(paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
          Matrix.diagonal v) * C‖ ≤
        ‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ *
          Matrix.diagonal v‖ * ‖C‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ‖ *
          M) * ‖C‖ :=
        mul_le_mul_of_nonneg_right hgeom (norm_nonneg _)
  simpa only [paperMatrixEuclideanOpNorm, ← Matrix.l2_opNorm_def] using hbound

end OperatorNorm

section ActualDerivative
open scoped Matrix.Norms.Elementwise

/-- The a.e. derivative of the actual allocated physical gain is bounded in
the induced Euclidean operator norm. In particular the bounded time rates of
the well means imply the bounded time rate of the genuine non-diagonal gain.
There is no hypothesis about Qdot. -/
theorem paper_physical_demand_actual_gain_rate_opNorm_ae
    {u r w : ℕ}
    (Bᵤ₀ : Matrix (Fin u) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (h hRate : ℝ → Fin w → ℝ) (α κ : ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       HasDerivAt (fun s => h s j) (hRate t j) t)
    (hrate : ∀ j : Fin w, ∀ᵐ t ∂paperPositiveTime,
       |hRate t j| ≤ M) :
    ∀ᵐ t ∂paperPositiveTime,
      paperMatrixEuclideanOpNorm
        (deriv (fun s => paperPhysicalDemandWellMatrix Bᵤ₀
           wellRegion β volume (h s) α κ * C) t) ≤
      paperMatrixEuclideanOpNorm
        (paperPhysicalDemandRateGeometry Bᵤ₀ wellRegion β volume κ) * M *
        paperMatrixEuclideanOpNorm C := by
  have hdall := paper_physical_well_rates_common_ae h hRate hderiv
  have hrall : ∀ᵐ t ∂paperPositiveTime, ∀ j : Fin w, |hRate t j| ≤ M :=
    Filter.eventually_all.mpr hrate
  filter_upwards [hdall, hrall] with t hdt hrt
  rw [paper_physical_demand_gain_deriv
    Bᵤ₀ wellRegion β volume h hRate α κ C t hdt]
  exact paper_physical_demand_rate_opNorm_bound
    Bᵤ₀ wellRegion β volume κ C (hRate t) M hM hrt

end ActualDerivative

end ReservoirSeismicityControl
