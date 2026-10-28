import ReservoirSeismicityControl.PaperActualDemandGain
import ReservoirSeismicityControl.SeismicityRateL2
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Stage 49: the actual spatial SR well averages supply the sensitivity box

Appendix A.2 proves local positive upper and lower bounds for the seismicity
field R on each well neighborhood U_j. Assumption A3 supplies positive bounds
on gamma_1. This module passes those *a.e. pointwise* inequalities through the
real Lebesgue integral over the physical well support V_j^*.

Consequently the physical sensitivity h_j(t) belongs to a fixed positive
interval. The integral, not a finite quadrature, is used in the definition.
The final bridge substitutes those integrals into Stage 48's inverse theorem.

For the Stage 48 interface (whose gain is defined for all real times), we
extend the solution to negative times by setting R(t) = R(0) for t < 0.
No behavior of the PDE before t = 0 is assumed or used.

PDE obligations still external here: the local a.e. SR bounds, coefficient
bounds, and spatial integrability supplied by Appendix A.2. This module
proves the transfer from those estimates to the finite-dimensional gain.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped Matrix

/-- The physical average h_j(t) = |V_j^*|^-1 integral_(V_j^*) gamma_1 R. -/
noncomputable def paperPhysicalSRWellMean
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ) (t : ℝ) : ℝ :=
  (∫ x in s, γ₁ x * R t x ∂μ) / μ.real s

/-- Normalized integration preserves an a.e. interval on a well of finite,
strictly positive volume. No quadrature approximation is involved. -/
theorem paper_set_mean_interval
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (f : X → ℝ) (lo hi : ℝ)
    (hfinite : μ s < ⊤) (hpositive : 0 < μ.real s)
    (hint : IntegrableOn f s μ)
    (hlo : ∀ᵐ x ∂(μ.restrict s), lo ≤ f x)
    (hhi : ∀ᵐ x ∂(μ.restrict s), f x ≤ hi) :
    lo ≤ (∫ x in s, f x ∂μ) / μ.real s ∧
      (∫ x in s, f x ∂μ) / μ.real s ≤ hi := by
  have hμfinite : μ s ≠ ⊤ := ne_of_lt hfinite
  have hclo : IntegrableOn (fun _ : X => lo) s μ :=
    integrableOn_const hμfinite
  have hchi : IntegrableOn (fun _ : X => hi) s μ :=
    integrableOn_const hμfinite
  have hlow : lo * μ.real s ≤ ∫ x in s, f x ∂μ := by
    calc
      lo * μ.real s = ∫ _x in s, lo ∂μ := by
        simp [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in s, f x ∂μ := integral_mono_ae hclo hint hlo
  have hupp : (∫ x in s, f x ∂μ) ≤ hi * μ.real s := by
    calc
      (∫ x in s, f x ∂μ) ≤ ∫ _x in s, hi ∂μ :=
        integral_mono_ae hint hchi hhi
      _ = hi * μ.real s := by
        simp [setIntegral_const, smul_eq_mul, mul_comm]
  constructor
  · exact (le_div_iff₀ hpositive).2 hlow
  · exact (div_le_iff₀ hpositive).2 hupp

/-- The product gamma_1(x) R(x,t) inherits positive spatial bounds from
A3 and the logistic SR comparison argument in Appendix A.2. -/
theorem paper_physical_sr_well_mean_interval
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmin Rmax : ℝ) (t : ℝ)
    (hfinite : μ s < ⊤) (hpositive : 0 < μ.real s)
    (hγmin : 0 < γmin) (hRmin : 0 < Rmin)
    (hγ : ∀ᵐ x ∂(μ.restrict s), γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ᵐ x ∂(μ.restrict s), Rmin ≤ R t x ∧ R t x ≤ Rmax)
    (hint : IntegrableOn (fun x => γ₁ x * R t x) s μ) :
    γmin * Rmin ≤ paperPhysicalSRWellMean μ s γ₁ R t ∧
    paperPhysicalSRWellMean μ s γ₁ R t ≤ γmax * Rmax := by
  have hpointlo : ∀ᵐ x ∂(μ.restrict s),
      γmin * Rmin ≤ γ₁ x * R t x := by
    filter_upwards [hγ, hR] with x hx hy
    have hRnonneg : 0 ≤ R t x := (le_of_lt hRmin).trans hy.1
    calc
      γmin * Rmin ≤ γmin * R t x :=
        mul_le_mul_of_nonneg_left hy.1 (le_of_lt hγmin)
      _ ≤ γ₁ x * R t x :=
        mul_le_mul_of_nonneg_right hx.1 hRnonneg
  have hpointup : ∀ᵐ x ∂(μ.restrict s),
      γ₁ x * R t x ≤ γmax * Rmax := by
    filter_upwards [hγ, hR] with x hx hy
    have hRnonneg : 0 ≤ R t x := (le_of_lt hRmin).trans hy.1
    have hγmaxnonneg : 0 ≤ γmax :=
      (le_of_lt hγmin).trans (hx.1.trans hx.2)
    calc
      γ₁ x * R t x ≤ γmax * R t x :=
        mul_le_mul_of_nonneg_right hx.2 hRnonneg
      _ ≤ γmax * Rmax :=
        mul_le_mul_of_nonneg_left hy.2 hγmaxnonneg
  exact paper_set_mean_interval μ s (fun x => γ₁ x * R t x)
    (γmin * Rmin) (γmax * Rmax) hfinite hpositive hint
    hpointlo hpointup

/-- Freeze the physical SR state at t = 0 for negative times. This is only
used to match Stage 48's all-real-time gain API. -/
noncomputable def paperNonnegativeTimeWellSensitivities
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ) : ℝ → Fin w → ℝ :=
  fun t j => paperPhysicalSRWellMean μ (well j) γ₁ R (max t 0)

/-- Local A2/A3/A5 comparison estimates supply the sensitivity box of
Appendix B for ALL times in the extended Stage 48 interface. -/
theorem paper_physical_well_sensitivity_box
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hfinite : ∀ j, μ (well j) < ⊤)
    (hpositive : ∀ j, 0 < μ.real (well j))
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(μ.restrict (well j)),
       γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(μ.restrict (well j)),
        Rmin j ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * R t x) (well j) μ) :
    (∀ t j, γmin * Rmin j ≤
      paperNonnegativeTimeWellSensitivities μ well γ₁ R t j) ∧
    (∀ t j, paperNonnegativeTimeWellSensitivities μ well γ₁ R t j ≤
      γmax * Rmax) := by
  constructor
  · intro t j
    exact (paper_physical_sr_well_mean_interval μ (well j) γ₁ R
      γmin γmax (Rmin j) Rmax (max t 0)
      (hfinite j) (hpositive j) hγmin (hRmin j)
      (hγ j) (hR (max t 0) (le_max_right _ _) j)
      (hint (max t 0) (le_max_right _ _) j)).1
  · intro t j
    exact (paper_physical_sr_well_mean_interval μ (well j) γ₁ R
      γmin γmax (Rmin j) Rmax (max t 0)
      (hfinite j) (hpositive j) hγmin (hRmin j)
      (hγ j) (hR (max t 0) (le_max_right _ _) j)
      (hint (max t 0) (le_max_right _ _) j)).2

/-- On physical times the nonnegative-time extension is exactly the original
well integral, not a surrogate finite-dimensional sensitivity. -/
theorem paper_physical_well_sensitivity_of_nonnegative_time
    {X : Type*} [MeasurableSpace X] {w : ℕ}
    (μ : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (j : Fin w) :
    paperNonnegativeTimeWellSensitivities μ well γ₁ R t j =
      paperPhysicalSRWellMean μ (well j) γ₁ R t := by
  simp [paperNonnegativeTimeWellSensitivities, max_eq_left ht]


/-- Appendix A.2's *local spatial bounds*, combined with A6's finite
vertex conditions, imply Stage 48's inverse estimate for the physical
demand gain built from actual SR well integrals. This discharges the
independent `lo ≤ h ≤ hi` hypotheses used in Stage 48. -/
theorem paper_physical_demand_inverse_from_local_sr_bounds
    {X : Type*} [MeasurableSpace X] {u r w : ℕ}
    (measure : Measure X) (well : Fin w → Set X)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (γmin γmax Rmax : ℝ) (Rmin : Fin w → ℝ)
    (hfinite : ∀ j, measure (well j) < ⊤)
    (hpositive : ∀ j, 0 < measure.real (well j))
    (hγmin : 0 < γmin) (hRmin : ∀ j, 0 < Rmin j)
    (hγ : ∀ j, ∀ᵐ x ∂(measure.restrict (well j)),
      γmin ≤ γ₁ x ∧ γ₁ x ≤ γmax)
    (hR : ∀ t, 0 ≤ t → ∀ j,
      ∀ᵐ x ∂(measure.restrict (well j)),
        Rmin j ≤ R t x ∧ R t x ≤ Rmax)
    (hint : ∀ t, 0 ≤ t → ∀ j,
      IntegrableOn (fun x => γ₁ x * R t x) (well j) measure)
    (B₀ : Matrix (Sum (Fin u) (Fin r)) (Fin w) ℝ)
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (hBC : B₀ * C = 1)
    (α μcoer M : ℝ)
    (hα : (α - 1) ^ 2 < 1)
    (hμ : 0 < μcoer) (hM : 0 < M) (hμM : μcoer ≤ M)
    (hvertexCoercive : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ v : Fin r → ℝ,
        μcoer * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r, v i *
            ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i)
    (hvertexUpper : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = γmin * Rmin j ∨ hV j = γmax * Rmax) →
      ∀ (xᵤ : Fin u → ℝ) (xᵣ : Fin r → ℝ),
        (∑ i : Fin r,
          (paperPhysicalSRCombinedAction wellRegion β volume C
            hV xᵤ xᵣ i) ^ 2) ≤
          M ^ 2 * ((∑ j : Fin u, (xᵤ j) ^ 2) +
            (∑ i : Fin r, (xᵣ i) ^ 2)))
    (t : ℝ) (x : EuclideanSpace ℝ (Sum (Fin u) (Fin r))) :
    let κ : ℝ := (1 - (α - 1) ^ 2) * μcoer / (2 * M ^ 2)
    let ρ : ℝ := max (1 - (1 - (α - 1) ^ 2) / 4)
      (1 - (1 - (α - 1) ^ 4) * μcoer ^ 2 / (4 * M ^ 2))
    let δ : ℝ := Real.sqrt ρ
    let Gphysical : ℝ → EuclideanSpace ℝ (Sum (Fin u) (Fin r)) →L[ℝ]
         EuclideanSpace ℝ (Sum (Fin u) (Fin r)) :=
      fun s => Matrix.toEuclideanCLM (𝕜 := ℝ)
        (n := Sum (Fin u) (Fin r))
        (paperPhysicalDemandWellMatrix
          (fun i j => B₀ (Sum.inl i) j)
          wellRegion β volume
          (paperNonnegativeTimeWellSensitivities measure well γ₁ R s)
          α κ * C)
    IsUnit (Gphysical t) ∧ ‖Ring.inverse (Gphysical t) x‖ ≤
      (1 / (1 - δ)) * ‖x‖ := by
  have hbox := paper_physical_well_sensitivity_box measure well γ₁ R
    γmin γmax Rmax Rmin hfinite hpositive hγmin hRmin hγ hR hint
  exact paper_physical_demand_product_inverse_from_vertices B₀ wellRegion
    β volume C hBC (fun j => γmin * Rmin j)
    (fun _ => γmax * Rmax)
    (paperNonnegativeTimeWellSensitivities measure well γ₁ R)
    α μcoer M hα hμ hM hμM hbox.1 hbox.2
    hvertexCoercive hvertexUpper t x

end ReservoirSeismicityControl
