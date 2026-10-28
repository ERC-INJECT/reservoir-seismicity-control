import ReservoirSeismicityControl.PaperPhysicalWellAverages
import ReservoirSeismicityControl.PaperAERateBridge
import ReservoirSeismicityControl.SeismicityRateL2

/-!
# Stage 50: time derivatives of the actual physical SR well integrals

Stage 49 introduced the raw spatial Lebesgue integral
  h(t) = integral_(V*) (gamma_1(x) * R(x,t)) / volume(V*).
Stages 12--14 established the corresponding derivative estimate for a
strongly differentiable L²-valued trajectory. This module connects these
objects, rather than treating them as interchangeable by convention.

First we establish their equality whenever the L² representative agrees
almost everywhere on the well with the physical product gamma_1 R. Next we
transfer the a.e. strong L² derivative and its bound to the *actual* h(t).
Finally we obtain the weighted estimate directly from the fixed spatial
coefficient multiplier K_gamma and the L² bound for R_t.

Analytic inputs not proved here: the actual SR state has an a.e. strong L²
derivative, K_gamma is the multiplication operator by gamma_1 on this
reservoir L² space, and the SR ODE/pressure estimate bounds R_t. They are
explicit arguments, not implicit conclusions of the finite-dimensional proof.
No bound on the rate of change of well controls Q is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- The physical well integral equals the previously formalized L² well mean,
provided the chosen L² representative is gamma_1(x) R(x,t) almost everywhere
on the well. This is the missing raw-integral / L² identification. -/
theorem paper_physical_well_mean_eq_L2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (F : Lp ℝ 2 μ) (t : ℝ)
    (hrep : ∀ᵐ x ∂(μ.restrict s),
      (F x : ℝ) = γ₁ x * R t x) :
    paperPhysicalSRWellMean μ s γ₁ R t =
      wellMeanL2 μ s hs hfinite F := by
  unfold paperPhysicalSRWellMean wellMeanL2
  rw [well_integral_L2_eq_set_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  rw [← hx]
  simp [Real.inner_apply]

/-- An a.e. strong L² derivative and its uniform bound give an a.e. bound on
 the derivative of the raw Lebesgue well sensitivity h(t). In particular, this
is NOT a claim that the derivative exists at a controller switching instant. -/
theorem paper_physical_well_mean_rate_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (γ₁ : X → ℝ) (R : ℝ → X → ℝ)
    (F Fdot : ℝ → Lp ℝ 2 μ) (C : ℝ)
    (hrep : ∀ τ : ℝ, ∀ᵐ x ∂(μ.restrict s),
      (F τ x : ℝ) = γ₁ x * R τ x)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt F (Fdot t) t)
    (hL2 : ∀ᵐ t ∂paperPositiveTime, ‖Fdot t‖ ≤ C) :
    ∀ᵐ t ∂paperPositiveTime,
      |deriv (fun τ => paperPhysicalSRWellMean μ s γ₁ R τ) t| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * C) / μ.real s := by
  have heq : (fun τ => paperPhysicalSRWellMean μ s γ₁ R τ) =
      (fun τ => wellMeanL2 μ s hs hfinite (F τ)) := by
    funext τ
    exact paper_physical_well_mean_eq_L2 μ s hs hfinite γ₁ R
      (F τ) τ (hrep τ)
  have hfactor : 0 ≤ (μ.real s) ^ (1 / (2 : ℝ)) := by
    positivity
  filter_upwards [hderiv, hL2] with t hd hb
  rw [heq, well_mean_L2_deriv μ s hs hfinite F (Fdot t) t hd]
  calc
    |wellMeanL2 μ s hs hfinite (Fdot t)| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * ‖Fdot t‖) / μ.real s :=
          well_mean_L2_bound μ s hs hfinite hpositive (Fdot t)
    _ ≤ ((μ.real s) ^ (1 / (2 : ℝ)) * C) / μ.real s := by
      apply div_le_div_of_nonneg_right _ hpositive.le
      exact mul_le_mul_of_nonneg_left hb hfactor

/-- If gamma_1 is represented by a fixed bounded multiplier K_gamma on L²,
then the a.e. sensitivity derivative is bounded by
  sqrt(volume(V*)) * ‖K_gamma‖ * sup_t ‖R_t‖ / volume(V*).

The representative identity is stated explicitly. Proving it for the physical
coefficient is the separate bounded-multiplication identification, not a new
assumption that the well controls have bounded derivatives. -/
theorem paper_physical_well_mean_rate_from_sr_L2_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Rdot : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Cγ CR : ℝ) (hCγ : 0 ≤ Cγ)
    (hK : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ τ : ℝ, ∀ᵐ x ∂(μ.restrict s),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hderiv : ∀ᵐ t ∂paperPositiveTime, HasDerivAt R (Rdot t) t)
    (hRdot : ∀ᵐ t ∂paperPositiveTime, ‖Rdot t‖ ≤ CR) :
    ∀ᵐ t ∂paperPositiveTime,
      |deriv (fun τ => paperPhysicalSRWellMean μ s γ₁ Rphysical τ) t| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * (Cγ * CR)) / μ.real s := by
  have hweightedDeriv : ∀ᵐ t ∂paperPositiveTime,
      HasDerivAt (fun τ => Kγ (R τ)) (Kγ (Rdot t)) t := by
    filter_upwards [hderiv] with t hd
    exact Kγ.hasFDerivAt.comp_hasDerivAt t hd
  have hweightedBound : ∀ᵐ t ∂paperPositiveTime,
      ‖Kγ (Rdot t)‖ ≤ Cγ * CR := by
    filter_upwards [hRdot] with t hr
    calc
      ‖Kγ (Rdot t)‖ ≤ ‖Kγ‖ * ‖Rdot t‖ := Kγ.le_opNorm (Rdot t)
      _ ≤ Cγ * ‖Rdot t‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ Cγ * CR := mul_le_mul_of_nonneg_left hr hCγ
  exact paper_physical_well_mean_rate_ae μ s hs hfinite hpositive γ₁
    Rphysical (fun τ => Kγ (R τ)) (fun τ => Kγ (Rdot τ))
    (Cγ * CR) hrep hweightedDeriv hweightedBound


/-- Explicitly reuse Stage 14's SR equation estimate, rather than assuming
an arbitrary bound on the SR rate. This stronger pointwise version requires
the strong L² derivative at the time in question. At switching instants the
manuscript uses the almost-everywhere version above instead. -/
theorem paper_physical_well_mean_rate_from_pressure_L2
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hpositive : 0 < μ.real s)
    (γ₁ : X → ℝ) (Rphysical : ℝ → X → ℝ)
    (R Udot Rdot reaction : ℝ → Lp ℝ 2 μ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Kpressure : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
    (Cγ Cmult CU Creact : ℝ) (hCγ : 0 ≤ Cγ)
    (hKγ : ‖Kγ‖ ≤ Cγ)
    (hrep : ∀ τ : ℝ, ∀ᵐ x ∂(μ.restrict s),
      ((Kγ (R τ)) x : ℝ) = γ₁ x * Rphysical τ x)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt R (Rdot t) t)
    (hKpressure : ∀ t, 0 ≤ t → ‖Kpressure t‖ ≤ Cmult)
    (hU : ∀ t, 0 ≤ t → ‖Udot t‖ ≤ CU)
    (hreaction : ∀ t, 0 ≤ t → ‖reaction t‖ ≤ Creact)
    (hODE : ∀ t, 0 ≤ t →
      Rdot t = -(Kpressure t (Udot t)) - reaction t)
    (t : ℝ) (ht : 0 < t) :
    |deriv (fun τ => paperPhysicalSRWellMean μ s γ₁ Rphysical τ) t| ≤
      ((μ.real s) ^ (1 / (2 : ℝ)) *
        (Cγ * (Cmult * CU + Creact))) / μ.real s := by
  have heq : (fun τ => paperPhysicalSRWellMean μ s γ₁ Rphysical τ) =
      (fun τ => wellMeanL2 μ s hs hfinite (Kγ (R τ))) := by
    funext τ
    exact paper_physical_well_mean_eq_L2 μ s hs hfinite γ₁ Rphysical
      (Kγ (R τ)) τ (hrep τ)
  have hweighted : HasDerivAt (fun τ => Kγ (R τ))
      (Kγ (Rdot t)) t :=
    Kγ.hasFDerivAt.comp_hasDerivAt t (hderiv t ht.le)
  have hsr : ‖Rdot t‖ ≤ Cmult * CU + Creact :=
    sr_rate_L2_from_pressure μ Udot Rdot reaction Kpressure
      Cmult CU Creact hKpressure hU hreaction hODE t ht.le
  have hfactor : 0 ≤ (μ.real s) ^ (1 / (2 : ℝ)) := by
    positivity
  have hrate : ‖Kγ (Rdot t)‖ ≤ Cγ * (Cmult * CU + Creact) := by
    calc
      ‖Kγ (Rdot t)‖ ≤ ‖Kγ‖ * ‖Rdot t‖ := Kγ.le_opNorm (Rdot t)
      _ ≤ Cγ * ‖Rdot t‖ :=
        mul_le_mul_of_nonneg_right hKγ (norm_nonneg _)
      _ ≤ Cγ * (Cmult * CU + Creact) :=
        mul_le_mul_of_nonneg_left hsr hCγ
  rw [heq, well_mean_L2_deriv μ s hs hfinite
      (fun τ => Kγ (R τ)) (Kγ (Rdot t)) t hweighted]
  calc
    |wellMeanL2 μ s hs hfinite (Kγ (Rdot t))| ≤
        ((μ.real s) ^ (1 / (2 : ℝ)) * ‖Kγ (Rdot t)‖) /
          μ.real s :=
            well_mean_L2_bound μ s hs hfinite hpositive (Kγ (Rdot t))
    _ ≤ ((μ.real s) ^ (1 / (2 : ℝ)) *
          (Cγ * (Cmult * CU + Creact))) / μ.real s := by
      apply div_le_div_of_nonneg_right _ hpositive.le
      exact mul_le_mul_of_nonneg_left hrate hfactor

end ReservoirSeismicityControl
