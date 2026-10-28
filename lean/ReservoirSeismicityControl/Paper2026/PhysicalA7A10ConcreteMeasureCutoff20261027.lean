import ReservoirSeismicityControl.Paper2026.PhysicalA7A10CanonicalCutoffNear20261027
import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDCanonicalGreenSemigroup20261027
import ReservoirSeismicityControl.Paper2026.PositiveSRFarSmoothProjection
import ReservoirSeismicityControl.PressureNeumannL2TensorMultiplier
import Mathlib.Tactic

/-!
# A7–A10: canonical spatial measure and actual normalized physical cutoff

The common n_d=1,2,3 physical measure identity was proved previously.
This module gives its actual L² map, rather than postulating an abstract
identification between ambient-restricted and reservoir-subtype L².

More importantly, it constructs the spatial multipliers K_gamma and cutoff
from the physical measurable scalar functions gamma1 and zeta (with their
A3 bounds). The resulting normalized finite-region SR observation is the
physical function zeta * indicator_V * gamma1 * R / normalization.

The separate standard elliptic H² compact cutoff / weak Green identity is
NOT being proved here. The already passing `a7_a10_green_cutoff_lift` takes
that analytical input and produces the canonical Neumann-domain lift.
- physical region/time representativity is required to identify an arbitrary
  L² representative of the actual SR trajectory, not assumed automatically.
- no new axioms and no assumed multiplier operator K_gamma or cutoff.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ENNReal

set_option maxHeartbeats 1400000

/-- The actual ambient-restricted to reservoir-subtype L² isometry.
Its measure-preservation theorem has ALREADY been proved for every n_d. -/
noncomputable def physicalNDAmbientToReservoirL2
    {n_d : ℕ} (Ω : Opens (PaperSpatial n_d)) :
    Lp ℝ 2 ((volume : Measure (PaperSpatial n_d)).restrict
      (Ω : Set (PaperSpatial n_d))) →L[ℝ]
    Lp ℝ 2 (ReservoirSeismicityControl.pressureNDRestrictedMeasure Ω
      (volume : Measure (PaperSpatial n_d))) :=
  (Lp.compMeasurePreservingₗᵢ ℝ
    (Subtype.val : ↥(Ω : Set (PaperSpatial n_d)) → PaperSpatial n_d)
    (ReservoirSeismicityControl.pressure_nd_subtype_measure_preserving Ω
      (volume : Measure (PaperSpatial n_d)))).toContinuousLinearMap

/-- No hidden normalization factor arises on passing to reservoir L². -/
theorem physical_nd_ambient_to_reservoir_norm
    {n_d : ℕ} (Ω : Opens (PaperSpatial n_d))
    (f : Lp ℝ 2 ((volume : Measure (PaperSpatial n_d)).restrict
      (Ω : Set (PaperSpatial n_d)))) :
    ‖physicalNDAmbientToReservoirL2 Ω f‖ = ‖f‖ := by
  exact (Lp.compMeasurePreservingₗᵢ ℝ
    (Subtype.val : ↥(Ω : Set (PaperSpatial n_d)) → PaperSpatial n_d)
    (ReservoirSeismicityControl.pressure_nd_subtype_measure_preserving Ω
      (volume : Measure (PaperSpatial n_d)))).norm_map f

/-- Actual spatial scalar multiplier on L², constructed from the existing
pointwise operator theorem. Its representative is a(x)f(x). -/
noncomputable def physicalScalarMultiplier
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (ha : Measurable a)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, |a x| ≤ M) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ReservoirSeismicityControl.pressureNeumannL2Multiplier μ
    (fun x => (a x) • (ContinuousLinearMap.id ℝ ℝ))
    (ha.smul measurable_const).aestronglyMeasurable
    M hM (by
      filter_upwards [hBound] with x hx
      simpa [norm_smul, Real.norm_eq_abs] using hx)

/-- The multiplier norm is an A3 consequence, not a new hypothesis. -/
theorem physical_scalar_multiplier_norm
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (ha : Measurable a)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, |a x| ≤ M) :
    ‖physicalScalarMultiplier μ a ha M hM hBound‖ ≤ M := by
  exact ReservoirSeismicityControl.pressure_neumann_l2_multiplier_norm_le μ
    (fun x => (a x) • (ContinuousLinearMap.id ℝ ℝ))
    (ha.smul measurable_const).aestronglyMeasurable
    M hM (by
      filter_upwards [hBound] with x hx
      simpa [norm_smul, Real.norm_eq_abs] using hx)

/-- The canonical L² multiplier equals pointwise spatial multiplication. -/
theorem physical_scalar_multiplier_apply_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (ha : Measurable a)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, |a x| ≤ M)
    (f : Lp ℝ 2 μ) :
    (physicalScalarMultiplier μ a ha M hM hBound f : X → ℝ) =ᵐ[μ]
      fun x => a x * f x := by
  have h := ReservoirSeismicityControl.pressure_neumann_l2_multiplier_apply_ae μ
    (fun x => (a x) • (ContinuousLinearMap.id ℝ ℝ))
    (ha.smul measurable_const).aestronglyMeasurable
    M hM (by
      filter_upwards [hBound] with x hx
      simpa [norm_smul, Real.norm_eq_abs] using hx) f
  filter_upwards [h] with x hx
  simpa only [physicalScalarMultiplier, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] using hx

/-- The actual smooth-cutoff and gamma1 multipliers have a product representative.
The physical fields are fixed in space; no SR time derivative is used. -/
theorem physical_gamma_cutoff_product_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (γ ζ : X → ℝ) (hγ : Measurable γ) (hζ : Measurable ζ)
    (Mγ Mζ : ℝ) (hMγ : 0 ≤ Mγ) (hMζ : 0 ≤ Mζ)
    (hγBound : ∀ᵐ x ∂μ, |γ x| ≤ Mγ)
    (hζBound : ∀ᵐ x ∂μ, |ζ x| ≤ Mζ)
    (f : Lp ℝ 2 μ) :
    ((physicalScalarMultiplier μ ζ hζ Mζ hMζ hζBound)
      ((physicalScalarMultiplier μ γ hγ Mγ hMγ hγBound) f) : X → ℝ)
        =ᵐ[μ] fun x => ζ x * γ x * f x := by
  have h1 := physical_scalar_multiplier_apply_ae μ ζ hζ Mζ hMζ
    hζBound ((physicalScalarMultiplier μ γ hγ Mγ hMγ hγBound) f)
  have h2 := physical_scalar_multiplier_apply_ae μ γ hγ Mγ hMγ
    hγBound f
  filter_upwards [h1, h2] with x hx hy
  rw [hx, hy]
  ring

/-- No separately postulated `hK` and no free `hcutoffAll`:
the normalized *near SR weight* of A10 is literally the fixed smooth
cutoff times the physical sensitivity gamma1*R on the actual SR region.
Only the natural a.e. identification of the chosen L² trajectory with
its physical pointwise rate is required. -/
theorem physical_actual_SR_near_weight_representative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region : Set X) (hregion : MeasurableSet region)
    (γ ζ : X → ℝ) (hγ : Measurable γ) (hζ : Measurable ζ)
    (Mγ Mζ : ℝ) (hMγ : 0 ≤ Mγ) (hMζ : 0 ≤ Mζ)
    (hγBound : ∀ᵐ x ∂μ, |γ x| ≤ Mγ)
    (hζBound : ∀ᵐ x ∂μ, |ζ x| ≤ Mζ)
    (R : ℝ → Lp ℝ 2 μ) (Rphysical : ℝ → X → ℝ)
    (hRRep : ∀ t, (R t : X → ℝ) =ᵐ[μ] Rphysical t)
    (gamma10 R0star t : ℝ) :
    let Kγ := physicalScalarMultiplier μ γ hγ Mγ hMγ hγBound
    let cutoff := physicalScalarMultiplier μ ζ hζ Mζ hMζ hζBound
    ∀ᵐ x ∂μ,
      ((paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) x : ℝ) =
        ζ x * region.indicator (fun y =>
          (γ y * Rphysical t y) /
            (gamma10 * R0star * μ.real region)) x := by
  let Kγ := physicalScalarMultiplier μ γ hγ Mγ hMγ hγBound
  let cutoff := physicalScalarMultiplier μ ζ hζ Mζ hMζ hζBound
  have hKRep : ∀ τ, ∀ᵐ x ∂μ,
      ((Kγ (R τ)) x : ℝ) = γ x * Rphysical τ x := by
    intro τ
    have h1 := physical_scalar_multiplier_apply_ae μ γ hγ Mγ hMγ
      hγBound (R τ)
    filter_upwards [h1, hRRep τ] with x hx hy
    rw [hx, hy]
  have hWeight := paper_sr_diffusion_weight_representative
    μ region hregion γ Rphysical Kγ R hKRep gamma10 R0star t
  have hCut := physical_scalar_multiplier_apply_ae μ ζ hζ Mζ hMζ
    hζBound (paperSRDiffusionWeight μ region hregion Kγ R gamma10 R0star t)
  filter_upwards [hWeight, hCut] with x hw hc
  change ((cutoff (paperSRDiffusionWeight μ region hregion Kγ R
      gamma10 R0star t)) x : ℝ) = _
  rw [hc, hw]


/-- A10's `hcutoffAll` is now a consequence of the constructed smooth-cutoff
multiplier. It no longer needs to be an assumption of the terminal physical
application when `cutoff = physicalScalarMultiplier μ ζ ...`. -/
theorem physical_cutoff_all_actual_SR_weights
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {r : ℕ} (regions : Fin r → Set X) (hregions : ∀ i, MeasurableSet (regions i))
    (ζ : X → ℝ) (hζ : Measurable ζ)
    (Mζ : ℝ) (hMζ : 0 ≤ Mζ)
    (hζBound : ∀ᵐ x ∂μ, |ζ x| ≤ Mζ)
    (Kγ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (R : ℝ → Lp ℝ 2 μ)
    (gamma10 R0star : ℝ) :
    let cutoff := physicalScalarMultiplier μ ζ hζ Mζ hMζ hζBound
    ∀ (i : Fin r) (t : ℝ), ∀ᵐ x ∂μ,
      ((cutoff (paperSRDiffusionWeight μ (regions i) (hregions i)
        Kγ R gamma10 R0star t)) x : ℝ) =
      ζ x * ((paperSRDiffusionWeight μ (regions i) (hregions i)
        Kγ R gamma10 R0star t) x : ℝ) := by
  dsimp only
  intro i t
  exact physical_scalar_multiplier_apply_ae μ ζ hζ Mζ hMζ hζBound _

/-- A smooth cutoff supported in the specified physical neighborhood makes
its actual normalized SR weight vanish outside that neighborhood. This is
the locality statement that fails for a hypothetical nonlocal `Kγ`.
The operator representation and normalization are NOT postulated. -/
theorem physical_actual_SR_near_supported_in
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (region U : Set X) (hregion : MeasurableSet region)
    (γ ζ : X → ℝ) (hγ : Measurable γ) (hζ : Measurable ζ)
    (Mγ Mζ : ℝ) (hMγ : 0 ≤ Mγ) (hMζ : 0 ≤ Mζ)
    (hγBound : ∀ᵐ x ∂μ, |γ x| ≤ Mγ)
    (hζBound : ∀ᵐ x ∂μ, |ζ x| ≤ Mζ)
    (hζSupport : ∀ x : X, x ∉ U → ζ x = 0)
    (R : ℝ → Lp ℝ 2 μ) (Rphysical : ℝ → X → ℝ)
    (hRRep : ∀ t, (R t : X → ℝ) =ᵐ[μ] Rphysical t)
    (gamma10 R0star t : ℝ) :
    let Kγ := physicalScalarMultiplier μ γ hγ Mγ hMγ hγBound
    let cutoff := physicalScalarMultiplier μ ζ hζ Mζ hMζ hζBound
    ∀ᵐ x ∂μ, x ∉ U →
      ((paperSRNearDiffusionWeight μ region hregion Kγ R
        gamma10 R0star cutoff t) x : ℝ) = 0 := by
  have h := physical_actual_SR_near_weight_representative μ region hregion
    γ ζ hγ hζ Mγ Mζ hMγ hMζ hγBound hζBound
    R Rphysical hRRep gamma10 R0star t
  filter_upwards [h] with x hx
  intro hnot
  rw [hx, hζSupport x hnot, zero_mul]

#print axioms physical_nd_ambient_to_reservoir_norm
#print axioms physical_scalar_multiplier_norm
#print axioms physical_scalar_multiplier_apply_ae
#print axioms physical_actual_SR_near_weight_representative
#print axioms physical_cutoff_all_actual_SR_weights
#print axioms physical_actual_SR_near_supported_in

end ReservoirSeismicityControl.Paper2026
