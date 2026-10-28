import ReservoirSeismicityControl.SeismicitySignedPhysicalLocalH2
import ReservoirSeismicityControl.SeismicitySignedSpatialH2Bootstrap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# M1: the physical L²-to-H² Bochner lifting gate

The physical signed SR reciprocal is constructed pointwise, and the verified
`sr_signed_physical_reciprocal_exact_duhamel` proves its Duhamel identity.
This module isolates the *functional-analytic* transfer of that identity to
H² on a near-well neighborhood U_j.

H below is the eventual bounded-Lipschitz Sobolev H²(U_j) Banach space and
L is L²(U_j).  The continuous linear map `embed : H →L[ℝ] L` is the canonical
inclusion.  The theorem does NOT assume that the constructed reciprocal Y
belongs to H²: it constructs its H² representative and proves its norm bound.

The remaining physical interface is substantial and explicit:
  (i) construct homogeneous and forcing H² fields from the signed physical
      exponential kernel using the *weak* 3D chain/product rules;
  (ii) show they are Bochner integrable in time and have uniform bounds;
  (iii) identify their L² images with the verified pointwise Duhamel formula.

These prerequisites are not proved here, and must not be confused with
Assumptions 1–5 alone. In particular this module is a **lifting gate**, NOT
an unconditional proof of Appendix A.2 (A7).

The advantage over previously generated helpers is that all conclusions,
including existence of an H² representative, its identification with the
physical L² field, and uniform norm control, now follow in one theorem.
No `sorry`, custom axiom, or requirement on Q-dot is used.
-/

namespace ReservoirSeismicityControl

open MeasureTheory

/-- An H²-valued candidate obtained by the physically normalized,
exponentially damped time kernel. This constructs an H² element rather
than assuming a priori H² regularity of the reciprocal. -/
noncomputable def srSignedH2BochnerCandidate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (aMin : ℝ) (hom : ℝ → H) (kernel : ℝ → ℝ → H) (t : ℝ) : H :=
  hom t + aMin⁻¹ •
    (∫ v, kernel t v ∂pressureExponentialKernelMeasure aMin t)

/-- The H² candidate has a uniform-in-time norm bound whenever the
homogeneous term and normalized forcing have the quantified Sobolev
bounds. Unlike a hypothesis `‖Y(t)‖H² ≤ M`, this estimates the actual
Bochner *construction*. -/
theorem sr_signed_H2_Bochner_candidate_uniform_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (aMin H0 Fmax : ℝ)
    (haMin : 0 < aMin) (hFmax : 0 ≤ Fmax)
    (hom : ℝ → H) (kernel : ℝ → ℝ → H)
    (hHom : ∀ t : ℝ, 0 ≤ t → ‖hom t‖ ≤ H0)
    (hKernel : ∀ t : ℝ, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        ‖kernel t v‖ ≤ Fmax) :
    ∀ t : ℝ, 0 ≤ t →
      ‖srSignedH2BochnerCandidate aMin hom kernel t‖ ≤
        H0 + Fmax / aMin := by
  intro t ht
  have hBound := sr_damped_bochner_convolution_norm_le
    aMin t Fmax haMin ht hFmax (kernel t) (hKernel t ht)
  calc
    ‖srSignedH2BochnerCandidate aMin hom kernel t‖ =
        ‖hom t + aMin⁻¹ •
          (∫ v, kernel t v ∂pressureExponentialKernelMeasure aMin t)‖ := rfl
    _ ≤ ‖hom t‖ + ‖aMin⁻¹ •
          (∫ v, kernel t v ∂pressureExponentialKernelMeasure aMin t)‖ :=
        norm_add_le _ _
    _ ≤ H0 + Fmax / aMin := add_le_add (hHom t ht) hBound

/-- A continuous embedding commutes with the explicit H²-valued Duhamel
integral. The hypothesis is *Bochner integrability of the kernel*, not
Sobolev regularity of the physical Y field. -/
theorem sr_signed_H2_Bochner_candidate_embeds
    {H L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (embed : H →L[ℝ] L)
    (aMin : ℝ) (hom : ℝ → H) (kernel : ℝ → ℝ → H)
    (hInt : ∀ t : ℝ, 0 ≤ t →
      Integrable (kernel t) (pressureExponentialKernelMeasure aMin t)) :
    ∀ t : ℝ, 0 ≤ t →
      embed (srSignedH2BochnerCandidate aMin hom kernel t) =
        embed (hom t) + aMin⁻¹ •
          (∫ v, embed (kernel t v)
            ∂pressureExponentialKernelMeasure aMin t) := by
  intro t ht
  unfold srSignedH2BochnerCandidate
  have hcomm := ContinuousLinearMap.integral_comp_comm embed (hInt t ht)
  rw [map_add, map_smul, hcomm]

/-- Consolidated M1 *lifting theorem*. The *constructed* reciprocal
`Yphysical` lives initially only in L². Under the specific H² kernel
regularity and L² Duhamel identification premises, we obtain an H²
representative with a bound independent of time. There is NO premise
saying `Yphysical ∈ H²`, nor a hypothesis already bounding its H² norm.

To complete physical M1, the time/space weak-Sobolev calculus must now
provide the H² `hom` and `kernel` and discharge `hPhysical` from
`sr_signed_physical_reciprocal_exact_duhamel`; this is the sole remaining
nontrivial analytic gate in the present lifting architecture. -/
theorem sr_signed_physical_reciprocal_exists_uniform_H2_lift
    {H L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (embed : H →L[ℝ] L)
    (aMin H0 Fmax : ℝ)
    (haMin : 0 < aMin) (hFmax : 0 ≤ Fmax)
    (Yphysical : ℝ → L) (hom : ℝ → H) (kernel : ℝ → ℝ → H)
    (hHom : ∀ t : ℝ, 0 ≤ t → ‖hom t‖ ≤ H0)
    (hKernel : ∀ t : ℝ, 0 ≤ t →
      ∀ᵐ v ∂pressureExponentialKernelMeasure aMin t,
        ‖kernel t v‖ ≤ Fmax)
    (hInt : ∀ t : ℝ, 0 ≤ t →
      Integrable (kernel t) (pressureExponentialKernelMeasure aMin t))
    (hPhysical : ∀ t : ℝ, 0 ≤ t →
      Yphysical t = embed (hom t) + aMin⁻¹ •
        (∫ v, embed (kernel t v)
          ∂pressureExponentialKernelMeasure aMin t)) :
    ∀ t : ℝ, 0 ≤ t → ∃ y : H,
      embed y = Yphysical t ∧ ‖y‖ ≤ H0 + Fmax / aMin := by
  intro t ht
  refine ⟨srSignedH2BochnerCandidate aMin hom kernel t, ?_, ?_⟩
  · exact (sr_signed_H2_Bochner_candidate_embeds
      embed aMin hom kernel hInt t ht).trans ((hPhysical t ht).symm)
  · exact sr_signed_H2_Bochner_candidate_uniform_bound
      aMin H0 Fmax haMin hFmax hom kernel hHom hKernel t ht

#print axioms ReservoirSeismicityControl.sr_signed_H2_Bochner_candidate_uniform_bound
#print axioms ReservoirSeismicityControl.sr_signed_H2_Bochner_candidate_embeds
#print axioms ReservoirSeismicityControl.sr_signed_physical_reciprocal_exists_uniform_H2_lift

end ReservoirSeismicityControl
