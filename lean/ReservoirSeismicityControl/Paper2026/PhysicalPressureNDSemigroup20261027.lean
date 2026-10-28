import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDPointwise20261027
import ReservoirSeismicityControl.PressureNeumannPhysicalA3L2Semigroup
import Mathlib.Tactic

/-!
# Neumann semigroup from the physical A3 tensor in arbitrary paper dimension

The k/(βη) coefficient is constructed as the actual pointwise and L²
multiplication operator on vector fields with Fin n_d components. A3
implies its uniform coercivity, symmetry and upper bound; the original
abstract Neumann graph-domain semigroup is then reused unchanged.

The physical H¹ smooth-IBP and density conditions are still exactly the
existing external/realization conditions, not falsely claimed as proved.
The dimension is explicitly restricted to the manuscript's {1,2,3}.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

section PhysicalL2

/-- The measurable physical tensor induces a symmetric L² coefficient with
lower and upper ellipticity estimates. Every coefficient bound is derived
from the A3 bounds on k, eta and beta. -/
theorem paper_pressure_A3_nd_l2_coefficient_properties
    {n_d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (z i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j) ≤
        kM * (∑ i : Fin n_d, (z i) ^ 2))
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let B := paperPressureL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    (∀ f g : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ,
      ⟪B f, g⟫_ℝ = ⟪f, B g⟫_ℝ) ∧
    (∀ f : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ,
      (km / (beta * etaM)) * (‖f‖ * ‖f‖) ≤ ⟪B f, f⟫_ℝ) ∧
    (∀ f : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ,
      ⟪B f, f⟫_ℝ ≤ (kM / (beta * etam)) * (‖f‖ * ‖f‖)) := by
  let E := EuclideanSpace ℝ (Fin n_d)
  let C : Ω → E →L[ℝ] E := paperPressurePointwiseCLM k eta beta
  let M : ℝ := kM / (beta * etam)
  let c : ℝ := km / (beta * etaM)
  have hM : 0 ≤ M :=
    div_nonneg hkM (le_of_lt (mul_pos hbeta hetam))
  have hC : AEStronglyMeasurable C μ :=
    (paper_pressure_pointwise_field_measurable k eta beta hTensor).aestronglyMeasurable
  have hBound : ∀ᵐ x ∂μ, ‖C x‖ ≤ M :=
    Filter.Eventually.of_forall
      (paper_pressure_pointwise_opNorm_le_of_A3
        k eta beta km kM etam etaM hbeta hkm hkM hetam
        hEtaLo hEtaHi hKSym hKLo hKHi)
  have hSym : ∀ᵐ x ∂μ, ∀ a b : E,
      ⟪C x a, b⟫_ℝ = ⟪a, C x b⟫_ℝ := by
    apply Filter.Eventually.of_forall
    intro x a b
    exact paper_pressure_pointwise_symmetric
      k eta beta x (hKSym x) a b
  have hLower : ∀ᵐ x ∂μ, ∀ z : E,
      c * (‖z‖ * ‖z‖) ≤ ⟪C x z, z⟫_ℝ := by
    apply Filter.Eventually.of_forall
    intro x z
    have h := paper_pressure_pointwise_lower
      k eta beta km etam etaM hbeta hkm hetam x
      (hEtaLo x) (hEtaHi x) (hKLo x) (WithLp.ofLp z)
    have hz : c * ‖z‖ ^ 2 ≤ ⟪C x z, z⟫_ℝ := by
      calc
        c * ‖z‖ ^ 2 = c * (∑ i : Fin n_d, (z i) ^ 2) := by
          rw [EuclideanSpace.real_norm_sq_eq z]
        _ ≤ ⟪C x z, z⟫_ℝ := by
          simpa only [c, C, WithLp.toLp_ofLp, PiLp.toLp_apply] using h
    simpa only [pow_two] using hz
  have hUpper : ∀ᵐ x ∂μ, ∀ z : E,
      ⟪C x z, z⟫_ℝ ≤ M * (‖z‖ * ‖z‖) := by
    apply Filter.Eventually.of_forall
    intro x z
    have h := paper_pressure_pointwise_upper
      k eta beta kM etam hbeta hkM hetam x
      (hEtaLo x) (hKHi x) (WithLp.ofLp z)
    have hz : ⟪C x z, z⟫_ℝ ≤ M * ‖z‖ ^ 2 := by
      calc
        ⟪C x z, z⟫_ℝ ≤ M * (∑ i : Fin n_d, (z i) ^ 2) := by
          simpa only [M, C, WithLp.toLp_ofLp, PiLp.toLp_apply] using h
        _ = M * ‖z‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq z]
    simpa only [pow_two] using hz
  let B := paperPressureL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hB : B = pressureNeumannL2Multiplier μ C hC M hM hBound := by
    rfl
  change (∀ f g : Lp E 2 μ, ⟪B f, g⟫_ℝ = ⟪f, B g⟫_ℝ) ∧
    (∀ f : Lp E 2 μ, c * (‖f‖ * ‖f‖) ≤ ⟪B f, f⟫_ℝ) ∧
    (∀ f : Lp E 2 μ, ⟪B f, f⟫_ℝ ≤ M * (‖f‖ * ‖f‖))
  rw [hB]
  refine ⟨?_, ?_, ?_⟩
  · intro f g
    exact pressure_neumann_l2_multiplier_symmetric
      μ C hC M hM hBound hSym f g
  · intro f
    exact pressure_neumann_l2_multiplier_elliptic_lower
      μ C hC M hM hBound c hLower f
  · intro f
    exact pressure_neumann_l2_multiplier_elliptic_upper
      μ C hC M hM hBound M hUpper f

end PhysicalL2

section PhysicalSemigroup

/-- The physical A3 tensor, represented as multiplication on vector-field L²,
provides the coefficient of the graph-domain Neumann semigroup directly.

The test-level gradient G and divergence delta, their integration-by-parts
identity and the density of their test spaces are still explicit hypotheses.
This is not yet an H¹-identification theorem for the physical reservoir. -/
theorem paper_pressure_A3_nd_l2_semigroup_exists_of_IBP
    {n_d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd : Paper2026.PaperSpatialDimension n_d)
    (μ : Measure Ω)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (G : D →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ)
    (T : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ))
    (delta : T →ₗ[ℝ] Lp ℝ 2 μ)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ), G u⟫_ℝ =
        ⟪delta phi, (u : Lp ℝ 2 μ)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ))
    (hDDense : DenseRange (D.subtype : D → Lp ℝ 2 μ))
    (k : Ω → Fin n_d → Fin n_d → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin n_d → ℝ),
      km * (∑ i : Fin n_d, (z i) ^ 2) ≤
        ∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin n_d → ℝ),
      (∑ i : Fin n_d, ∑ j : Fin n_d, z i * k x i j * z j) ≤
        kM * (∑ i : Fin n_d, (z i) ^ 2))
    (hTensor : ∀ i j : Fin n_d,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let C := paperPressureL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ),
      ∀ u f : Lp ℝ 2 μ,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          pressureNeumannGraphHilbertEmbedding D G x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            ⟪C (pressureNeumannGraphHilbertGradient D G x),
              pressureNeumannGraphHilbertGradient D G v⟫_ℝ =
                ⟪f, pressureNeumannGraphHilbertEmbedding D G v⟫_ℝ) ↔
        ∃ hu : u ∈ S.generatorDomain,
          S.generator ⟨u, hu⟩ = -f := by
  let C := paperPressureL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hc : 0 < km / (beta * etaM) :=
    div_pos hkm (mul_pos hbeta hetaM)
  have hA3 := paper_pressure_A3_nd_l2_coefficient_properties
    μ k eta beta km kM etam etaM hbeta hkm hkM hetam hetaM
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  have hEll : ∀ z : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ,
      (km / (beta * etaM)) * (‖z‖ * ‖z‖) ≤ ⟪C z, z⟫_ℝ :=
    hA3.2.1
  have hSym : ∀ z w : Lp (EuclideanSpace ℝ (Fin n_d)) 2 μ,
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hA3.1
  exact pressure_neumann_graph_coefficient_semigroup_exists_of_IBP
    D G T delta hIBP hTDense hDDense C
    (km / (beta * etaM)) hc hEll hSym

end PhysicalSemigroup


#print axioms paper_pressure_A3_nd_l2_coefficient_properties
#print axioms paper_pressure_A3_nd_l2_semigroup_exists_of_IBP

end ReservoirSeismicityControl
