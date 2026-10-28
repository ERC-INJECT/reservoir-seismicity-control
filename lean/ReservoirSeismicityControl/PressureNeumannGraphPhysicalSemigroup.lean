import ReservoirSeismicityControl.PressureNeumannGradientClosability
import ReservoirSeismicityControl.PressureNeumannPhysicalCoercivity

/-!
# Block 70: the physical Neumann semigroup on the completed gradient graph

Combines the previous verified Hilbert graph-domain, closability from weak
integration by parts, physical tensor symmetry, and ellipticity-derived
coercivity. We derive completeness, the norm estimate, and the injective,
dense embedding rather than assuming them separately.

Remaining physical-realization obligations are explicit:
* identify the squared norm of the completed gradient component with the
  integrated squared three-dimensional spatial gradient (`hGradientSq`);
* realize the integral diffusion energy as a continuous bilinear form `E`
  and the unit-shift form as a continuous bilinear form `B₁` (`hEnergy`,
  `hForm₁`), with the stated integrability conditions;
* instantiate the test domains, weak gradient, test divergence,
  integration by parts and their densities for the real reservoir domain.

No boundedness of derivatives of the well rates is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators

/-- The concrete completed-gradient form domain inherits the physical
semigroup theorem from the test-level integration-by-parts identity and
ellipticity. In particular, the graph norm and embedding properties are
*proved*, not extra assumptions on the abstract form space. -/
theorem pressure_physical_graph_neumann_semigroup_exists_of_IBP
    {H K Ω : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [MeasurableSpace Ω]
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (T : Submodule ℝ K) (delta : T →ₗ[ℝ] H)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : K), G u⟫_ℝ = ⟪delta phi, (u : H)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → K))
    (hDDense : DenseRange (D.subtype : D → H))
    (μ : Measure Ω)
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km etam etaM : ℝ)
    (gradient : pressureNeumannGraphHilbertDomain D G → Ω → Fin 3 → ℝ)
    (B₁ E : pressureNeumannGraphHilbertDomain D G →L[ℝ]
      pressureNeumannGraphHilbertDomain D G →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : pressureNeumannGraphHilbertDomain D G,
      B₁ x y =
        ⟪pressureNeumannGraphHilbertEmbedding D G x,
          pressureNeumannGraphHilbertEmbedding D G y⟫_ℝ + E x y)
    (hEnergy : ∀ u v : pressureNeumannGraphHilbertDomain D G,
      E u v = pressurePhysicalThreeDEnergy μ k eta beta gradient u v)
    (hGradientSq : ∀ u : pressureNeumannGraphHilbertDomain D G,
      pressurePhysicalThreeDGradientSq μ gradient u =
        ‖pressureNeumannGraphHilbertGradient D G u‖ *
          ‖pressureNeumannGraphHilbertGradient D G u‖)
    (hGradInt : ∀ u : pressureNeumannGraphHilbertDomain D G, Integrable
      (fun x => ∑ i : Fin 3, (gradient u x i) ^ 2) μ)
    (hEnergyInt : ∀ u : pressureNeumannGraphHilbertDomain D G, Integrable
      (fun x => ∑ i : Fin 3, ∑ l : Fin 3,
        gradient u x i * pressurePhysicalTensor k eta beta x i l * gradient u x l) μ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hetam : 0 < etam)
    (hetaM : 0 < etaM)
    (hetaLo : ∀ᵐ x ∂μ, etam ≤ eta x)
    (hetaHi : ∀ᵐ x ∂μ, eta x ≤ etaM)
    (hkLo : ∀ᵐ x ∂μ, ∀ g : Fin 3 → ℝ,
      km * (∑ i : Fin 3, (g i) ^ 2) ≤
        ∑ i : Fin 3, ∑ l : Fin 3, g i * k x i l * g l)
    (hsym : ∀ᵐ x ∂μ, ∀ i l : Fin 3, k x i l = k x l i) :
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H,
      ∀ u f : H,
        (∃ x : pressureNeumannGraphHilbertDomain D G,
          pressureNeumannGraphHilbertEmbedding D G x = u ∧
          ∀ v : pressureNeumannGraphHilbertDomain D G,
            pressurePhysicalThreeDEnergy μ k eta beta gradient x v =
              ⟪f, pressureNeumannGraphHilbertEmbedding D G v⟫_ℝ) ↔
          ∃ hu : u ∈ S.generatorDomain,
            S.generator ⟨u, hu⟩ = -f := by
  have hGraphNorm : ∀ x : pressureNeumannGraphHilbertDomain D G,
      ‖x‖ * ‖x‖ ≤
        ‖pressureNeumannGraphHilbertEmbedding D G x‖ *
          ‖pressureNeumannGraphHilbertEmbedding D G x‖ +
        pressurePhysicalThreeDGradientSq μ gradient x := by
    intro x
    apply le_of_eq
    calc
      ‖x‖ * ‖x‖ =
          ‖pressureNeumannGraphHilbertEmbedding D G x‖ *
            ‖pressureNeumannGraphHilbertEmbedding D G x‖ +
          ‖pressureNeumannGraphHilbertGradient D G x‖ *
            ‖pressureNeumannGraphHilbertGradient D G x‖ :=
        pressure_neumann_graph_norm_sq D G x
      _ = _ := by rw [hGradientSq x]
  have hEmbedding :
      Function.Injective (pressureNeumannGraphHilbertEmbedding D G) ∧
        DenseRange (pressureNeumannGraphHilbertEmbedding D G) :=
    pressure_neumann_graph_embedding_injective_and_dense
      D G T delta hIBP hTDense hDDense
  exact pressure_physical_neumann_semigroup_exists_of_graph_norm
    μ k eta beta km etam etaM gradient
    (pressureNeumannGraphHilbertEmbedding D G) B₁ E hForm₁ hEnergy
    hGraphNorm hGradInt hEnergyInt hEmbedding.1 hEmbedding.2
    hbeta hkm hetam hetaM hetaLo hetaHi hkLo hsym

end ReservoirSeismicityControl
