import ReservoirSeismicityControl.PressureNeumannPhysicalA3L2Semigroup
import ReservoirSeismicityControl.PressureNeumannClosedGradientOperator

/-!
# Block 70: physical A3 Neumann semigroup in closed-gradient variables

The physical A3 L² semigroup theorem has a weak generator characterization
in terms of a point `(u, Gu)` in the completed graph. The closed-gradient
operator allows us to express the same characterization directly in the
pressure variable `u` and its closed gradient on the pressure-domain submodule.

This is a change of mathematical presentation, not an assumption about
spatial regularity or boundary traces. In particular this file does not
identify the closed gradient domain with H¹(Ω). That identification and
the realization of smooth Neumann test cores remain separate obligations.

No bound on time derivatives of well fluxes is assumed.
-/

namespace ReservoirSeismicityControl

open MeasureTheory
open scoped InnerProductSpace BigOperators Matrix

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The completed-graph weak formulation is exactly the weak formulation
on the domain of the closed gradient. -/
theorem pressure_neumann_graph_energy_iff_closed_gradient
    (D : Submodule ℝ H) (G : D →ₗ[ℝ] K)
    (C : K →L[ℝ] K)
    (hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G))
    (u f : H) :
    (∃ x : pressureNeumannGraphHilbertDomain D G,
      pressureNeumannGraphHilbertEmbedding D G x = u ∧
        ∀ y : pressureNeumannGraphHilbertDomain D G,
          ⟪C (pressureNeumannGraphHilbertGradient D G x),
            pressureNeumannGraphHilbertGradient D G y⟫_ℝ =
          ⟪f, pressureNeumannGraphHilbertEmbedding D G y⟫_ℝ) ↔
    (∃ hu : u ∈ pressureNeumannClosedGradientDomain D G,
      ∀ v : pressureNeumannClosedGradientDomain D G,
        ⟪C (pressureNeumannClosedGradient D G hInj ⟨u, hu⟩),
          pressureNeumannClosedGradient D G hInj v⟫_ℝ =
        ⟪f, (v : H)⟫_ℝ) := by
  constructor
  · rintro ⟨x, hx, hWeak⟩
    have hu : u ∈ pressureNeumannClosedGradientDomain D G := by
      change u ∈ LinearMap.range (pressureNeumannGraphHilbertEmbedding D G).toLinearMap
      exact ⟨x, hx⟩
    refine ⟨hu, ?_⟩
    have hval : (⟨u, hu⟩ : pressureNeumannClosedGradientDomain D G) =
        ⟨pressureNeumannGraphHilbertEmbedding D G x,
          LinearMap.mem_range_self
            (pressureNeumannGraphHilbertEmbedding D G).toLinearMap x⟩ :=
      Subtype.ext hx.symm
    have hGx :
        pressureNeumannClosedGradient D G hInj ⟨u, hu⟩ =
          pressureNeumannGraphHilbertGradient D G x := by
      rw [hval]
      exact pressure_neumann_closed_gradient_on_graph D G hInj x
    intro v
    obtain ⟨y, hy, hGy⟩ :=
      (pressure_neumann_closed_gradient_graph_iff D G hInj
        (v : H) (pressureNeumannClosedGradient D G hInj v)).2
        ⟨v.property, rfl⟩
    calc
      ⟪C (pressureNeumannClosedGradient D G hInj ⟨u, hu⟩),
          pressureNeumannClosedGradient D G hInj v⟫_ℝ =
        ⟪C (pressureNeumannGraphHilbertGradient D G x),
          pressureNeumannGraphHilbertGradient D G y⟫_ℝ := by
        rw [hGx, hGy]
      _ = ⟪f, pressureNeumannGraphHilbertEmbedding D G y⟫_ℝ := hWeak y
      _ = ⟪f, (v : H)⟫_ℝ := by rw [hy]
  · rintro ⟨hu, hWeak⟩
    obtain ⟨x, hx, hGx⟩ :=
      (pressure_neumann_closed_gradient_graph_iff D G hInj
        u (pressureNeumannClosedGradient D G hInj ⟨u, hu⟩)).2
        ⟨hu, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    let v : pressureNeumannClosedGradientDomain D G :=
      ⟨pressureNeumannGraphHilbertEmbedding D G y,
        LinearMap.mem_range_self
          (pressureNeumannGraphHilbertEmbedding D G).toLinearMap y⟩
    have hGy : pressureNeumannClosedGradient D G hInj v =
        pressureNeumannGraphHilbertGradient D G y :=
      pressure_neumann_closed_gradient_on_graph D G hInj y
    calc
      ⟪C (pressureNeumannGraphHilbertGradient D G x),
          pressureNeumannGraphHilbertGradient D G y⟫_ℝ =
        ⟪C (pressureNeumannClosedGradient D G hInj ⟨u, hu⟩),
          pressureNeumannClosedGradient D G hInj v⟫_ℝ := by
        rw [hGx, hGy]
      _ = ⟪f, (v : H)⟫_ℝ := hWeak v
      _ = ⟪f, pressureNeumannGraphHilbertEmbedding D G y⟫_ℝ := rfl

section PhysicalSemigroup

/-- The physical A3 Neumann semigroup generator is characterized by its
weak diffusion form using the *closed gradient on a pressure submodule*.
The graph-closure construction, coefficient boundedness and ellipticity
are already proved; only the density and integration-by-parts conditions
for the proposed test spaces are required here.

The closed-gradient domain has not yet been identified with H¹(Ω). -/
theorem pressure_neumann_physical_A3_closed_gradient_semigroup_exists_of_IBP
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (D : Submodule ℝ (Lp ℝ 2 μ))
    (G : D →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 3)) 2 μ)
    (T : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 3)) 2 μ))
    (delta : T →ₗ[ℝ] Lp ℝ 2 μ)
    (hIBP : ∀ phi : T, ∀ u : D,
      ⟪(phi : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ), G u⟫_ℝ =
        ⟪delta phi, (u : Lp ℝ 2 μ)⟫_ℝ)
    (hTDense : DenseRange (T.subtype : T → Lp (EuclideanSpace ℝ (Fin 3)) 2 μ))
    (hDDense : DenseRange (D.subtype : D → Lp ℝ 2 μ))
    (k : Ω → Fin 3 → Fin 3 → ℝ) (eta : Ω → ℝ)
    (beta km kM etam etaM : ℝ)
    (hbeta : 0 < beta) (hkm : 0 < km) (hkM : 0 ≤ kM)
    (hetam : 0 < etam) (hetaM : 0 < etaM)
    (hEtaLo : ∀ x, etam ≤ eta x)
    (hEtaHi : ∀ x, eta x ≤ etaM)
    (hKSym : ∀ x i j, k x i j = k x j i)
    (hKLo : ∀ x (z : Fin 3 → ℝ),
      km * (∑ i : Fin 3, (z i) ^ 2) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j)
    (hKHi : ∀ x (z : Fin 3 → ℝ),
      (∑ i : Fin 3, ∑ j : Fin 3, z i * k x i j * z j) ≤
        kM * (∑ i : Fin 3, (z i) ^ 2))
    (hTensor : ∀ i j : Fin 3,
      Measurable (fun x => pressurePhysicalTensor k eta beta x i j)) :
    let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
      beta km kM etam etaM hbeta hkm hkM hetam
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
    ∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ),
      ∀ u f : Lp ℝ 2 μ,
        (∃ hu : u ∈ pressureNeumannClosedGradientDomain D G,
          ∀ v : pressureNeumannClosedGradientDomain D G,
            ⟪C (pressureNeumannClosedGradient D G
                  (pressure_neumann_graph_embedding_injective_of_integration_by_parts
                    D G T delta hIBP hTDense) ⟨u, hu⟩),
              pressureNeumannClosedGradient D G
                  (pressure_neumann_graph_embedding_injective_of_integration_by_parts
                    D G T delta hIBP hTDense) v⟫_ℝ =
              ⟪f, (v : Lp ℝ 2 μ)⟫_ℝ) ↔
        ∃ hs : u ∈ S.generatorDomain,
          S.generator ⟨u, hs⟩ = -f := by
  let C := pressureNeumannPhysicalL2MultiplierOfA3 μ k eta
    beta km kM etam etaM hbeta hkm hkM hetam
    hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  let hInj : Function.Injective (pressureNeumannGraphHilbertEmbedding D G) :=
    pressure_neumann_graph_embedding_injective_of_integration_by_parts
      D G T delta hIBP hTDense
  obtain ⟨S, hSem⟩ :=
    pressure_neumann_physical_A3_l2_semigroup_exists_of_IBP
      μ D G T delta hIBP hTDense hDDense k eta
      beta km kM etam etaM hbeta hkm hkM hetam hetaM
      hEtaLo hEtaHi hKSym hKLo hKHi hTensor
  refine ⟨S, ?_⟩
  intro u f
  exact (pressure_neumann_graph_energy_iff_closed_gradient
    D G C hInj u f).symm.trans (hSem u f)

end PhysicalSemigroup

end ReservoirSeismicityControl
