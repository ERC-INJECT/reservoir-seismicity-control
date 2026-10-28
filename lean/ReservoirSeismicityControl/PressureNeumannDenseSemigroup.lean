import ReservoirSeismicityControl.PressureNeumannGeneratedSemigroup
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Block 70 — discharge Neumann resolvent dense range from form-domain density

The previous generation adapter required dense range for *each* R_lam.
Here we derive those hypotheses uniformly from the density of the embedding
j : V -> H, injectivity of j, and symmetry of the single unit weak form B₁.

The geometric verification of dense H¹(Ω) -> L²(Ω), and identification of
the physical reservoir form, remain separate obligations. No Q derivative
bounds are assumed.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace
open MarkovProcess.Semigroup

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An inner-product separation criterion implies actual topological density
for the image of a bounded real-linear operator on a Hilbert space. -/
theorem pressure_neumann_denseRange_of_separating
    (R : H →L[ℝ] H)
    (hsepR : ∀ z : H, (∀ x : H, ⟪z, R x⟫_ℝ = 0) → z = 0) :
    DenseRange R := by
  let K : Submodule ℝ H := LinearMap.range (R : H →ₗ[ℝ] H)
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hz0 : z = 0 := hsepR z (by
        intro x
        exact (Submodule.mem_orthogonal' K z).mp hz (R x) ⟨x, rfl⟩)
      simpa [hz0]
    · exact bot_le
  have htop : K.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff).2 horth
  have hclosure : closure (K : Set H) = Set.univ := by
    have hco := congrArg (fun S : Submodule ℝ H => (S : Set H)) htop
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe] using hco
  rw [denseRange_iff_closure_range]
  have hrange : (K : Set H) = Set.range R := rfl
  simpa only [hrange] using hclosure

/-- Symmetry of the shifted form follows from symmetry of the unit form.
The diffusion energy is already determined by the unit form identity. -/
theorem pressure_neumann_canonical_shift_symmetric
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (x y : V) :
    pressureNeumannCanonicalShiftForm lam B₁ E x y =
      pressureNeumannCanonicalShiftForm lam B₁ E y x := by
  have hSymE : E x y = E y x := by
    have hxy : ⟪j x, j y⟫_ℝ + E x y =
        ⟪j y, j x⟫_ℝ + E y x := by
      calc
        _ = B₁ x y := (hForm₁ x y).symm
        _ = B₁ y x := hSym₁ x y
        _ = _ := hForm₁ y x
    rw [real_inner_comm (j x) (j y)] at hxy
    exact add_left_cancel hxy
  rw [pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁ x y,
      pressure_neumann_canonical_shift_formula lam j B₁ E hForm₁ y x,
      real_inner_comm (j x) (j y), hSymE]

/-- Every positive canonical Neumann resolvent has dense range, provided
only the usual symmetry and geometrical embedding properties. -/
theorem pressure_neumann_canonical_denseRange
    (lam : ℝ) (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j)
    (hjDense : DenseRange j)
    (hLam : 0 < lam) :
    DenseRange (pressureNeumannCanonicalResolvent lam j B₁ E hB₁ hForm₁ hE hLam) := by
  let BLam := pressureNeumannCanonicalShiftForm lam B₁ E
  let hBLam : IsCoercive BLam :=
    pressure_neumann_canonical_shift_coercive lam j B₁ E hB₁ hForm₁ hE hLam
  have hSymLam : ∀ x y : V, BLam x y = BLam y x :=
    pressure_neumann_canonical_shift_symmetric lam j B₁ E hForm₁ hSym₁
  have hsep : ∀ f : H, (∀ v : V, ⟪f, j v⟫_ℝ = 0) → f = 0 := by
    intro f hf
    exact hjDense.eq_zero_of_inner_left ℝ hf
  have hsymmetric : ∀ f g : H,
      ⟪pressureHilbertWeakResolvent j BLam hBLam f, g⟫_ℝ =
      ⟪f, pressureHilbertWeakResolvent j BLam hBLam g⟫_ℝ :=
    pressure_hilbert_resolvent_symmetric j BLam hBLam hSymLam
  have hinj : Function.Injective (pressureHilbertWeakResolvent j BLam hBLam) :=
    pressure_hilbert_resolvent_injective j BLam hBLam hjinj hsep
  change DenseRange (pressureHilbertWeakResolvent j BLam hBLam)
  exact pressure_neumann_denseRange_of_separating
    (pressureHilbertWeakResolvent j BLam hBLam)
    (pressure_neumann_resolvent_range_separating
      (pressureHilbertWeakResolvent j BLam hBLam) hsymmetric hinj)

/-- Genuine C₀ contraction semigroup generated from the canonical Neumann
resolvents, without an independently assumed dense-range family. -/
noncomputable def pressureNeumannGeneratedSemigroupOfDenseEmbedding
    (j : V →L[ℝ] H) (B₁ E : V →L[ℝ] V →L[ℝ] ℝ)
    (hB₁ : IsCoercive B₁)
    (hForm₁ : ∀ x y : V, B₁ x y = ⟪j x, j y⟫_ℝ + E x y)
    (hE : ∀ x : V, 0 ≤ E x x)
    (hSym₁ : ∀ x y : V, B₁ x y = B₁ y x)
    (hjinj : Function.Injective j) (hjDense : DenseRange j) :
    StronglyContinuousContractionSemigroup H :=
  pressureNeumannGeneratedSemigroup j B₁ E hB₁ hForm₁ hE
    (fun lam hLam => pressure_neumann_canonical_denseRange
      lam j B₁ E hB₁ hForm₁ hE hSym₁ hjinj hjDense hLam)

end ReservoirSeismicityControl
