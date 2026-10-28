import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDCanonicalGreenSemigroup20261027
import ReservoirSeismicityControl.PressureNeumannGeneratorWeakIdentity
import Mathlib.Tactic

/-!
# The positive physical Neumann operator is symmetric and nonnegative

The physical n_d-dimensional canonical Green semigroup theorem supplies
exactly the weak-energy / negative-generator equivalence used below.
Hence the positive realization A := -generator automatically satisfies
the symmetric-positive operator conditions of A10, with no independent
symmetry or positivity hypothesis. The coefficient form's symmetry and
nonnegativity come from A3 in the passing n_d-dimensional multiplier theorem.

This is an operator identification lemma, not a claim that A10's
pressure-path identifications, local elliptic cutoff lifts, or A7's
standard Sobolev calculus have yet been instantiated.
-/

namespace ReservoirSeismicityControl

open scoped InnerProductSpace
open MarkovProcess.Semigroup

variable {V H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Positive Neumann operator `A = -L` is symmetric whenever the generator
`L` is characterized by a symmetric weak energy. In the physical application
`V` is the dimension-parametric maximal Neumann form domain; `j` and `g`
are its actual pressure and gradient embeddings and `C` is the A3 tensor
multiplier. The sole characterization hypothesis is already the CONCLUSION
of the passing canonical Green semigroup theorem. -/
theorem pressure_nd_positive_generator_symmetric_of_weak_characterization
    (S : StronglyContinuousContractionSemigroup H)
    (j : V → H) (g : V → K) (C : K →L[ℝ] K)
    (hCSym : ∀ z w : K, ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ)
    (hWeak : ∀ u f : H,
      (∃ x : V, j x = u ∧
        ∀ v : V, ⟪C (g x), g v⟫_ℝ = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f)
    (a b : S.generatorDomain) :
    ⟪-S.generator a, (b : H)⟫_ℝ =
      ⟪(a : H), -S.generator b⟫_ℝ := by
  obtain ⟨x, hx, hxe⟩ :=
    (hWeak (a : H) (-S.generator a)).2 ⟨a.property, by simp⟩
  obtain ⟨y, hy, hye⟩ :=
    (hWeak (b : H) (-S.generator b)).2 ⟨b.property, by simp⟩
  have hCswap (z w : K) : ⟪C z, w⟫_ℝ = ⟪C w, z⟫_ℝ := by
    calc
      ⟪C z, w⟫_ℝ = ⟪z, C w⟫_ℝ := hCSym z w
      _ = ⟪C w, z⟫_ℝ := real_inner_comm _ _
  calc
    ⟪-S.generator a, (b : H)⟫_ℝ =
        ⟪-S.generator a, j y⟫_ℝ := by rw [hy]
    _ = ⟪C (g x), g y⟫_ℝ := (hxe y).symm
    _ = ⟪C (g y), g x⟫_ℝ := hCswap _ _
    _ = ⟪-S.generator b, j x⟫_ℝ := hye x
    _ = ⟪j x, -S.generator b⟫_ℝ := real_inner_comm _ _
    _ = ⟪(a : H), -S.generator b⟫_ℝ := by rw [hx]

/-- The positive physical Neumann generator is nonnegative, derived from
its weak energy and the A3 nonnegative tensor multiplier. -/
theorem pressure_nd_positive_generator_nonnegative_of_weak_characterization
    (S : StronglyContinuousContractionSemigroup H)
    (j : V → H) (g : V → K) (C : K →L[ℝ] K)
    (hCNonneg : ∀ z : K, 0 ≤ ⟪C z, z⟫_ℝ)
    (hWeak : ∀ u f : H,
      (∃ x : V, j x = u ∧
        ∀ v : V, ⟪C (g x), g v⟫_ℝ = ⟪f, j v⟫_ℝ) ↔
      ∃ hu : u ∈ S.generatorDomain,
        S.generator ⟨u, hu⟩ = -f)
    (a : S.generatorDomain) :
    0 ≤ ⟪-S.generator a, (a : H)⟫_ℝ := by
  obtain ⟨x, hx, hxe⟩ :=
    (hWeak (a : H) (-S.generator a)).2 ⟨a.property, by simp⟩
  calc
    0 ≤ ⟪C (g x), g x⟫_ℝ := hCNonneg _
    _ = ⟪-S.generator a, j x⟫_ℝ := hxe x
    _ = ⟪-S.generator a, (a : H)⟫_ℝ := by rw [hx]

end ReservoirSeismicityControl

#check ReservoirSeismicityControl.pressure_nd_positive_generator_symmetric_of_weak_characterization
#check ReservoirSeismicityControl.pressure_nd_positive_generator_nonnegative_of_weak_characterization
#print axioms ReservoirSeismicityControl.pressure_nd_positive_generator_symmetric_of_weak_characterization
#print axioms ReservoirSeismicityControl.pressure_nd_positive_generator_nonnegative_of_weak_characterization
