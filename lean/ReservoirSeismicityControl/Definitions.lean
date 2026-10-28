import Mathlib

/-!
# Time-uniform scalar bounds

These are helper statements, not a model of the reservoir PDE. The analytic
function spaces and weak solution theory remain separate formalization tasks.
-/

namespace ReservoirSeismicityControl

/-- A nonnegative-time, uniformly bounded real-valued signal. -/
def BoundedSignal (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → |f t| ≤ M

/-- Strict positivity uniformly for all nonnegative times. -/
def UniformPositive (f : ℝ → ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, 0 ≤ t → m ≤ f t

/-- A constant is a bounded signal. -/
theorem boundedSignal_const (c : ℝ) :
    BoundedSignal (fun _ : ℝ => c) := by
  refine ⟨|c|, abs_nonneg c, ?_⟩
  intro t ht
  exact le_refl _

/-- Sum of two time-uniformly bounded signals. -/
theorem boundedSignal_add {f g : ℝ → ℝ}
    (hf : BoundedSignal f) (hg : BoundedSignal g) :
    BoundedSignal (fun t => f t + g t) := by
  rcases hf with ⟨Mf, hMf, hf⟩
  rcases hg with ⟨Mg, hMg, hg⟩
  refine ⟨Mf + Mg, add_nonneg hMf hMg, ?_⟩
  intro t ht
  calc
    |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
    _ ≤ Mf + Mg := add_le_add (hf t ht) (hg t ht)

end ReservoirSeismicityControl
