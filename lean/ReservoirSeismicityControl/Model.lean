import ReservoirSeismicityControl.Definitions

/-!
# Typed finite-indexed signals from the paper

This file establishes the index structure for well controls and regional
outputs without claiming a formal model of the infinite-dimensional Neumann
PDE. It is intentionally only a starting point for the PDE model.
-/

namespace ReservoirSeismicityControl

/-- n wells, mᵤ pressure outputs, mᵣ SR outputs, nᵣ demand constraints. -/
structure Dimensions where
  wells : ℕ
  pressureRegions : ℕ
  srRegions : ℕ
  demandConstraints : ℕ

/-- Observable and controlled signals, sampled as functions of real time. -/
structure ControlSignals (n mu mr nr : ℕ) where
  flux : ℝ → Fin n → ℝ
  pressureOutputs : ℝ → Fin mu → ℝ
  srOutputs : ℝ → Fin mr → ℝ
  pressureReferences : ℝ → Fin mu → ℝ
  srReferences : ℝ → Fin mr → ℝ
  demand : ℝ → Fin nr → ℝ

/- The geometric PDE model, Neumann domain, weak derivatives, and
   coupling to local SR remain to be defined; see PROOF_OBLIGATIONS.md. -/

end ReservoirSeismicityControl
