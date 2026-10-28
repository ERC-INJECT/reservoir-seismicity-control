import ReservoirSeismicityControl.Model

/-!
# Stability theorem imported conceptually from Moreno--Garcia-Mathey (2024)

There is NO Lean proof of the MIMO super-twisting theorem [43] in this project.
To claim a completely checked Theorem 1 or 2, the relevant published stability
theorem must be formalized, with its exact hypotheses (matrix norm, required
gain restrictions, perturbation class, continuous-time solution concept, and
finite-time/ISS conclusion), and then proved in Lean.

The paper's controller-level application must also establish that the model
satisfies those hypotheses. Do NOT add a custom Lean `axiom` standing for [43]
and then report that the entire controller theorem is machine-checked.
-/

namespace ReservoirSeismicityControl

/-- Distinguishes the three controller regimes in the manuscript. -/
inductive ControllerRegime
  | superTwisting
  | intermediate
  | linear
  deriving DecidableEq, Repr

end ReservoirSeismicityControl
