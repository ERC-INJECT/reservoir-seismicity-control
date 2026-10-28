import ReservoirSeismicityControl.Algebra
import ReservoirSeismicityControl.Definitions

/-!
# Appendix B: exact demand and constrained uncertainty

Proved below: W(C z + F D)=D whenever WC=0 and WF=I. This is the
algebraic core of exact demand tracking in (25).

Not proved here: B₀ C_W=I and W F_D=I from the pseudoinverse and rank
hypotheses, the positive-definite SR allocation (B19), the matrix norm
estimate (B20), or the derivative bound (B21).
-/

namespace ReservoirSeismicityControl

/-- Exact demand tracking from the two allocation identities. -/
theorem demand_exact
    {n m nr : ℕ}
    (W : (Fin n → ℝ) →ₗ[ℝ] (Fin nr → ℝ))
    (C : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (F : (Fin nr → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hWC : ∀ z : Fin m → ℝ, W (C z) = 0)
    (hWF : ∀ d : Fin nr → ℝ, W (F d) = d)
    (z : Fin m → ℝ) (d : Fin nr → ℝ) :
    W (C z + F d) = d := by
  calc
    W (C z + F d) = W (C z) + W (F d) := map_add W _ _
    _ = (0 : Fin nr → ℝ) + d := by rw [hWC z, hWF d]
    _ = d := zero_add d

end ReservoirSeismicityControl
