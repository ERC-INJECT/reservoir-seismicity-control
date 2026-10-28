import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3HessianStrongConvergence20261026
import ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Closure
import Mathlib.Tactic

/-!
# Appendix A.2: actual weak H² graph of the A3 coefficient product

For the physical coefficient a(x,q) = gamma2(x,q) * Rstar(x), this
assembles the previously checked strong L² convergence of all its
Leibniz product jets with the existing closedness theorem for weak H²
graphs. The conclusion is the ACTUAL weak spatial derivative graph of
the nonsmooth coefficient product (at a fixed time), rather than a
separately assumed graph of that product.

Inputs from standard, externally cited bounded-Lipschitz Sobolev theory:
(1) smooth approximations of the *factors*, with their factor Lp limits;
(2) the integration-by-parts identities of the smooth product approximants.
The preceding smooth-product module derives their classical derivative
formulas from factor derivatives; the standard smooth test-function
integration-by-parts theorem supplies the remaining pairing identities.
Neither the weak derivatives of the nonsmooth PRODUCT nor convergence of
its product jets is a hypothesis here.

The L² and L∞ (respectively L² and L⁴) factor representatives supplied to
this theorem must represent the same underlying Sobolev fields when it is
applied physically. That canonical representative identification belongs to
standard Lp/Sobolev theory. This theorem does not construct mollifiers or
certify the physical test space.

No sorry, admit, custom axiom, or change to any previously passing module.
-/

namespace ReservoirSeismicityControl.Paper2026

open Filter MeasureTheory
open ReservoirSeismicityControl.SeismicitySignedPhysicalWeakH2Closure

private instance weakProductFactTwo : Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩
private instance weakProductFactFour : Fact ((1 : ENNReal) ≤ 4) :=
  ⟨by norm_num⟩
private instance weakProductFactTop : Fact ((1 : ENNReal) ≤ ⊤) :=
  ⟨by simp⟩

private instance weakProductHolder2Inf :
    (2 : ENNReal).HolderTriple ⊤ 2 := by
  constructor
  simp

private instance weakProductHolderInf2 :
    (⊤ : ENNReal).HolderTriple 2 2 := by
  constructor
  simp

private instance weakProductHolder44 :
    (4 : ENNReal).HolderTriple 4 2 := by
  constructor
  change ((4 : NNReal) : ENNReal)⁻¹ + ((4 : NNReal) : ENNReal)⁻¹ =
    ((2 : NNReal) : ENNReal)⁻¹
  rw [← ENNReal.coe_inv (show (4 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_inv (show (2 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_add]
  apply congrArg (fun z : NNReal => (z : ENNReal))
    (show (4 : NNReal)⁻¹ + (4 : NNReal)⁻¹ = (2 : NNReal)⁻¹ by
      apply Subtype.ext
      norm_num)

/-- The actual `gamma2 * Rstar` has the weak H² graph whose three first
and nine second spatial derivatives are its genuine Leibniz products.
The only smooth integration-by-parts inputs are for the approximating
coefficients, not the limiting physical coefficient. All product-jet
convergence is DERIVED from convergence of the factor jets using the
previously verified strong Hölder limit theorems. -/
noncomputable def physical_A7_actual_A3_coefficient_weak_H2_from_factor_limits
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {Φ : Type*}
    (pair : Φ → Lp ℝ 2 μ →L[ℝ] ℝ)
    (testDeriv : Fin 3 → Φ → Lp ℝ 2 μ →L[ℝ] ℝ)
    (gamma2 : Lp ℝ 2 μ) (gammaInf starInf : Lp ℝ ⊤ μ)
    (gamma2N : ℕ → Lp ℝ 2 μ)
    (gammaInfN starInfN : ℕ → Lp ℝ ⊤ μ)
    (Dgamma2 Dstar2 : Fin 3 → Lp ℝ 2 μ)
    (Dgamma2N Dstar2N : ℕ → Fin 3 → Lp ℝ 2 μ)
    (Dgamma4 Dstar4 : Fin 3 → Lp ℝ 4 μ)
    (Dgamma4N Dstar4N : ℕ → Fin 3 → Lp ℝ 4 μ)
    (DDgamma2 DDstar2 : Fin 3 → Fin 3 → Lp ℝ 2 μ)
    (DDgamma2N DDstar2N : ℕ → Fin 3 → Fin 3 → Lp ℝ 2 μ)
    (hg : Tendsto gamma2N atTop (nhds gamma2))
    (hgInf : Tendsto gammaInfN atTop (nhds gammaInf))
    (hrInf : Tendsto starInfN atTop (nhds starInf))
    (hDg : ∀ i, Tendsto (fun n => Dgamma2N n i) atTop
      (nhds (Dgamma2 i)))
    (hDr : ∀ i, Tendsto (fun n => Dstar2N n i) atTop
      (nhds (Dstar2 i)))
    (hDg4 : ∀ i, Tendsto (fun n => Dgamma4N n i) atTop
      (nhds (Dgamma4 i)))
    (hDr4 : ∀ i, Tendsto (fun n => Dstar4N n i) atTop
      (nhds (Dstar4 i)))
    (hDDg : ∀ i j, Tendsto (fun n => DDgamma2N n i j) atTop
      (nhds (DDgamma2 i j)))
    (hDDr : ∀ i j, Tendsto (fun n => DDstar2N n i j) atTop
      (nhds (DDstar2 i j)))
    (hSmoothFirst : ∀ n i φ,
      testDeriv i φ
        ((ContinuousLinearMap.holderL μ 2 ⊤ 2
          (ContinuousLinearMap.mul ℝ ℝ) (gamma2N n)) (starInfN n)) =
      -pair φ
        ((ContinuousLinearMap.holderL μ 2 ⊤ 2
            (ContinuousLinearMap.mul ℝ ℝ) (Dgamma2N n i)) (starInfN n) +
          (ContinuousLinearMap.holderL μ ⊤ 2 2
            (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN n)) (Dstar2N n i)))
    (hSmoothSecond : ∀ n i j φ,
      testDeriv j φ
        ((ContinuousLinearMap.holderL μ 2 ⊤ 2
            (ContinuousLinearMap.mul ℝ ℝ) (Dgamma2N n i)) (starInfN n) +
          (ContinuousLinearMap.holderL μ ⊤ 2 2
            (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN n)) (Dstar2N n i)) =
      -pair φ
        ((ContinuousLinearMap.holderL μ 2 ⊤ 2
            (ContinuousLinearMap.mul ℝ ℝ) (DDgamma2N n i j)) (starInfN n) +
          (ContinuousLinearMap.holderL μ 4 4 2
            (ContinuousLinearMap.mul ℝ ℝ) (Dgamma4N n i)) (Dstar4N n j) +
          (ContinuousLinearMap.holderL μ 4 4 2
            (ContinuousLinearMap.mul ℝ ℝ) (Dgamma4N n j)) (Dstar4N n i) +
          (ContinuousLinearMap.holderL μ ⊤ 2 2
            (ContinuousLinearMap.mul ℝ ℝ) (gammaInfN n)) (DDstar2N n i j))) :
    WeakH2Three pair testDeriv := by
  let M2Inf := ContinuousLinearMap.holderL μ 2 ⊤ 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let MInf2 := ContinuousLinearMap.holderL μ ⊤ 2 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let M44 := ContinuousLinearMap.holderL μ 4 4 2
    (ContinuousLinearMap.mul ℝ ℝ)
  let aN : ℕ → Lp ℝ 2 μ := fun n => (M2Inf (gamma2N n)) (starInfN n)
  let daN : ℕ → Fin 3 → Lp ℝ 2 μ := fun n i =>
    (M2Inf (Dgamma2N n i)) (starInfN n) +
      (MInf2 (gammaInfN n)) (Dstar2N n i)
  let ddaN : ℕ → Fin 3 → Fin 3 → Lp ℝ 2 μ := fun n i j =>
    (M2Inf (DDgamma2N n i j)) (starInfN n) +
      (M44 (Dgamma4N n i)) (Dstar4N n j) +
      (M44 (Dgamma4N n j)) (Dstar4N n i) +
      (MInf2 (gammaInfN n)) (DDstar2N n i j)
  let a : Lp ℝ 2 μ := (M2Inf gamma2) starInf
  let da : Fin 3 → Lp ℝ 2 μ := fun i =>
    (M2Inf (Dgamma2 i)) starInf + (MInf2 gammaInf) (Dstar2 i)
  let dda : Fin 3 → Fin 3 → Lp ℝ 2 μ := fun i j =>
    (M2Inf (DDgamma2 i j)) starInf +
      (M44 (Dgamma4 i)) (Dstar4 j) +
      (M44 (Dgamma4 j)) (Dstar4 i) +
      (MInf2 gammaInf) (DDstar2 i j)
  let approx : ℕ → WeakH2Three pair testDeriv := fun n =>
    { value := aN n
      first := daN n
      second := ddaN n
      weak_first := by
        intro i φ
        exact hSmoothFirst n i φ
      weak_second := by
        intro i j φ
        exact hSmoothSecond n i j φ }
  have h01 := physical_A7_A3_actual_value_and_gradient_strong_L2_limit
    μ gamma2 gammaInf starInf gamma2N gammaInfN starInfN
    Dgamma2 Dstar2 Dgamma2N Dstar2N
    hg hgInf hrInf hDg hDr
  have h2 := physical_A7_A3_actual_Hessian_products_strong_L2_limit
    μ gammaInf starInf gammaInfN starInfN
    Dgamma4 Dstar4 Dgamma4N Dstar4N
    DDgamma2 DDstar2 DDgamma2N DDstar2N
    hgInf hrInf hDg4 hDr4 hDDg hDDr
  have hv : Tendsto (fun n => (approx n).value) atTop (nhds a) := h01.1
  have hgrad : ∀ i, Tendsto (fun n => (approx n).first i)
      atTop (nhds (da i)) := h01.2
  have hhess : ∀ i j, Tendsto (fun n => (approx n).second i j)
      atTop (nhds (dda i j)) := h2
  exact WeakH2Three.ofStrongLimit pair testDeriv approx a da dda hv hgrad hhess

#print axioms physical_A7_actual_A3_coefficient_weak_H2_from_factor_limits

end ReservoirSeismicityControl.Paper2026
