import ReservoirSeismicityControl.Paper2026.PhysicalA7ActualA3SmoothProduct20261026
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-!
# Appendix A.2: strong L² convergence of the physical A3 Hessian product jets

The previous verified results gave integrability of the actual gamma2*Rstar
Leibniz jets and all classical derivative formulas for their smooth
approximations. This module supplies the missing *nonlinear strong-limit*
step for the four Hessian terms, including both first-derivative products.

No convergence hypothesis is imposed on a product jet. Only the standard
factor-mollification convergences in L∞, L⁴, and L² are inputs. Such factor
convergences are part of the external bounded-Lipschitz H² extension/
mollification and Sobolev embedding results, NOT proved here. In particular
strong convergence in L∞ does not follow merely from L∞ boundedness.

The continuity used below is actual Mathlib Lp Hölder multiplication, not
pointwise limit interchange. No sorry, custom axioms, or edits to frozen files.
-/

namespace ReservoirSeismicityControl.Paper2026

open MeasureTheory Filter

private instance factOneLeTwo : Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩
private instance factOneLeFour : Fact ((1 : ENNReal) ≤ 4) :=
  ⟨by norm_num⟩
private instance factOneLeTop : Fact ((1 : ENNReal) ≤ ⊤) :=
  ⟨by simp⟩

private instance holder242 : (2 : ENNReal).HolderTriple ⊤ 2 := by
  constructor
  simp

private instance holderT22 : (⊤ : ENNReal).HolderTriple 2 2 := by
  constructor
  simp

private instance holder442 : (4 : ENNReal).HolderTriple 4 2 := by
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

/-- Continuity of any *already constructed* continuous bilinear operator.
In particular, this avoids repeatedly elaborating the generic Hölder-triple
instance while proving convergence. No product-limit assumption is added. -/
private theorem continuous_bilinear_tendsto
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℕ → E) (g : ℕ → F)
    (f0 : E) (g0 : F)
    (hf : Tendsto f atTop (nhds f0))
    (hg : Tendsto g atTop (nhds g0)) :
    Tendsto (fun n => (B (f n)) (g n)) atTop (nhds ((B f0) g0)) := by
  have hcont : Continuous (Function.uncurry fun (x : E) (y : F) => (B x) y) :=
    B.continuous₂
  exact (hcont.tendsto (f0, g0)).comp (hf.prodMk_nhds hg)

/-- Strong L² convergence of ALL nine actual Hessian Leibniz candidates
from the factor approximations. It derives convergence of the nonlinear
terms instead of assuming it. L⁴ × L⁴ → L² is enough in dimension <= 3;
H² -> W¹,⁴ is a standard consequence of the paper's Sobolev assumptions.
The other terms use L² × L∞ → L² and L∞ × L² → L².

The products use the canonical Hölder Lp representative; connecting them
to the pointwise derivative formulas is the standard `holder` representative
identity from Mathlib. -/
theorem physical_A7_A3_actual_Hessian_products_strong_L2_limit
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gammaInf starInf : Lp ℝ ⊤ μ)
    (gammaInfN starInfN : ℕ → Lp ℝ ⊤ μ)
    (Dgamma4 Dstar4 : Fin 3 → Lp ℝ 4 μ)
    (Dgamma4N Dstar4N : ℕ → Fin 3 → Lp ℝ 4 μ)
    (DDgamma2 DDstar2 : Fin 3 → Fin 3 → Lp ℝ 2 μ)
    (DDgamma2N DDstar2N : ℕ → Fin 3 → Fin 3 → Lp ℝ 2 μ)
    (hg0 : Tendsto gammaInfN atTop (nhds gammaInf))
    (hr0 : Tendsto starInfN atTop (nhds starInf))
    (hg1 : ∀ i, Tendsto (fun n => Dgamma4N n i) atTop (nhds (Dgamma4 i)))
    (hr1 : ∀ i, Tendsto (fun n => Dstar4N n i) atTop (nhds (Dstar4 i)))
    (hg2 : ∀ i j, Tendsto (fun n => DDgamma2N n i j) atTop
      (nhds (DDgamma2 i j)))
    (hr2 : ∀ i j, Tendsto (fun n => DDstar2N n i j) atTop
      (nhds (DDstar2 i j))) :
    let M2Inf := ContinuousLinearMap.holderL μ
      (2 : ENNReal) (⊤ : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ)
    let M44 := ContinuousLinearMap.holderL μ
      (4 : ENNReal) (4 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ)
    let MInf2 := ContinuousLinearMap.holderL μ
      (⊤ : ENNReal) (2 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ)
    ∀ i j : Fin 3,
      Tendsto (fun n =>
        (M2Inf (DDgamma2N n i j)) (starInfN n) +
        (M44 (Dgamma4N n i)) (Dstar4N n j) +
        (M44 (Dgamma4N n j)) (Dstar4N n i) +
        (MInf2 (gammaInfN n)) (DDstar2N n i j))
        atTop (nhds (
        (M2Inf (DDgamma2 i j)) starInf +
        (M44 (Dgamma4 i)) (Dstar4 j) +
        (M44 (Dgamma4 j)) (Dstar4 i) +
        (MInf2 gammaInf) (DDstar2 i j))) := by
  dsimp
  intro i j
  have h0 := continuous_bilinear_tendsto
    (ContinuousLinearMap.holderL μ (2 : ENNReal) (⊤ : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ))
    (fun n => DDgamma2N n i j) starInfN (DDgamma2 i j) starInf
    (hg2 i j) hr0
  have h1 := continuous_bilinear_tendsto
    (ContinuousLinearMap.holderL μ (4 : ENNReal) (4 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ))
    (fun n => Dgamma4N n i) (fun n => Dstar4N n j)
    (Dgamma4 i) (Dstar4 j) (hg1 i) (hr1 j)
  have h2 := continuous_bilinear_tendsto
    (ContinuousLinearMap.holderL μ (4 : ENNReal) (4 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ))
    (fun n => Dgamma4N n j) (fun n => Dstar4N n i)
    (Dgamma4 j) (Dstar4 i) (hg1 j) (hr1 i)
  have h3 := continuous_bilinear_tendsto
    (ContinuousLinearMap.holderL μ (⊤ : ENNReal) (2 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ))
    gammaInfN (fun n => DDstar2N n i j)
    gammaInf (DDstar2 i j) hg0 (hr2 i j)
  exact ((h0.add h1).add h2).add h3

/-- Strong convergence of the zero-order physical coefficient and its three
first-order Leibniz jets. Again no product convergence assumption is made:
the two terms are obtained from L²×L∞ and L∞×L² Hölder continuity. -/
theorem physical_A7_A3_actual_value_and_gradient_strong_L2_limit
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gamma2 : Lp ℝ 2 μ) (gammaInf starInf : Lp ℝ ⊤ μ)
    (gamma2N : ℕ → Lp ℝ 2 μ)
    (gammaInfN starInfN : ℕ → Lp ℝ ⊤ μ)
    (Dgamma2 Dstar2 : Fin 3 → Lp ℝ 2 μ)
    (Dgamma2N Dstar2N : ℕ → Fin 3 → Lp ℝ 2 μ)
    (hg : Tendsto gamma2N atTop (nhds gamma2))
    (hgInf : Tendsto gammaInfN atTop (nhds gammaInf))
    (hrInf : Tendsto starInfN atTop (nhds starInf))
    (hDg : ∀ i, Tendsto (fun n => Dgamma2N n i) atTop
      (nhds (Dgamma2 i)))
    (hDr : ∀ i, Tendsto (fun n => Dstar2N n i) atTop
      (nhds (Dstar2 i))) :
    let M2Inf := ContinuousLinearMap.holderL μ
      (2 : ENNReal) (⊤ : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ)
    let MInf2 := ContinuousLinearMap.holderL μ
      (⊤ : ENNReal) (2 : ENNReal) (2 : ENNReal)
      (ContinuousLinearMap.mul ℝ ℝ)
    Tendsto (fun n => (M2Inf (gamma2N n)) (starInfN n)) atTop
      (nhds ((M2Inf gamma2) starInf)) ∧
    (∀ i : Fin 3, Tendsto (fun n =>
      (M2Inf (Dgamma2N n i)) (starInfN n) +
      (MInf2 (gammaInfN n)) (Dstar2N n i)) atTop
      (nhds ((M2Inf (Dgamma2 i)) starInf +
             (MInf2 gammaInf) (Dstar2 i)))) := by
  dsimp
  constructor
  · exact continuous_bilinear_tendsto
      (ContinuousLinearMap.holderL μ (2 : ENNReal) (⊤ : ENNReal) (2 : ENNReal)
        (ContinuousLinearMap.mul ℝ ℝ))
      gamma2N starInfN gamma2 starInf hg hrInf
  · intro i
    have h0 := continuous_bilinear_tendsto
      (ContinuousLinearMap.holderL μ (2 : ENNReal) (⊤ : ENNReal) (2 : ENNReal)
        (ContinuousLinearMap.mul ℝ ℝ))
      (fun n => Dgamma2N n i) starInfN (Dgamma2 i) starInf
      (hDg i) hrInf
    have h1 := continuous_bilinear_tendsto
      (ContinuousLinearMap.holderL μ (⊤ : ENNReal) (2 : ENNReal) (2 : ENNReal)
        (ContinuousLinearMap.mul ℝ ℝ))
      gammaInfN (fun n => Dstar2N n i)
      gammaInf (Dstar2 i) hgInf (hDr i)
    exact h0.add h1

#print axioms physical_A7_A3_actual_value_and_gradient_strong_L2_limit

#print axioms physical_A7_A3_actual_Hessian_products_strong_L2_limit

end ReservoirSeismicityControl.Paper2026
