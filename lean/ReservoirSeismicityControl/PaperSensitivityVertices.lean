import ReservoirSeismicityControl.PaperPhysicalDemandSensitivity

/-!
# Stage 46: the Appendix B sensitivity-box vertex certificate

The sensitivity intervals can be closed or degenerate. This file shows that
any predicate preserved by convex interpolation, and valid at every box vertex,
is valid at every admissible sensitivity vector. It then specializes the result
to affine scalar tests and to the symmetric quadratic control-authority test.

The vertex inequalities themselves are the *finite checks required in A6*.
They are not asserted as unconditional properties of the well allocator.
-/

namespace ReservoirSeismicityControl

open scoped Matrix

/-- Every real number between two endpoints is their convex combination,
including the case when the endpoints coincide. -/
theorem paper_interval_convex_coordinates
    (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ x = θ * a + (1 - θ) * b := by
  by_cases heq : a = b
  · subst b
    have hx : x = a := le_antisymm hb ha
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    simp [hx]
  · have hab : a < b := lt_of_le_of_ne (le_trans ha hb) heq
    have hgap : 0 < b - a := sub_pos.mpr hab
    refine ⟨(b - x) / (b - a), ?_, ?_, ?_⟩
    · exact div_nonneg (by linarith) (le_of_lt hgap)
    · apply (div_le_iff₀ hgap).2
      nlinarith
    · have hcancel : ((b - x) / (b - a)) * (b - a) = b - x :=
        div_mul_cancel₀ (b - x) (ne_of_gt hgap)
      calc
        x = b - (b - x) := by ring
        _ = b - ((b - x) / (b - a)) * (b - a) := by rw [hcancel]
        _ = ((b - x) / (b - a)) * a +
              (1 - ((b - x) / (b - a))) * b := by ring

/-- A coordinate-free finite-box lemma. There is no assumption that the
intervals have positive width. A `vertex` is a vector whose every coordinate
is one of its prescribed two endpoints. -/
theorem paper_box_vertex_propagation
    {w : ℕ}
    (lo hi h : Fin w → ℝ)
    (P : (Fin w → ℝ) → Prop)
    (hlo : ∀ i, lo i ≤ h i)
    (hhi : ∀ i, h i ≤ hi i)
    (hvertex : ∀ x, (∀ i, x i = lo i ∨ x i = hi i) → P x)
    (hconvex : ∀ x y (θ : ℝ), 0 ≤ θ → θ ≤ 1 → P x → P y →
      P (fun i => θ * x i + (1 - θ) * y i)) :
    P h := by
  classical
  have hstep : ∀ s : Finset (Fin w),
      ∀ x : Fin w → ℝ,
        (∀ i ∈ s, x i = h i) →
        (∀ i, i ∉ s → x i = lo i ∨ x i = hi i) → P x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x _ hx
        apply hvertex x
        intro i
        exact hx i (by simp)
    | @insert a s ha ih =>
        intro x hx hv
        obtain ⟨θ, hθ0, hθ1, hθeq⟩ :=
          paper_interval_convex_coordinates (lo a) (hi a) (h a) (hlo a) (hhi a)
        have hp (z : ℝ) (hz : z = lo a ∨ z = hi a) :
            P (Function.update x a z) := by
          apply ih (Function.update x a z)
          · intro i his
            have hne : i ≠ a := by
              intro heq
              subst i
              exact ha his
            simpa [hne] using hx i (Finset.mem_insert_of_mem his)
          · intro i his
            by_cases hia : i = a
            · subst i
              simpa using hz
            · have hout : i ∉ insert a s := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨hia, his⟩
              simpa [hia] using hv i hout
        have hcombine := hconvex
          (Function.update x a (lo a)) (Function.update x a (hi a)) θ
          hθ0 hθ1 (hp (lo a) (Or.inl rfl)) (hp (hi a) (Or.inr rfl))
        have hfun :
            (fun i => θ * Function.update x a (lo a) i +
              (1 - θ) * Function.update x a (hi a) i) = x := by
          funext i
          by_cases hia : i = a
          · subst i
            simpa [hx a (by simp)] using hθeq.symm
          · simp [hia]
            ring
        rw [hfun] at hcombine
        exact hcombine
  apply hstep Finset.univ h
  · intro i _
    rfl
  · intro i hi
    exact False.elim (hi (Finset.mem_univ i))

/-- An affine scalar observation achieves every lower vertex certificate
throughout the whole sensitivity box. -/
theorem paper_affine_vertex_lower_bound
    {w : ℕ} (lo hi h : Fin w → ℝ)
    (f : (Fin w → ℝ) → ℝ) (μ : ℝ)
    (hlo : ∀ i, lo i ≤ h i)
    (hhi : ∀ i, h i ≤ hi i)
    (haff : ∀ x y θ,
      f (fun i => θ * x i + (1 - θ) * y i) =
        θ * f x + (1 - θ) * f y)
    (hvertex : ∀ x, (∀ i, x i = lo i ∨ x i = hi i) → μ ≤ f x) :
    μ ≤ f h := by
  apply paper_box_vertex_propagation lo hi h (fun x => μ ≤ f x)
    hlo hhi hvertex
  intro x y θ hθ0 hθ1 hx hy
  rw [haff]
  have hleft : 0 ≤ θ * (f x - μ) :=
    mul_nonneg hθ0 (sub_nonneg.mpr hx)
  have hright : 0 ≤ (1 - θ) * (f y - μ) :=
    mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hy)
  nlinarith

/-- The same principle for an upper bound, used for the norm certificates
required for the common constant `M` in Appendix B. -/
theorem paper_affine_vertex_upper_bound
    {w : ℕ} (lo hi h : Fin w → ℝ)
    (f : (Fin w → ℝ) → ℝ) (M : ℝ)
    (hlo : ∀ i, lo i ≤ h i)
    (hhi : ∀ i, h i ≤ hi i)
    (haff : ∀ x y θ,
      f (fun i => θ * x i + (1 - θ) * y i) =
        θ * f x + (1 - θ) * f y)
    (hvertex : ∀ x, (∀ i, x i = lo i ∨ x i = hi i) → f x ≤ M) :
    f h ≤ M := by
  apply paper_box_vertex_propagation lo hi h (fun x => f x ≤ M)
    hlo hhi hvertex
  intro x y θ hθ0 hθ1 hx hy
  rw [haff]
  have hleft : 0 ≤ θ * (M - f x) :=
    mul_nonneg hθ0 (sub_nonneg.mpr hx)
  have hright : 0 ≤ (1 - θ) * (M - f y) :=
    mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hy)
  nlinarith

/-- The SR-to-SR block is affine in the actual physical well sensitivities.
No diagonal or decoupling assumption on the allocator is used. -/
theorem paper_physical_sr_sr_block_affine
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (h₀ h₁ : Fin w → ℝ) (θ : ℝ) :
    paperPhysicalSRSRBlock wellRegion β volume
      (fun j => θ * h₀ j + (1 - θ) * h₁ j) C =
      θ • paperPhysicalSRSRBlock wellRegion β volume h₀ C +
        (1 - θ) • paperPhysicalSRSRBlock wellRegion β volume h₁ C := by
  classical
  ext i j
  simp only [paperPhysicalSRSRBlock, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hmatrix := paper_physical_sr_well_affine
    wellRegion β volume h₀ h₁ θ
  have hentry (k : Fin w) :
      paperPhysicalSRWellMatrix wellRegion β volume
          (fun j => θ * h₀ j + (1 - θ) * h₁ j) i k =
        θ * paperPhysicalSRWellMatrix wellRegion β volume h₀ i k +
          (1 - θ) * paperPhysicalSRWellMatrix wellRegion β volume h₁ i k := by
    have he := congrArg (fun A : Matrix (Fin r) (Fin w) ℝ => A i k) hmatrix
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using he
  calc
    (∑ k : Fin w, paperPhysicalSRWellMatrix wellRegion β volume
          (fun j => θ * h₀ j + (1 - θ) * h₁ j) i k * C k (Sum.inr j)) =
      ∑ k : Fin w,
        (θ * paperPhysicalSRWellMatrix wellRegion β volume h₀ i k +
         (1 - θ) * paperPhysicalSRWellMatrix wellRegion β volume h₁ i k) *
          C k (Sum.inr j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hentry]
    _ = θ * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h₀ i k *
            C k (Sum.inr j)) +
        (1 - θ) * (∑ k : Fin w,
          paperPhysicalSRWellMatrix wellRegion β volume h₁ i k *
            C k (Sum.inr j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- A scalar evaluation of the physical SR authority matrix on a fixed
SR direction. This equals `vᵀ (Bhat_R(h) C_R) v`. -/
noncomputable def paper_physical_sr_quadratic
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (v : Fin r → ℝ) (h : Fin w → ℝ) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin r,
    v i * (paperPhysicalSRSRBlock wellRegion β volume h C i j * v j)

/-- The actual physical SR quadratic form is affine in the vector of well
sensitivities. This is the exact fact used for the A6 vertex test. -/
theorem paper_physical_sr_quadratic_affine
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (v : Fin r → ℝ) (h₀ h₁ : Fin w → ℝ) (θ : ℝ) :
    paper_physical_sr_quadratic wellRegion β volume C v
        (fun j => θ * h₀ j + (1 - θ) * h₁ j) =
      θ * paper_physical_sr_quadratic wellRegion β volume C v h₀ +
        (1 - θ) * paper_physical_sr_quadratic wellRegion β volume C v h₁ := by
  classical
  simp only [paper_physical_sr_quadratic]
  have hblock := paper_physical_sr_sr_block_affine
    wellRegion β volume C h₀ h₁ θ
  have hentry (i j : Fin r) :
      paperPhysicalSRSRBlock wellRegion β volume
          (fun k => θ * h₀ k + (1 - θ) * h₁ k) C i j =
        θ * paperPhysicalSRSRBlock wellRegion β volume h₀ C i j +
          (1 - θ) * paperPhysicalSRSRBlock wellRegion β volume h₁ C i j := by
    have he := congrArg (fun A : Matrix (Fin r) (Fin r) ℝ => A i j) hblock
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using he
  simp_rw [hentry]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A6's lower vertex certificate implies uniform positive SR authority
throughout the physical sensitivity box. The only remaining A6 assumption
here is the finite family of vertex inequalities themselves. -/
theorem paper_physical_sr_vertex_coercivity
    {u r w : ℕ}
    (wellRegion : Fin w → Option (Fin r))
    (β : ℝ) (volume : Fin r → ℝ)
    (C : Matrix (Fin w) (Sum (Fin u) (Fin r)) ℝ)
    (lo hi h : Fin w → ℝ) (μ : ℝ)
    (hlo : ∀ j, lo j ≤ h j)
    (hhi : ∀ j, h j ≤ hi j)
    (hvertex : ∀ hV : Fin w → ℝ,
      (∀ j, hV j = lo j ∨ hV j = hi j) →
      ∀ v : Fin r → ℝ,
        μ * (∑ i : Fin r, (v i) ^ 2) ≤
          ∑ i : Fin r,
            v i * ((paperPhysicalSRSRBlock wellRegion β volume hV C).mulVec v) i) :
    ∀ v : Fin r → ℝ,
      μ * (∑ i : Fin r, (v i) ^ 2) ≤
        ∑ i : Fin r,
          v i * ((paperPhysicalSRSRBlock wellRegion β volume h C).mulVec v) i := by
  classical
  intro v
  have hquadratic (h' : Fin w → ℝ) :
      paper_physical_sr_quadratic wellRegion β volume C v h' =
        ∑ i : Fin r,
          v i * ((paperPhysicalSRSRBlock wellRegion β volume h' C).mulVec v) i := by
    simp [paper_physical_sr_quadratic, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
  rw [← hquadratic]
  apply paper_affine_vertex_lower_bound lo hi h
    (paper_physical_sr_quadratic wellRegion β volume C v)
    (μ * (∑ i : Fin r, (v i) ^ 2)) hlo hhi
    (paper_physical_sr_quadratic_affine wellRegion β volume C v)
  intro hV hv
  rw [hquadratic]
  exact hvertex hV hv v

end ReservoirSeismicityControl
