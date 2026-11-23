module

public import Mathlib
public import Lightlike.Rows.G1_059.Minkowski2

/-!
# `Gret ∘ box = id` for the 1+1 retarded Green operator (row G1-059)

For `f : ℝ × ℝ → ℝ` of class `C²` with compact support, `Gret (box f) = f` (the `G ∘ P = id` half
of the Green operator property, BGP key `bgp-2007`, Section 3.4).  The proof is the fundamental theorem
of calculus twice, through `HasCompactSupport.integral_Iic_deriv_eq`.

* `deriv_slice2`: the partial derivative in the second variable is `fderiv f p (0,1)`;
* `Gret_box`: `Gret (box f) = f`.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.GreenOps.Mink2

/-- Slices in the first variable of a compactly supported function have compact support. -/
lemma hasCompactSupport_slice1 {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) (b : ℝ) :
    HasCompactSupport fun a => F (a, b) := by
  obtain ⟨R, hR⟩ := exists_bound hF
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_
  intro a ha
  by_contra h
  have h1 : |a| < R := (hR _ h).1
  exact ha ⟨(abs_lt.mp h1).1.le, (abs_lt.mp h1).2.le⟩

/-- Slices in the second variable of a compactly supported function have compact support. -/
lemma hasCompactSupport_slice2 {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) (a : ℝ) :
    HasCompactSupport fun b => F (a, b) := by
  obtain ⟨R, hR⟩ := exists_bound hF
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_
  intro b hb
  by_contra h
  have h1 : |b| < R := (hR _ h).2
  exact hb ⟨(abs_lt.mp h1).1.le, (abs_lt.mp h1).2.le⟩

/-- The partial derivative in the second variable of a `C¹` function. -/
lemma deriv_slice2 {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    deriv (fun v => F (a, v)) b = fderiv ℝ F (a, b) (0, 1) := by
  have h1 : HasDerivAt (fun v : ℝ => (a, v)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have h2 : HasFDerivAt F (fderiv ℝ F (a, b)) (a, b) :=
    ((hF.differentiable one_ne_zero) (a, b)).hasFDerivAt
  exact (h2.comp_hasDerivAt b h1).deriv

/-- `Gret ∘ box = id` on `C²` functions with compact support. -/
theorem Gret_box {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f) :
    Gret (box f) = f := by
  set g : ℝ × ℝ → ℝ := fun p => fderiv ℝ f p (0, 1) with hg
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hgd : ContDiff ℝ 1 g :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgc : HasCompactSupport g := hcs.fderiv_apply (𝕜 := ℝ) (0, 1)
  have hd : ∀ a b, deriv (fun v => f (a, v)) b = g (a, b) := fun a b => deriv_slice2 hf1 a b
  have hbox : ∀ a b, box f (a, b) = 4 * deriv (fun a' => g (a', b)) a := by
    intro a b
    unfold box
    dsimp only
    simp only [hd]
  have inner : ∀ u b, ∫ a in Iic u, box f (a, b) = 4 * g (u, b) := by
    intro u b
    simp_rw [hbox]
    rw [integral_const_mul]
    rw [HasCompactSupport.integral_Iic_deriv_eq (f := fun a => g (a, b))
      (hgd.comp (contDiff_id.prodMk contDiff_const)) (hasCompactSupport_slice1 hgc b) u]
  have outer : ∀ u v, ∫ b in Iic v, g (u, b) = f (u, v) := by
    intro u v
    simp_rw [← hd]
    exact HasCompactSupport.integral_Iic_deriv_eq (f := fun b => f (u, b))
      (hf1.comp (contDiff_const.prodMk contDiff_id)) (hasCompactSupport_slice2 hcs u) v
  funext ⟨u, v⟩
  unfold Gret
  dsimp only
  simp_rw [inner]
  rw [integral_const_mul, outer]
  ring

end Lightlike.GreenOps.Mink2
