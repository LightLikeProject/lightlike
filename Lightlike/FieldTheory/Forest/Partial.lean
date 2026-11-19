import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Finset.Sort

/-!
# Iterated partial derivatives along a finite set of coordinates

For a smooth `G : ℝ^ι → V`, `pd l G` is the partial derivative `∂_l G`, and `pdF F G` is `∏_{l ∈ F} ∂_l G`, the product
of the partial derivatives along the coordinates of a finite set `F`. Partial derivatives of a smooth function commute
(`pd_comm`), so `pdF F G` does not depend on the order (`pdF_insert`).
-/

open scoped ContDiff

namespace Lightlike.FieldTheory.Forest

variable {ι : Type*} [DecidableEq ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The partial derivative `∂_l G` of `G : ℝ^ι → V` along the coordinate `l`. -/
noncomputable def pd (l : ι) (G : (ι → ℝ) → V) : (ι → ℝ) → V := fun x => fderiv ℝ G x (Pi.single l 1)

variable [Fintype ι]

lemma contDiff_pd {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) (l : ι) : ContDiff ℝ ∞ (pd l G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- **Partial derivatives of a smooth function commute.** -/
lemma pd_comm {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) (a b : ι) : pd a (pd b G) = pd b (pd a G) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have e : ∀ u v : ι, pd u (pd v G) x = fderiv ℝ (fderiv ℝ G) x (Pi.single u 1) (Pi.single v 1) := fun u v => by
    unfold pd
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [e, e, (hG.contDiffAt.isSymmSndFDerivAt (by simp)).eq]

lemma contDiff_foldr_pd {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) (L : List ι) :
    ContDiff ℝ ∞ (L.foldr pd G) := by
  induction L with
  | nil => exact hG
  | cons a L ih => exact contDiff_pd ih a

lemma foldr_pd_perm {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) {L₁ L₂ : List ι} (h : L₁.Perm L₂) :
    L₁.foldr pd G = L₂.foldr pd G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr, ih]
  | swap x y L => exact pd_comm (contDiff_foldr_pd hG L) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The product of the partial derivatives along a finite set** of coordinates, `∏_{l ∈ F} ∂_l G`. -/
noncomputable def pdF (F : Finset ι) (G : (ι → ℝ) → V) : (ι → ℝ) → V := F.toList.foldr pd G

omit [Fintype ι] in
@[simp] lemma pdF_empty (G : (ι → ℝ) → V) : pdF ∅ G = G := by simp [pdF]

lemma contDiff_pdF {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) (F : Finset ι) : ContDiff ℝ ∞ (pdF F G) :=
  contDiff_foldr_pd hG _

/-- `∂^{F ∪ {l}} G = ∂_l ∂^F G` for `l ∉ F`. -/
lemma pdF_insert {G : (ι → ℝ) → V} (hG : ContDiff ℝ ∞ G) {F : Finset ι} {l : ι} (hl : l ∉ F) :
    pdF (insert l F) G = pd l (pdF F G) :=
  foldr_pd_perm hG (Finset.toList_insert hl)

omit [Fintype ι] in
/-- The derivative along a sum of coordinate vectors is the sum of the partial derivatives. -/
lemma fderiv_sum_single {G : (ι → ℝ) → V} (x : ι → ℝ) (T : Finset ι) :
    fderiv ℝ G x (∑ l ∈ T, Pi.single l 1) = ∑ l ∈ T, pd l G x := by
  rw [map_sum]; rfl

end Lightlike.FieldTheory.Forest
