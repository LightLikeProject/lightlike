import Lightlike.Spacetime.EHManifold.HalfSpaceDivergence
import Lightlike.Spacetime.EHManifold.PdLemmas
import Lightlike.Spacetime.EHManifold.ShearCalculus

/-!
# The divergence theorem on the region above a graph

`integral_divergence_graph`: for `γ : ℝⁿ → ℝ` of class `C²` and a `C¹` vector field `F` on `ℝⁿ⁺¹` with
compact support,

`∫_{x_i ≥ γ(x')} ∑_j ∂_j F_j = -∫_{ℝⁿ} (F_i - ∑_k ∂_k γ · F_{k'}) (x', γ(x')) dx'`,

where `x'` are the coordinates other than `x_i` and `k'` is the `k`-th of them. The right side is the flux
of `F` through the graph of `γ` with the outward (downward) normal: `ν dS = (∇γ, -1) dx'`.

The proof transports the half-space case (`integral_divergence_halfSpace`) with the shear
`x ↦ (x', x_i + γ(x'))`, which preserves Lebesgue measure.

This is Case III of the proof of the divergence theorem of Loomis–Sternberg for a boundary given as a graph.

## References

* L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6, Theorem 6.1,
  p. 421, and Case III of its proof, p. 423.
-/

open MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The shear as a measurable equivalence. -/
def shearMEquiv (γ : (Fin n → ℝ) → ℝ) (hγ : Continuous γ) (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun := shearFwd γ i
  invFun := shearBwd γ i
  left_inv := shearBwd_shearFwd γ i
  right_inv := shearFwd_shearBwd γ i
  measurable_toFun := by
    have : Continuous (shearFwd γ i) := by
      unfold shearFwd
      exact Continuous.finInsertNth i
        ((continuous_apply i).add (hγ.comp (continuous_pi fun k => continuous_apply _)))
        (continuous_pi fun k => continuous_apply _)
    exact this.measurable
  measurable_invFun := by
    have : Continuous (shearBwd γ i) := by
      unfold shearBwd
      exact Continuous.finInsertNth i
        ((continuous_apply i).sub (hγ.comp (continuous_pi fun k => continuous_apply _)))
        (continuous_pi fun k => continuous_apply _)
    exact this.measurable

lemma continuous_shearBwd (γ : (Fin n → ℝ) → ℝ) (hγ : Continuous γ) (i : Fin (n + 1)) :
    Continuous (shearBwd γ i) := by
  unfold shearBwd
  exact Continuous.finInsertNth i
    ((continuous_apply i).sub (hγ.comp (continuous_pi fun k => continuous_apply _)))
    (continuous_pi fun k => continuous_apply _)

/-- The transported vector field `G`, with `div G = (div F) ∘ Ψ` for the shear `Ψ`. -/
def shearField (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ :=
  if j = i then
    F i (shearFwd γ i x) - ∑ k : Fin n, pd k γ (i.removeNth x) * F (i.succAbove k) (shearFwd γ i x)
  else F j (shearFwd γ i x)

variable (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ) (i : Fin (n + 1))
  (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))

lemma shearField_same (x : Fin (n + 1) → ℝ) :
    shearField γ i F i x = F i (shearFwd γ i x) -
      ∑ k : Fin n, pd k γ (i.removeNth x) * F (i.succAbove k) (shearFwd γ i x) := by
  simp [shearField]

lemma shearField_succAbove (k : Fin n) (x : Fin (n + 1) → ℝ) :
    shearField γ i F (i.succAbove k) x = F (i.succAbove k) (shearFwd γ i x) := by
  simp [shearField, Fin.succAbove_ne]

include hγ in
/-- `x ↦ ∂_k γ (x')` is `C¹`. -/
lemma contDiff_pd_comp_removeNth (k : Fin n) :
    ContDiff ℝ 1 (fun x : Fin (n + 1) → ℝ => pd k γ (i.removeNth x)) := by
  have h1 : ContDiff ℝ 1 (fun y => pd k γ y) := by
    unfold pd
    exact (hγ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h1.comp (removeNthL i).contDiff

include hγ hF in
/-- The transported field is `C¹`. -/
lemma contDiff_shearField (j : Fin (n + 1)) : ContDiff ℝ 1 (shearField γ i F j) := by
  have hΨ : ContDiff ℝ 1 (shearFwd γ i) := contDiff_shearFwd γ (hγ.of_le (by norm_num)) i
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · have hfun : shearField γ j F j = fun x => F j (shearFwd γ j x) -
        ∑ k : Fin n, pd k γ (j.removeNth x) * F (j.succAbove k) (shearFwd γ j x) :=
      funext fun x => shearField_same γ j F x
    rw [hfun]
    exact ((hF j).comp hΨ).sub (ContDiff.sum fun k _ =>
      (contDiff_pd_comp_removeNth γ hγ j k).mul ((hF _).comp hΨ))
  · have hfun : shearField γ i F (i.succAbove k) = fun x => F (i.succAbove k) (shearFwd γ i x) :=
      funext fun x => shearField_succAbove γ i F k x
    rw [hfun]
    exact (hF _).comp hΨ

include hγ hF in
/-- **The divergence of the transported field** is the divergence of `F` at the sheared point. -/
theorem sum_pd_shearField (x : Fin (n + 1) → ℝ) :
    ∑ j, pd j (shearField γ i F j) x = ∑ j, pd j (F j) (shearFwd γ i x) := by
  have hγd : DifferentiableAt ℝ γ (i.removeNth x) :=
    (hγ.differentiable (by norm_num)).differentiableAt
  have hFd : ∀ j, DifferentiableAt ℝ (F j) (shearFwd γ i x) := fun j =>
    ((hF j).differentiable (by simp)).differentiableAt
  have hΨ : ContDiff ℝ 1 (shearFwd γ i) := contDiff_shearFwd γ (hγ.of_le (by norm_num)) i
  have hFΨ : ∀ j, DifferentiableAt ℝ (fun z => F j (shearFwd γ i z)) x := fun j =>
    (((hF j).comp hΨ).differentiable (by simp)).differentiableAt
  have hcoef : ∀ k, DifferentiableAt ℝ (fun z : Fin (n + 1) → ℝ => pd k γ (i.removeNth z)) x := fun k =>
    ((contDiff_pd_comp_removeNth γ hγ i k).differentiable (by simp)).differentiableAt
  -- the coefficient `∂_k γ (x')` does not depend on `x_i`
  have hcoef0 : ∀ k, pd i (fun z : Fin (n + 1) → ℝ => pd k γ (i.removeNth z)) x = 0 := by
    intro k
    have h1 : ContDiff ℝ 1 (fun y => pd k γ y) := by
      unfold pd
      exact (hγ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have h2 := ((h1.differentiable (by simp)).differentiableAt (x := removeNthL i x)).hasFDerivAt.comp x
      (removeNthL i).hasFDerivAt
    have h3 : fderiv ℝ (fun z : Fin (n + 1) → ℝ => pd k γ (i.removeNth z)) x = _ := h2.fderiv
    unfold pd at h3 ⊢
    rw [h3]
    simp [removeNth_single_same]
  -- the `i`-th term
  have hi : pd i (shearField γ i F i) x = pd i (F i) (shearFwd γ i x) -
      ∑ k : Fin n, pd k γ (i.removeNth x) * pd i (F (i.succAbove k)) (shearFwd γ i x) := by
    have hfun : shearField γ i F i = fun z => F i (shearFwd γ i z) -
        ∑ k : Fin n, pd k γ (i.removeNth z) * F (i.succAbove k) (shearFwd γ i z) :=
      funext fun z => shearField_same γ i F z
    have hprod : ∀ k, DifferentiableAt ℝ (fun z : Fin (n + 1) → ℝ =>
        pd k γ (i.removeNth z) * F (i.succAbove k) (shearFwd γ i z)) x := fun k =>
      (hcoef k).mul (hFΨ _)
    have hsumd : DifferentiableAt ℝ (fun z : Fin (n + 1) → ℝ => ∑ k : Fin n,
        pd k γ (i.removeNth z) * F (i.succAbove k) (shearFwd γ i z)) x :=
      DifferentiableAt.fun_sum fun k _ => hprod k
    rw [hfun]
    have e1 := pd_fun_sub (u := fun z => F i (shearFwd γ i z))
      (v := fun z : Fin (n + 1) → ℝ => ∑ k : Fin n,
        pd k γ (i.removeNth z) * F (i.succAbove k) (shearFwd γ i z)) (hFΨ i) hsumd i
    have e2 := pd_fun_sum Finset.univ (fun (k : Fin n) (z : Fin (n + 1) → ℝ) =>
      pd k γ (i.removeNth z) * F (i.succAbove k) (shearFwd γ i z)) (fun k _ => hprod k) i
    rw [e1, e2, pd_comp_shearFwd_same γ i (F i) x hγd (hFd i)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have e4 := pd_fun_mul (u := fun z : Fin (n + 1) → ℝ => pd k γ (i.removeNth z))
      (v := fun z => F (i.succAbove k) (shearFwd γ i z)) (hcoef k) (hFΨ (i.succAbove k)) i
    rw [e4, hcoef0 k, zero_mul, zero_add,
      pd_comp_shearFwd_same γ i (F (i.succAbove k)) x hγd (hFd _)]
  -- the other terms
  have hk : ∀ k : Fin n, pd (i.succAbove k) (shearField γ i F (i.succAbove k)) x =
      pd (i.succAbove k) (F (i.succAbove k)) (shearFwd γ i x) +
        pd k γ (i.removeNth x) * pd i (F (i.succAbove k)) (shearFwd γ i x) := by
    intro k
    have hfun : shearField γ i F (i.succAbove k) = fun z => F (i.succAbove k) (shearFwd γ i z) :=
      funext fun z => shearField_succAbove γ i F k z
    rw [hfun]
    exact pd_comp_shearFwd_succAbove γ i k (F (i.succAbove k)) x hγd (hFd _)
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ i, hi]
  simp only [hk, Finset.sum_add_distrib]
  ring

include hγ hF in
/-- **The divergence theorem on the region above a graph**, for a compactly supported `C¹` field. -/
theorem integral_divergence_graph (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x in {x : Fin (n + 1) → ℝ | γ (i.removeNth x) ≤ x i}, ∑ j, pd j (F j) x =
      -∫ y : Fin n → ℝ, (F i (i.insertNth (γ y) y) -
        ∑ k : Fin n, pd k γ y * F (i.succAbove k) (i.insertNth (γ y) y)) := by
  have hγc : Continuous γ := hγ.continuous
  -- compact support of the transported field
  have hK : IsCompact (shearBwd γ i '' ⋃ j, tsupport (F j)) :=
    (isCompact_iUnion fun j => (hc j).isCompact).image (continuous_shearBwd γ hγc i)
  have hzero : ∀ j x, x ∉ shearBwd γ i '' ⋃ j, tsupport (F j) → shearField γ i F j x = 0 := by
    intro j x hx
    have hF0 : ∀ m, F m (shearFwd γ i x) = 0 := by
      intro m
      by_contra hne
      exact hx ⟨shearFwd γ i x, mem_iUnion.2 ⟨m, subset_tsupport _ hne⟩, shearBwd_shearFwd γ i x⟩
    unfold shearField
    split_ifs <;> simp [hF0]
  have hGc : ∀ j, HasCompactSupport (shearField γ i F j) := fun j =>
    HasCompactSupport.intro hK fun x hx => hzero j x hx
  have hhalf := integral_divergence_halfSpace i (shearField γ i F)
    (fun j => contDiff_shearField γ hγ i F hF j) hGc
  -- change of variables with the shear
  have hmp := measurePreserving_shearFwd γ hγc.measurable i
  have hemb : MeasurableEmbedding (shearFwd γ i) := (shearMEquiv γ hγc i).measurableEmbedding
  have hcv := hmp.setIntegral_preimage_emb hemb (fun x => ∑ j, pd j (F j) x)
    {x : Fin (n + 1) → ℝ | γ (i.removeNth x) ≤ x i}
  have hpre : shearFwd γ i ⁻¹' {x : Fin (n + 1) → ℝ | γ (i.removeNth x) ≤ x i} =
      {x : Fin (n + 1) → ℝ | 0 ≤ x i} := by
    ext x
    exact shearFwd_mem_graph_iff γ i x
  rw [hpre] at hcv
  rw [← hcv]
  have hdiv : ∀ x, ∑ j, pd j (F j) (shearFwd γ i x) = ∑ j, pd j (shearField γ i F j) x := fun x =>
    (sum_pd_shearField γ hγ i F hF x).symm
  simp only [hdiv]
  rw [hhalf]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show shearField γ i F i (Fin.insertNth (α := fun _ => ℝ) i 0 y) = _
  rw [shearField_same]
  have h1 : shearFwd γ i (Fin.insertNth (α := fun _ => ℝ) i 0 y) =
      Fin.insertNth (α := fun _ => ℝ) i (γ y) y := by
    unfold shearFwd
    simp
  have h2 : i.removeNth (Fin.insertNth (α := fun _ => ℝ) i 0 y) = y := by simp
  rw [h1, h2]

end Lightlike
