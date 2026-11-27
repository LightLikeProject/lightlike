import Mathlib
import Lightlike.Geometry.HeatKernel.PartialJets
import Lightlike.Regge.Conv3.JetCurvature
import Lightlike.Spacetime.LaplaceBeltrami.CoordCalculus

/-!
# The jets of the world function at the diagonal

For a solution `s` of the eikonal equation `g^{ij} ∂ᵢs ∂ⱼs = 4s` near `p` with `∂s(p) = 0` and `∂²s(p) = 2 g(p)`, the
derivatives of `s` at `p` of order three are `∂_a ∂_b ∂_c s(p) = ∂_a g_{bc} + ∂_b g_{ca} + ∂_c g_{ab}` (`thirdJet`).
They follow by differentiating the eikonal equation at `p` (`eikonal_pdL`) and expanding with the Leibniz rule.

## References

* `basile-2024`: I. Basile et al., *Lectures in Quantum Gravity*, arXiv:2412.08690v3, §4.2.5, eqs. (4.82)–(4.91) (the
  coincidence limits of the world function, there in covariant form and with half the library's `σ`).
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U S : Set (Fin n → ℝ)} {s : (Fin n → ℝ) → ℝ}

/-- Iterated partial derivatives of a constant multiple. -/
lemma pdL_const_mul {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (c : ℝ) (L : List (Fin n)) :
    ∀ y ∈ S, pdL L (fun z => c * f z) y = c * pdL L f y := by
  induction L with
  | nil => intro y _; rfl
  | cons a L ih =>
    intro y hy
    rw [pdL_cons, pd_congr_on hS hy ih a, pdL_cons]
    unfold pd
    rw [fderiv_const_mul (differentiableAt_of_contDiffOn' (contDiffOn_pdL hf hS _) hS hy)]
    rfl

/-- **The differentiated eikonal equation**: the iterated partial derivatives of `g^{ij} ∂ᵢs ∂ⱼs` at a point of `S` are
`4` times those of `s`, expanded by the Leibniz rule. -/
lemma eikonal_pdL (hg : IsCoordMetric g U) (hS : IsOpen S) (hSU : S ⊆ U) (hs : ContDiffOn ℝ ∞ s S)
    (heik : ∀ y ∈ S, coordGradPair g s s y = 4 * s y) (L : List (Fin n)) {y : Fin n → ℝ} (hy : y ∈ S) :
    ∑ i, ∑ j, ((splits L).map fun AB => pdL AB.1 (fun z => (g z)⁻¹ i j) y *
        ((splits AB.2).map fun CD => pdL CD.1 (pd i s) y * pdL CD.2 (pd j s) y).sum).sum =
      4 * pdL L s y := by
  have hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => (g z)⁻¹ i j) S := fun i j =>
    (Regge.Conv3.cdo_inv g hg i j).mono hSU
  have hsi : ∀ i, ContDiffOn ℝ ∞ (pd i s) S := fun i => contDiffOn_pd hs hS i
  have heq : EqOn (fun z => ∑ i, ∑ j, (g z)⁻¹ i j * (pd i s z * pd j s z)) (fun z => 4 * s z) S := by
    intro z hz
    show _ = 4 * s z
    rw [← heik z hz]
    unfold coordGradPair
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [← pdL_const_mul hs hS 4 L y hy, ← pdL_congr_on hS heq L y hy,
    pdL_sum _ (fun i _ => ContDiffOn.sum fun j _ => (hG i j).mul ((hsi i).mul (hsi j))) hS L y hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pdL_sum _ (fun j _ => (hG i j).mul ((hsi i).mul (hsi j))) hS L y hy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pdL_mul (hG i j) ((hsi i).mul (hsi j)) hS L y hy]
  refine congrArg List.sum (List.map_congr_left fun AB _ => ?_)
  rw [pdL_mul (hsi i) (hsi j) hS AB.2 y hy]


/-- A double contraction as a matrix product. -/
lemma sum_sum_mul_mul (A B C : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n) :
    ∑ x, ∑ y, A x y * (B b x * C c y) = (B * A * C.transpose) b c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- The inverse metric contracted with the metric in its second slot. -/
lemma sum_inv_mul_metric (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (X : Fin n → ℝ) (c : Fin n) (t : ℝ) :
    ∑ x, ∑ y, (g p)⁻¹ x y * (X x * (t * g p c y)) = t * X c := by
  have hsym := hg.symm p hp
  have hinv : (g p)⁻¹ * g p = 1 := Matrix.nonsing_inv_mul _ (hg.isUnit_det p hp)
  have key : ∀ x, ∑ y, (g p)⁻¹ x y * g p c y = if x = c then 1 else 0 := by
    intro x
    have := congrFun (congrFun hinv x) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    have := congrFun (congrFun hsym c) y
    rw [Matrix.transpose_apply] at this
    rw [← this]
  calc ∑ x, ∑ y, (g p)⁻¹ x y * (X x * (t * g p c y)) = ∑ x, t * X x * ∑ y, (g p)⁻¹ x y * g p c y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = t * X c := by simp [key]

/-- The inverse metric contracted with the metric in its first slot. -/
lemma sum_inv_mul_metric' (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (Y : Fin n → ℝ) (a : Fin n) (t : ℝ) :
    ∑ x, ∑ y, (g p)⁻¹ x y * (t * g p a x * Y y) = t * Y a := by
  have hsymi : ((g p)⁻¹).transpose = (g p)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm p hp]
  rw [Finset.sum_comm]
  rw [← sum_inv_mul_metric hg hp Y a t]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have := congrFun (congrFun hsymi x) y
  rw [Matrix.transpose_apply] at this
  rw [← this]
  ring

/-- The derivative of the inverse metric contracted twice with the metric: `∂_a g^{xy} g_{bx} g_{cy} = -∂_a g_{bc}`. -/
lemma sum_pd_inv_mul_metric (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a b c : Fin n) (t : ℝ) :
    ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (t * g p b x * (t * g p c y)) = -(t * t * pd a (fun z => g z b c) p) := by
  have hsym := hg.symm p hp
  have hu := hg.isUnit_det p hp
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => pd a (fun z => g z i l) p with hD
  have hM : ∀ x y, pd a (fun z => (g z)⁻¹ x y) p = -((g p)⁻¹ * D * (g p)⁻¹) x y := by
    intro x y
    rw [Regge.Conv3.pd_inv hg hp a x y, Matrix.mul_apply]
    simp only [Matrix.mul_apply, hD, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h1 : ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (t * g p b x * (t * g p c y)) =
      t * t * ∑ x, ∑ y, (-((g p)⁻¹ * D * (g p)⁻¹)) x y * (g p b x * g p c y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hM, Matrix.neg_apply]
    ring
  rw [h1, sum_sum_mul_mul]
  have : g p * -((g p)⁻¹ * D * (g p)⁻¹) * (g p).transpose = -D := by
    rw [hsym, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [this, Matrix.neg_apply, hD, Matrix.of_apply]
  ring

/-- **The third derivatives of the world function at the diagonal**: for a solution of the eikonal equation with
`∂s(p) = 0` and `∂²s(p) = 2 g(p)`, `∂_a ∂_b ∂_c s(p) = ∂_a g_{bc} + ∂_b g_{ca} + ∂_c g_{ab}`. -/
theorem thirdJet (hg : IsCoordMetric g U) (hS : IsOpen S) (hSU : S ⊆ U) (hs : ContDiffOn ℝ ∞ s S)
    (heik : ∀ y ∈ S, coordGradPair g s s y = 4 * s y) {p : Fin n → ℝ} (hp : p ∈ S) (hs1 : ∀ i, pd i s p = 0)
    (hs2 : ∀ i j, pd i (pd j s) p = 2 * g p i j) (a b c : Fin n) :
    pdL [a, b, c] s p = pd a (fun y => g y b c) p + pd b (fun y => g y c a) p + pd c (fun y => g y a b) p := by
  have hpU := hSU hp
  have E := eikonal_pdL hg hS hSU hs heik [a, b, c] hp
  simp only [splits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, pdL_nil, pdL_cons, hs1, hs2, mul_zero, zero_mul, add_zero, zero_add] at E
  simp only [mul_add, Finset.sum_add_distrib, sum_inv_mul_metric hg hpU, sum_inv_mul_metric' hg hpU,
    sum_pd_inv_mul_metric hg hpU] at E
  -- the third derivatives in any order
  have T : ∀ L : List (Fin n), L.Perm [a, b, c] → pdL L s p = pdL [a, b, c] s p := fun L hL =>
    pdL_perm hs hS hL p hp
  have t1 : pd a (pd b (pd c s)) p = pdL [a, b, c] s p := rfl
  have t2 : pd a (pd c (pd b s)) p = pdL [a, b, c] s p := T [a, c, b] (.cons a (.swap b c []))
  have t3 : pd b (pd c (pd a s)) p = pdL [a, b, c] s p :=
    T [b, c, a] ((List.Perm.cons b (.swap a c [])).trans (.swap a b [c]))
  have gs : ∀ x y z : Fin n, pd x (fun w => g w z y) p = pd x (fun w => g w y z) p := by
    intro x y z
    refine pd_congr_on hg.isOpen hpU (fun w hw => ?_) x
    have := congrFun (congrFun (hg.symm w hw) y) z
    rw [Matrix.transpose_apply] at this
    exact this
  rw [t1, t2, t3, gs a b c, gs b c a, gs c a b] at E
  linarith

end Lightlike
