import Mathlib
import Lightlike.Geometry.HeatKernel.LaplacianChristoffel
import Lightlike.Geometry.HeatKernel.FourthJetContract
import Lightlike.Geometry.HeatKernel.FourthJet

/-!
# The jets of the transport coefficient at the diagonal

For a solution `s` of the eikonal equation near `p` with `∂s(p) = 0` and `∂²s(p) = 2 g(p)`, the gradient of `Δs`
vanishes at `p` (`laplacian_pd_eq_zero`), so the transport coefficient `h = Δs/4 + n/2` has vanishing gradient there.
With `v_a = H^{xy} ∂_a g_{xy}` and `w_a = H^{xy} ∂_x g_{ya}` the three terms of `∂_a Δs(p)` (`Δ` in Christoffel form,
`laplacian_eq_explicit`) are `-2 v_a`, `v_a + 2 w_a` (the third jet, `thirdJet`) and `-(2 w_a - v_a)` (the lowered
Christoffel symbols, `sum_christoffel_mul_metric`).

## References

* `basile-2024`: I. Basile et al., *Lectures in Quantum Gravity*, arXiv:2412.08690v3, §4.2.5, eq. (4.81) and the vanishing
  third coincidence limit (4.91), which make the terms with `∇A₀` harmless; here the coordinate form.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U S : Set (Fin n → ℝ)} {s : (Fin n → ℝ) → ℝ}

/-- Iterated partial derivatives of a difference. -/
lemma pdL_sub' {f h : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hh : ContDiffOn ℝ ∞ h S) (hS : IsOpen S)
    (L : List (Fin n)) : ∀ y ∈ S, pdL L (fun z => f z - h z) y = pdL L f y - pdL L h y := by
  induction L with
  | nil => intro y _; rfl
  | cons a L ih =>
    intro y hy
    rw [pdL_cons, pd_congr_on hS hy ih a, pdL_cons, pdL_cons]
    unfold pd
    rw [fderiv_fun_sub (differentiableAt_of_contDiffOn' (contDiffOn_pdL hf hS _) hS hy)
      (differentiableAt_of_contDiffOn' (contDiffOn_pdL hh hS _) hS hy)]
    rfl

/-- Iterated partial derivatives of a negation. -/
lemma pdL_neg' {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (L : List (Fin n)) :
    ∀ y ∈ S, pdL L (fun z => -f z) y = -pdL L f y := by
  intro y hy
  have := pdL_sub' (f := fun _ => 0) (h := f) contDiffOn_const hf hS L y hy
  simp only [zero_sub] at this
  rw [this]
  have h0 : ∀ L : List (Fin n), ∀ y ∈ S, pdL L (fun _ => (0 : ℝ)) y = 0 := fun L =>
    pdL_eq_zero_of_eqOn hS (fun _ _ => rfl) L
  rw [h0 L y hy, zero_sub]

/-- **The Laplacian of `s` on `S`** in Christoffel form, as an explicit function. -/
lemma laplacian_eq_explicit (hg : IsCoordMetric g U) (hS : IsOpen S) (hSU : S ⊆ U) (hs : ContDiffOn ℝ ∞ s S) :
    EqOn (coordLaplacian g s) (fun y => -∑ i, ∑ j, ((g y)⁻¹ i j * pd i (pd j s) y -
      ∑ k, (g y)⁻¹ i j * (christoffel g k i j y * pd k s y))) S := by
  intro y hy
  have hgS : IsCoordMetric g S :=
    ⟨hS, fun y hy => hg.symm y (hSU hy), fun y hy => hg.isUnit_det y (hSU hy), fun i j => (hg.smooth i j).mono hSU⟩
  have h := hgS.coordLaplacian_eq_christoffel hs hy
  rw [h]
  simp only [mul_sub, Finset.mul_sum]

/-- A row of `∂_a g⁻¹` contracted with the metric: `Σ_y ∂_a g^{xy} g_{cy} = -Σ_i g^{xi} ∂_a g_{ic}`. -/
lemma sum_pd_inv_row (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a x c : Fin n) :
    ∑ y, pd a (fun z => (g z)⁻¹ x y) p * g p c y = -∑ i, (g p)⁻¹ x i * pd a (fun z => g z i c) p := by
  have := sum_pd_inv_mul_metric_right hg hp a c (fun x' => if x' = x then 1 else 0) 1
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  rw [← this]

/-- The Christoffel symbols lowered with the metric: `Σ_k Γ^k_{xy} g_{ak} = Γ_{a,xy}`. -/
lemma sum_christoffel_mul_metric (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a x y : Fin n) :
    ∑ k, christoffel g k x y p * g p a k = christoffelFirst g a x y p := by
  have hgG : g p * (g p)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hg.isUnit_det p hp)
  simp only [christoffel_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ k, (g p)⁻¹ k l * christoffelFirst g l x y p * g p a k =
      (if a = l then 1 else 0) * christoffelFirst g l x y p := fun l => by
    have h := congrFun (congrFun hgG a) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The gradient of the Laplacian of the world function vanishes at the diagonal**. -/
theorem laplacian_pd_eq_zero (hg : IsCoordMetric g U) (hS : IsOpen S) (hSU : S ⊆ U) (hs : ContDiffOn ℝ ∞ s S)
    (heik : ∀ y ∈ S, coordGradPair g s s y = 4 * s y) {p : Fin n → ℝ} (hp : p ∈ S) (hs1 : ∀ i, pd i s p = 0)
    (hs2 : ∀ i j, pd i (pd j s) p = 2 * g p i j) (a : Fin n) : pd a (coordLaplacian g s) p = 0 := by
  have hpU := hSU hp
  have hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => (g z)⁻¹ i j) S := fun i j => (Regge.Conv3.cdo_inv g hg i j).mono hSU
  have hGam : ∀ k i j, ContDiffOn ℝ ∞ (christoffel g k i j) S := fun k i j => (hg.contDiffOn_christoffel k i j).mono hSU
  have hsi : ∀ i, ContDiffOn ℝ ∞ (pd i s) S := fun i => contDiffOn_pd hs hS i
  have hsij : ∀ i j, ContDiffOn ℝ ∞ (pd i (pd j s)) S := fun i j => contDiffOn_pd (hsi j) hS i
  have E := pdL_congr_on hS (laplacian_eq_explicit hg hS hSU hs) [a] p hp
  have hinner : ∀ i j, ContDiffOn ℝ ∞ (fun y => (g y)⁻¹ i j * pd i (pd j s) y -
      ∑ k, (g y)⁻¹ i j * (christoffel g k i j y * pd k s y)) S := fun i j =>
    ((hG i j).mul (hsij i j)).sub (ContDiffOn.sum fun k _ => (hG i j).mul ((hGam k i j).mul (hsi k)))
  rw [pdL_neg' (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => hinner i j) hS [a] p hp,
    pdL_sum _ (fun i _ => ContDiffOn.sum fun j _ => hinner i j) hS [a] p hp] at E
  simp only [pdL_sum _ (fun j _ => hinner _ j) hS [a] p hp, pdL_sub' ((hG _ _).mul (hsij _ _))
    (ContDiffOn.sum fun k _ => (hG _ _).mul ((hGam k _ _).mul (hsi k))) hS [a] p hp,
    pdL_sum _ (fun k _ => (hG _ _).mul ((hGam k _ _).mul (hsi k))) hS [a] p hp,
    pdL_mul (hG _ _) (hsij _ _) hS [a] p hp, pdL_mul (hG _ _) ((hGam _ _ _).mul (hsi _)) hS [a] p hp,
    pdL_mul (hGam _ _ _) (hsi _) hS _ p hp] at E
  simp only [splits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append,
    pdL_nil, pdL_cons, hs1, hs2, mul_zero, add_zero, zero_add] at E
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at E
  -- the three contractions
  set H : Fin n → Fin n → ℝ := fun x y => (g p)⁻¹ x y with hHdef
  set D : Fin n → Fin n → Fin n → ℝ := fun i x y => pd i (fun z => g z x y) p with hDdef
  have hH : ∀ x y, H x y = H y x := fun x y => by
    have hsy : ((g p)⁻¹).transpose = (g p)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm p hpU]
    have := congrFun (congrFun hsy y) x
    rwa [Matrix.transpose_apply] at this
  have hD : ∀ i x y, D i x y = D i y x := fun i x y =>
    pd_congr_on hg.isOpen hpU (fun z hz => by
      have := congrFun (congrFun (hg.symm z hz) y) x
      rwa [Matrix.transpose_apply] at this) i
  have hgsym : ∀ x y, g p x y = g p y x := fun x y => by
    have := congrFun (congrFun (hg.symm p hpU) y) x
    rwa [Matrix.transpose_apply] at this
  have hA : ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (2 * g p x y) = -2 * ∑ x, ∑ y, H x y * D a x y := by
    have : ∀ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (2 * g p x y) = -2 * ∑ y, H x y * D a x y := fun x => by
      have h := sum_pd_inv_row hg hpU a x x
      have e : ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (2 * g p x y) =
          2 * ∑ y, pd a (fun z => (g z)⁻¹ x y) p * g p x y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      rw [e, h, Finset.mul_sum]
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [show D a x i = D a i x from hD a x i]; ring
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.mul_sum]
  have hB : ∑ x, ∑ y, (g p)⁻¹ x y * pd a (pd x (pd y s)) p =
      ∑ x, ∑ y, H x y * D a x y + 2 * ∑ x, ∑ y, H x y * D x y a := by
    have hT := fun x y => thirdJet hg hS hSU hs heik hp hs1 hs2 a x y
    simp only [pdL_cons, pdL_nil] at hT
    simp only [hT, mul_add, Finset.sum_add_distrib]
    have e : ∑ x, ∑ y, (g p)⁻¹ x y * pd y (fun w => g w a x) p = ∑ x, ∑ y, H x y * D x y a := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        show (g p)⁻¹ y x * D x a y = H x y * D x y a
        rw [hD x a y, show (g p)⁻¹ y x = H x y from hH y x]
    have e' : ∑ x, ∑ y, (g p)⁻¹ x y * pd x (fun w => g w y a) p = ∑ x, ∑ y, H x y * D x y a := rfl
    rw [e, e']
    ring
  have hC : ∑ x, ∑ y, ∑ k, (g p)⁻¹ x y * (christoffel g k x y p * (2 * g p a k)) =
      2 * ∑ x, ∑ y, H x y * D x y a - ∑ x, ∑ y, H x y * D a x y := by
    have : ∀ x y, ∑ k, (g p)⁻¹ x y * (christoffel g k x y p * (2 * g p a k)) =
        2 * (H x y * christoffelFirst g a x y p) := fun x y => by
      rw [← sum_christoffel_mul_metric hg hpU a x y, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ x, ∑ y, H x y * pd y (fun z => g z a x) p = ∑ x, ∑ y, H x y * D x y a := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        show H y x * D x a y = H x y * D x y a
        rw [hD x a y, hH y x]
    calc ∑ x, ∑ y, ∑ k, (g p)⁻¹ x y * (christoffel g k x y p * (2 * g p a k))
        = ∑ x, ∑ y, H x y * D x y a + ∑ x, ∑ y, H x y * pd y (fun z => g z a x) p -
            ∑ x, ∑ y, H x y * D a x y := by
          simp only [this, christoffelFirst, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
            show 2 * (H x y * (1 / 2 * (D x a y + D y a x - D a x y))) = H x y * D x y a + H x y * D y a x - H x y * D a x y
            rw [hD x a y]
            ring
      _ = 2 * ∑ x, ∑ y, H x y * D x y a - ∑ x, ∑ y, H x y * D a x y := by rw [e2]; ring
  rw [hA, hB, hC] at E
  rw [E]
  ring

end Lightlike
