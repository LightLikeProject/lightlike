import Lightlike.FieldTheory.Forest.Formula
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positivity of the forest matrix

Rivasseau–Wang (*How to resum Feynman graphs*, arXiv:1003.1037, Theorem II.1, pp. 2-3): the symmetric `n × n`
matrix `X^F(w)` with `X_ii = 1` and `X_ij = x^F_ij(w)` is positive for parameters in `[0, 1]`. The source writes it as
a convex combination `∑_k (w_{k-1} - w_k) X^{F,k}` of block matrices of ones (eq. (II-4)); here the same decomposition
in integral form, `X_ij = ∫_0^1 1[i, j joined by the links with w ≥ t] dt` (`le_ultra_iff`), each block matrix being
positive (`sum_block_nonneg`).

## Main results

* `posSemidef_forestMatrix`: the forest matrix is positive semidefinite for parameters at most `1`.
* `le_ultra_iff`: the level sets of the ultrametric are the clusters of the links with large parameters.

## References

* V. Rivasseau, Z. Wang, arXiv:1003.1037, Theorem II.1 and eqs. (II-2)-(II-4), pp. 2-3.
-/

open MeasureTheory Set Finset

namespace Lightlike.FieldTheory.Forest

variable {n : ℕ}

lemma ultra_of_not_joined {F : Finset (Link n)} {w : Link n → ℝ} {a b : Fin n} (h : ¬ Joined F a b) :
    ultra F w a b = 0 := by
  rcases ultra_cases F w a b with h0 | ⟨l, -, hj, -⟩
  · exact h0
  · exact absurd (hj.mono (above_subset F w _)) h

lemma ultra_le_one {F : Finset (Link n)} {w : Link n → ℝ} (hw : ∀ l ∈ F, w l ≤ 1) (a b : Fin n) :
    ultra F w a b ≤ 1 := by
  rcases ultra_cases F w a b with h0 | ⟨l, hl, -, he⟩
  · rw [h0]; exact zero_le_one
  · rw [he]; exact hw l hl

/-- **The level sets of the ultrametric**: for `t > 0`, `t ≤ x^F_ab(w)` exactly when `a` and `b` are joined by the
links of `F` with `w ≥ t`. -/
lemma le_ultra_iff {F : Finset (Link n)} {w : Link n → ℝ} {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : 0 < t) :
    t ≤ ultra F w a b ↔ Joined (above F w t) a b := by
  constructor
  · intro h
    rcases ultra_cases F w a b with h0 | ⟨l, -, hj, he⟩
    · rw [h0] at h; exact absurd h (not_le.2 ht)
    · rw [he] at h
      exact hj.mono fun m hm => mem_above.2 ⟨(mem_above.1 hm).1, h.trans (mem_above.1 hm).2⟩
  · rintro ⟨q⟩
    obtain ⟨l₀, hl₀, he₀⟩ := Finset.exists_mem_eq_inf' (walkLinks_nonempty hab q) w
    have hl₀' := mem_above.1 (mem_walkLinks.1 hl₀).1
    have hj₀ : Joined (above F w (w l₀)) a b := by
      refine ⟨q.transfer (graphOf (above F w (w l₀))) fun e he => ?_⟩
      obtain ⟨l, hl, rfl⟩ := mem_edgeSet_graphOf.1 (q.edges_subset_edgeSet he)
      refine mem_edgeSet_graphOf.2 ⟨l, mem_above.2 ⟨(mem_above.1 hl).1, ?_⟩, rfl⟩
      rw [← he₀]
      exact Finset.inf'_le _ (mem_walkLinks.2 ⟨hl, he⟩)
    exact hl₀'.2.trans (le_ultra hl₀'.1 hj₀)

/-- **A block matrix of ones is positive**: for the matrix `c` with `c_ij = 1` when `i` and `j` are in the same
connected component of `G` and `0` otherwise, `∑_ij x_i c_ij x_j = ∑_C (∑_{i ∈ C} x_i)² ≥ 0`. -/
lemma sum_block_nonneg (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (c : Fin n → Fin n → ℝ)
    (h1 : ∀ i j, G.Reachable i j → c i j = 1) (h0 : ∀ i j, ¬ G.Reachable i j → c i j = 0) :
    0 ≤ ∑ i, x i * ∑ j, c i j * x j := by
  classical
  set f := G.connectedComponentMk
  set S : G.ConnectedComponent → ℝ := fun C => ∑ j ∈ univ.filter (fun j => f j = C), x j
  have hrow : ∀ i, ∑ j, c i j * x j = S (f i) := fun i => by
    simp only [S, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : G.Reachable i j
    · rw [h1 i j h, one_mul, ite_eq_left (SimpleGraph.ConnectedComponent.eq.2 h.symm)]
    · rw [h0 i j h, zero_mul, ite_eq_right (fun h' => h (SimpleGraph.ConnectedComponent.eq.1 h').symm)]
  have hsq : ∑ i, x i * S (f i) = ∑ C ∈ univ.image f, S C * S C := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image f) (g := f)
      fun i _ => mem_image_of_mem f (mem_univ i)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [show S C * S C = (∑ j ∈ univ.filter (fun j => f j = C), x j) * S C from rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  simp_rw [hrow]
  rw [hsq]
  exact Finset.sum_nonneg fun C _ => mul_self_nonneg _

/-- The matrix `X^F(w)` (Rivasseau–Wang, Theorem II.1): `1` on the diagonal, `x^F_ij(w)` off it. -/
noncomputable def forestMatrix (F : Finset (Link n)) (w : Link n → ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  classical exact fun i j => if i = j then 1 else ultra F w i j

lemma forestMatrix_diag (F : Finset (Link n)) (w : Link n → ℝ) (i : Fin n) : forestMatrix F w i i = 1 := by
  classical simp [forestMatrix]

lemma forestMatrix_of_ne (F : Finset (Link n)) (w : Link n → ℝ) {i j : Fin n} (h : i ≠ j) :
    forestMatrix F w i j = ultra F w i j := by
  classical simp [forestMatrix, h]

/-- The off-diagonal entries of `X^F(w)` are the entries of the point `X^F(w)` of the forest formula. -/
lemma forestMatrix_eq_forestPoint (F : Finset (Link n)) (w : Link n → ℝ) {e : Link n} {a b : Fin n}
    (he : e.1 = s(a, b)) : forestMatrix F w a b = forestPoint F w e := by
  have hab : a ≠ b := fun h => e.2 (by rw [he, h]; exact Sym2.mk_isDiag_iff.2 rfl)
  rw [forestMatrix_of_ne F w hab]
  by_cases hl : Linked F e
  · rw [forestPoint, interp_of_linked hl, ultraL_of_eq he]
  · rw [forestPoint_of_not_linked hl, ultra_of_not_joined fun h => hl ((linked_iff_of_eq he).2 h)]

/-- For `u ∈ [0, 1]`, `u = ∫_0^1 1[t ≤ u] dt`. -/
lemma integral_indicator_Iic {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∫ t in Ioc (0 : ℝ) 1, (Iic u).indicator 1 t = u := by
  rw [integral_indicator_one measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic]
  have : Iic u ∩ Ioc (0 : ℝ) 1 = Ioc 0 u := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨h, h0, -⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨h, h0, h.trans hu.2⟩
  rw [this, Real.volume_real_Ioc, sub_zero, max_eq_left hu.1]

/-- **The forest matrix is positive** (Rivasseau–Wang, Theorem II.1, pp. 2-3): for parameters `w_l ≤ 1` on `F`,
`X^F(w)` is symmetric and `∑_ij x_i X^F_ij(w) x_j ≥ 0`. -/
theorem posSemidef_forestMatrix (F : Finset (Link n)) {w : Link n → ℝ} (hw : ∀ l ∈ F, w l ≤ 1) :
    (forestMatrix F w).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · rw [star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · rw [forestMatrix_of_ne F w h, forestMatrix_of_ne F w (Ne.symm h), ultra_symm]
  have hM : ∀ i j, forestMatrix F w i j ∈ Icc (0 : ℝ) 1 := fun i j => by
    by_cases h : i = j
    · subst h; rw [forestMatrix_diag]; exact ⟨zero_le_one, le_rfl⟩
    · rw [forestMatrix_of_ne F w h]; exact ⟨ultra_nonneg _ _ _ _, ultra_le_one hw _ _⟩
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set c : Fin n → Fin n → ℝ → ℝ := fun i j => (Iic (forestMatrix F w i j)).indicator 1
  have hc : ∀ i j, Integrable (c i j) μ := fun i j => (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hint : ∀ i, Integrable (fun t => x i * ∑ j, c i j t * x j) μ := fun i =>
    (integrable_finsetSum _ fun j _ => (hc i j).mul_const _).const_mul _
  have hsum : star x ⬝ᵥ (forestMatrix F w).mulVec x = ∫ t, ∑ i, x i * ∑ j, c i j t * x j ∂μ := by
    simp only [star_trivial, dotProduct, Matrix.mulVec]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hc i j).mul_const _]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    exact congrArg (· * x j) (integral_indicator_Iic (hM i j)).symm
  rw [hsum]
  refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
  refine sum_block_nonneg (graphOf (above F w t)) x (fun i j => c i j t) (fun i j hj => ?_) (fun i j hj => ?_)
  · refine indicator_of_mem ?_ _
    by_cases h : i = j
    · subst h; rw [Set.mem_Iic, forestMatrix_diag]; exact ht.2
    · rw [Set.mem_Iic, forestMatrix_of_ne F w h]; exact (le_ultra_iff h ht.1).2 hj
  · refine indicator_of_notMem (fun hm => hj ?_) _
    by_cases h : i = j
    · subst h; exact SimpleGraph.Reachable.refl i
    · rw [Set.mem_Iic, forestMatrix_of_ne F w h] at hm; exact (le_ultra_iff h ht.1).1 hm

end Lightlike.FieldTheory.Forest
