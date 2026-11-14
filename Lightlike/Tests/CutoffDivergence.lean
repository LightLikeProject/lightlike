module

public import Lightlike.Tests.TreeDependence

/-!
# The cutoff cannot be removed on the ring of three tetrahedra

On the ring `R` of three tetrahedra (`Lightlike/Tests/TreeDependence.lean`) with the star tree `T1`,
the gauge-fixed amplitude with doubled-spin cutoff `L` on every edge is computed in closed form:

* `amplitudeGF_R_T1_cutoff : amplitudeGF R T1 (fun _ => L) = ∑_{J ≤ L} (-1)^J (J + 1)^3`
  (`J` is the doubled spin `2j`, so the terms are `(-1)^{2j} (2j+1)^3`);
* `amplitudeGF_R_T1_no_limit`: hence the amplitude has **no limit** as the cutoff is removed.

`R` is not a 3-manifold (`not_isCombManifold_R`), so this does not decide whether the cutoff can be
removed on a closed combinatorial 3-manifold; that question is open.

The proof: forcing leaves the edges `24, 25, 34, 35` free; the triangles `234, 245, 345` (each with
one edge of spin `0`) force the four spins to be equal; and the colouring with spin `J` on those
edges has weight `(J+1)^4` from the edges, `1` from the triangles, and `{0 J J; 0 J J} =
(-1)^J / (J+1)` from the tetrahedron `2345`.

Contrast: when the gauge set forces every edge, the amplitude is `1` for every cutoff
(`amplitudeGF_of_forcesAll`, for example the boundary of the 4-simplex).
-/

@[expose] public section

open Finset Lightlike.Pentagon PhyslibAlpha.Sl2 Filter Topology

namespace Lightlike.PR.Test.Ring

set_option maxRecDepth 20000

/-- The four free edges of `T1`. -/
def S4 : Finset (Finset (Fin 6)) := {{2, 4}, {2, 5}, {3, 4}, {3, 5}}

lemma c1_same (J : ℕ) : c1 J J J J = fun e => if e ∈ S4 then J else 0 := by
  funext e
  simp only [c1, Function.update_apply, S4, mem_insert, mem_singleton]
  split_ifs <;> simp_all

/-- The edge factors of the colouring with spin `J` on `S4`: `((J+1)(-1)^J)^4`. -/
lemma prod_edges_c1 (J : ℕ) : ∏ e ∈ R.edges, edgeW (c1 J J J J e) = edgeW J ^ 4 := by
  rw [c1_same]
  simp only [apply_ite edgeW]
  rw [prod_ite, show edgeW 0 = 1 by simp [edgeW], prod_const_one, mul_one, prod_const,
    show #(R.edges.filter (· ∈ S4)) = 4 by decide]

/-- The triangle signs of the colouring with spin `J` on `S4` cancel: the four triangles of
`2345` each have perimeter `2J`, all others `0`. -/
lemma prod_tris_c1 (J : ℕ) : ∏ f ∈ R.tris, triW (c1 J J J J) f = 1 := by
  rw [c1_same]
  have hm : ∀ f ∈ R.tris, (∑ e ∈ f.powersetCard 2, if e ∈ S4 then J else 0) =
      J * #((f.powersetCard 2).filter (· ∈ S4)) := by
    intro f _
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_comm]
  have heven : ∀ f ∈ R.tris, #((f.powersetCard 2).filter (· ∈ S4)) % 2 = 0 := by decide
  have hsum : ∑ f ∈ R.tris, #((f.powersetCard 2).filter (· ∈ S4)) / 2 = 4 := by decide
  calc ∏ f ∈ R.tris, triW (fun e => if e ∈ S4 then J else 0) f
      = ∏ f ∈ R.tris, ((-1 : ℝ) ^ J) ^ (#((f.powersetCard 2).filter (· ∈ S4)) / 2) := by
        refine prod_congr rfl fun f hf => ?_
        rw [triW, hm f hf, ← pow_mul]
        congr 1
        have := heven f hf
        obtain ⟨k, hk⟩ : ∃ k, #((f.powersetCard 2).filter (· ∈ S4)) = 2 * k := ⟨_, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)).symm⟩
        rw [hk, Nat.mul_div_cancel_left _ (by norm_num), ← mul_assoc, mul_comm J 2,
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    _ = ((-1 : ℝ) ^ J) ^ 4 := by rw [prod_pow_eq_pow_sum, hsum]
    _ = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- The 6j symbol `{0 J J; 0 J J} = (-1)^J / (J+1)` (doubled spins). -/
lemma sixJSym_0JJ (J : ℕ) : sixJSym 0 J J 0 J J = (-1) ^ J / ((J : ℝ) + 1) := by
  have hT : Tri J J 0 := by unfold Tri; omega
  rw [sixJSym_zero_left]
  simp only [hT, and_self, ite_true]
  rw [show (J + J + 0) / 2 = J by omega, Real.mul_self_sqrt (by positivity)]

/-- The tetrahedron factors of the colouring with spin `J` on `S4`: only `2345` contributes,
with `{0 J J; 0 J J}`. -/
lemma prod_tets_c1 (J : ℕ) : ∏ t ∈ R.tets, tetW (c1 J J J J) t = (-1) ^ J / ((J : ℝ) + 1) := by
  rw [show R.tets = {{0, 1, 2, 3}, {2, 3, 4, 5}, {4, 5, 0, 1}} from rfl,
    prod_insert (by decide), prod_insert (by decide), prod_singleton,
    tetW_eq_tetAmp _ (by decide) (p := ![0, 1, 2, 3]) (by decide) (by decide),
    tetW_eq_tetAmp _ (by decide) (p := ![4, 5, 2, 3]) (by decide) (by decide),
    tetW_eq_tetAmp _ (by decide) (p := ![4, 5, 0, 1]) (by decide) (by decide),
    tetAmp_eq, tetAmp_eq, tetAmp_eq, c1_same]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [sixJSym_0JJ J, sixJSym_0JJ 0]
  norm_num

/-- **The colouring with spin `J` on the four free edges has weight `(-1)^J (J+1)^3`.** -/
theorem weight_c1_same (J : ℕ) : weight R (c1 J J J J) = (-1) ^ J * ((J : ℝ) + 1) ^ 3 := by
  rw [weight, prod_edges_c1, prod_tris_c1, prod_tets_c1, edgeW]
  have hJ : (J : ℝ) + 1 ≠ 0 := by positivity
  have h4 : ((-1 : ℝ) ^ J) ^ 4 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, h4]
  field_simp

/-- Any other colouring of the four free edges has an inadmissible triangle. -/
theorem weight_c1_ne {x y z w : ℕ} (h : ¬ (x = y ∧ y = z ∧ z = w)) : weight R (c1 x y z w) = 0 := by
  have v24 : c1 x y z w {2, 4} = x := by simp (config := { decide := true }) [c1]
  have v25 : c1 x y z w {2, 5} = y := by simp (config := { decide := true }) [c1]
  have v34 : c1 x y z w {3, 4} = z := by simp (config := { decide := true }) [c1]
  have v35 : c1 x y z w {3, 5} = w := by simp (config := { decide := true }) [c1]
  have v23 : c1 x y z w {3, 2} = 0 := by simp (config := { decide := true }) [c1]
  have v45 : c1 x y z w {4, 5} = 0 := by simp (config := { decide := true }) [c1]
  have v42 : c1 x y z w {4, 2} = x := by
    simp (config := { decide := true }) [c1, Function.update_apply]
  have v43 : c1 x y z w {4, 3} = z := by
    simp (config := { decide := true }) [c1, Function.update_apply]
  by_cases hxz : x = z
  · by_cases hxy : x = y
    · -- then `z ≠ w`: the triangle `345` fails
      refine weight_eq_zero_of_not_Tri (K := R) (p := 3) (q := 4) (r := 5) (by decide) (by decide)
        (by decide) (by decide) ?_
      rw [v35, v45, v43]
      unfold Tri
      omega
    · refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 4) (r := 5) (by decide) (by decide)
        (by decide) (by decide) ?_
      rw [v25, v45, v42]
      unfold Tri
      omega
  · refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 3) (r := 4) (by decide) (by decide)
      (by decide) (by decide) ?_
    rw [v24, v34, v23]
    unfold Tri
    omega

/-- **The gauge-fixed amplitude of the ring with the star tree, at doubled-spin cutoff `L` on every
edge, is `∑_{J ≤ L} (-1)^J (J+1)^3`** (`J = 2j`: the terms are `(-1)^{2j} (2j+1)^3`). -/
theorem amplitudeGF_R_T1_cutoff (L : ℕ) :
    amplitudeGF R T1 (fun _ => L) = ∑ J ∈ range (L + 1), (-1 : ℝ) ^ J * ((J : ℝ) + 1) ^ 3 := by
  rw [T1_force]
  simp only [amplitudeGF]
  rw [show R.edges \ insert {4, 5} (insert {1, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3}
      (insert {1, 2} T1))))) = insert {2, 4} (insert {2, 5} (insert {3, 4} (insert {3, 5} ∅)))
      from by decide,
    sum_pi_four (by decide) (by decide) (by decide)]
  change ∑ w ∈ _, ∑ z ∈ _, ∑ y ∈ _, ∑ x ∈ _, weight R (c1 x y z w) = _
  have key : ∀ x y z w : ℕ, weight R (c1 x y z w) =
      if x = y ∧ y = z ∧ z = w then (-1 : ℝ) ^ x * ((x : ℝ) + 1) ^ 3 else 0 := by
    intro x y z w
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact weight_c1_same x
    · exact weight_c1_ne h
  simp only [key]
  -- only `x = y = z = w` survives: collapse the four sums to one
  set g : ℕ → ℝ := fun x => (-1 : ℝ) ^ x * ((x : ℝ) + 1) ^ 3 with hg
  have collapse : ∀ (y : ℕ), y ∈ range (L + 1) → ∀ (P : Prop) [Decidable P],
      ∑ x ∈ range (L + 1), (if x = y ∧ P then g x else 0) = if P then g y else 0 := by
    intro y hy P _
    by_cases hP : P
    · simp only [hP, and_true, sum_ite_eq', hy, ite_true]
    · simp [hP]
  rw [sum_congr rfl fun w _ => sum_congr rfl fun z _ => sum_congr rfl fun y hy =>
    collapse y hy (y = z ∧ z = w)]
  rw [sum_congr rfl fun w _ => sum_congr rfl fun z hz => collapse z hz (z = w)]
  refine sum_congr rfl fun w hw => ?_
  rw [sum_ite_eq']
  simp [hw]

/-- **The cutoff cannot be removed for the ring**: the gauge-fixed amplitude with the star tree
has no limit as the cutoff `L` grows, since consecutive values differ by `(L+2)^3 ≥ 8`. -/
theorem amplitudeGF_R_T1_no_limit :
    ¬ ∃ A : ℝ, Tendsto (fun L : ℕ => amplitudeGF R T1 (fun _ => L)) atTop (𝓝 A) := by
  rintro ⟨A, hA⟩
  have hshift := hA.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hA
  rw [sub_self] at hdiff
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiff 1 one_pos
  have h := hN N le_rfl
  simp only [Function.comp, amplitudeGF_R_T1_cutoff, sum_range_succ (n := N + 1),
    add_sub_cancel_left] at h
  rw [Real.dist_eq, sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  have : (1 : ℝ) ≤ |(((N + 1 : ℕ) : ℝ) + 1) ^ 3| := by
    rw [abs_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
    exact one_le_pow₀ this
  linarith

end Lightlike.PR.Test.Ring
