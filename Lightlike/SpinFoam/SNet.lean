import Lightlike.SpinFoam.Vertex
import Lightlike.Recoupling.Loop

/-!
# Signed spin networks

The Pachner moves of the Ooguri model are proven by rewriting the product of the vertex amplitudes
of a configuration of 4-simplices, summed over its internal colours, into a network of
intertwiners whose shape is visibly the same for both sides of the move. This file sets up the
networks and the rewriting steps.

A **signed network** `S : SNet F E N` has edges `E` and nodes `N` (finite types), with live
flags. A live edge `e` carries the face `face e` (a triangle, whose colour is its spin) and a flag
`kap e`; a live node `n` carries the face `tet n` (a tetrahedron, whose colour is its virtual spin)
and four legs: the leg `l` sits on the edge `leg n l` with the sign `neg n l`. A list of
**constraints** `(e₁, e₂, b)` asks `x e₂ = ± x e₁`, and a list `cst` of faces gives the constant
sign `Π_{f ∈ cst} (-1)^{col f}`. With a colouring `col` of the faces the network evaluates to
(`ev`)

`Π_{f ∈ cst} (-1)^{col f} · Σ_x Π_{e, kap e} (-1)^{(j_e - x_e)/2} · Π_n ι_{tet n}(± x_{leg n l}) ·
  Π_{(e₁, e₂, b)} [x e₂ = ± x e₁]`,

where `x` runs over the admissible projections of the live edges (`0` on the dead ones), `j_e` is
the spin of `face e`, and `ι_t` is the canonical intertwiner of the tetrahedron `t` with the spins
of its legs' faces (`nodeT`, the leg order of `canonTet`).

## Main results

* `sum_pi_mul_of_dep`: a sum over a box of a product of two factors that depend on complementary
  sets of coordinates is the product of the two sums.
* `ev_subst`: eliminating a constraint `x e₂ = ± x e₁` (the edge `e₂` dies and its references move
  to `e₁`).
* `ev_flipNode`, `ev_flipVar`, `ev_addParity`: gauge changes that leave the evaluation unchanged.
* `ev_glue`, `ev_loop`: summing the virtual spin of a tetrahedron shared by two nodes glues them;
  summing also the spin of a triangle closes a loop.
* `ev_relabel`, `ev_union`: relabelling edges and nodes; a disjoint union is a product.
* `ev_vnet`: the vertex network of a 4-simplex evaluates to its vertex contraction.
* `isInv_rem_vnet`, `isInv_rem_block`: a vertex network without one node is an invariant tensor,
  also as an untouched block of a larger network (the hypothesis of `ev_glue`).

## References

* `martin-dussaud-2019`, §5.6: Yutsis diagrams, the graphical calculus of angular-momentum
  recoupling (Yutsis, Levinson, Vanagas, *Mathematical Apparatus of the Theory of Angular Momentum*,
  1962).
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam

/-! ## Boxes, signs and the node tensor -/

/-- The admissible projections of a doubled spin `j`: `-j ≤ μ ≤ j` with `j - μ` even. -/
def pbox (j : ℕ) : Finset ℤ := (Icc (-(j : ℤ)) j).filter fun μ => ((j : ℤ) - μ) % 2 = 0

lemma mem_pbox {j : ℕ} {μ : ℤ} : μ ∈ pbox j ↔ AdmProj j μ := by
  simp [pbox, AdmProj, and_assoc]

/-- `x` for `b = false`, `-x` for `b = true`. -/
def sg (b : Bool) (x : ℤ) : ℤ := if b then -x else x

@[simp] lemma sg_false (x : ℤ) : sg false x = x := rfl
@[simp] lemma sg_true (x : ℤ) : sg true x = -x := rfl

lemma sg_sg (a b : Bool) (x : ℤ) : sg a (sg b x) = sg (xor a b) x := by
  cases a <;> cases b <;> simp [sg]

lemma sg_eq_iff {b : Bool} {x y : ℤ} : sg b x = y ↔ x = sg b y := by
  cases b <;> simp [sg]; omega

lemma sg_mem_pbox {b : Bool} {j : ℕ} {μ : ℤ} : sg b μ ∈ pbox j ↔ μ ∈ pbox j := by
  cases b
  · rfl
  · rw [sg_true, mem_pbox, mem_pbox, admProj_neg]

lemma edgeSign_mul_self (j : ℕ) (m : ℤ) : edgeSign j m * edgeSign j m = 1 := by
  unfold edgeSign
  rw [← mul_zpow]; norm_num

lemma edgeSign_sg {b : Bool} {j : ℕ} {m : ℤ} (h : m ∈ pbox j) :
    edgeSign j (sg b m) = (if b then (-1) ^ j else 1) * edgeSign j m := by
  cases b
  · simp
  · rw [sg_true, edgeSign_neg (mem_pbox.1 h).2.2]; simp

/-- The canonical intertwiner of a tetrahedron `t` whose legs lie on the faces `f l`, in the leg
order of `canonTet`: the virtual spin `col t` couples the legs `0` and `2`. -/
noncomputable def nodeT {F : Type*} (col : F → ℕ) (t : F) (f : Fin 4 → F) (m : Fin 4 → ℤ) : ℝ :=
  fourJ (col (f 0)) (col (f 2)) (col (f 1)) (col (f 3)) (col t) (m 0) (m 2) (m 1) (m 3)

/-- The sign `Π_{f ∈ l} (-1)^{col f}` of a list of faces. -/
noncomputable def fsign {F : Type*} (l : List F) (col : F → ℕ) : ℝ :=
  (l.map fun f => (-1 : ℝ) ^ col f).prod

@[simp] lemma fsign_nil {F : Type*} (col : F → ℕ) : fsign [] col = 1 := rfl

@[simp] lemma fsign_cons {F : Type*} (f : F) (l : List F) (col : F → ℕ) :
    fsign (f :: l) col = (-1) ^ col f * fsign l col := by
  simp [fsign]

lemma fsign_append {F : Type*} (l₁ l₂ : List F) (col : F → ℕ) :
    fsign (l₁ ++ l₂) col = fsign l₁ col * fsign l₂ col := by
  simp [fsign]

/-- Taking the face `f₀` out of the constant sign leaves the factor `((-1)^{col f₀})^{count}`. -/
lemma fsign_filter {F : Type*} [DecidableEq F] (l : List F) (col : F → ℕ) (f₀ : F) :
    fsign l col = fsign (l.filter (· ≠ f₀)) col * ((-1 : ℝ) ^ col f₀) ^ l.count f₀ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = f₀
    · subst h
      simp only [fsign_cons, ih, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.count_cons_self, pow_succ]
      ring
    · simp only [fsign_cons, ih, List.filter_cons, ne_eq, h, not_false_eq_true, decide_true,
        ↓reduceIte, List.count_cons, beq_iff_eq, add_zero]
      ring

/-- A face that occurs an even number of times can be dropped from the constant sign. -/
lemma fsign_filter_of_even {F : Type*} [DecidableEq F] {l : List F} (col : F → ℕ) {f₀ : F}
    (h : Even (l.count f₀)) : fsign l col = fsign (l.filter (· ≠ f₀)) col := by
  rw [fsign_filter l col f₀, ← pow_mul, mul_comm (col f₀), pow_mul, h.neg_one_pow, one_pow,
    mul_one]

/-- The constant sign only sees the parity of the number of times each face occurs. -/
lemma fsign_eq_of_count {F : Type*} [DecidableEq F] {l₁ l₂ : List F} (col : F → ℕ)
    (h : ∀ f ∈ l₁ ++ l₂, l₁.count f % 2 = l₂.count f % 2) : fsign l₁ col = fsign l₂ col := by
  have hp : ∀ (f : F) (n : ℕ), ((-1 : ℝ) ^ col f) ^ n = ((-1 : ℝ) ^ col f) ^ (n % 2) := by
    intro f n
    have h2 : ((-1 : ℝ) ^ col f) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, h2, one_pow, one_mul]
  have hext : ∀ l : List F, l.toFinset ⊆ (l₁ ++ l₂).toFinset → fsign l col =
      ∏ f ∈ (l₁ ++ l₂).toFinset, ((-1 : ℝ) ^ col f) ^ l.count f := by
    intro l hl
    unfold fsign
    rw [prod_list_map_count]
    refine prod_subset hl fun f _ hf => ?_
    rw [List.count_eq_zero_of_not_mem (fun h' => hf (List.mem_toFinset.2 h')), pow_zero]
  rw [hext l₁ (by intro f hf; simp only [List.mem_toFinset, List.mem_append] at hf ⊢; tauto),
    hext l₂ (by intro f hf; simp only [List.mem_toFinset, List.mem_append] at hf ⊢; tauto)]
  refine prod_congr rfl fun f hf => ?_
  rw [hp f (l₁.count f), hp f (l₂.count f), h f (List.mem_toFinset.1 hf)]

lemma sg_not (b : Bool) (x : ℤ) : sg (!b) x = -sg b x := by
  cases b <;> simp [sg]

/-- The projections of a nonzero intertwiner sum to zero. -/
lemma sum_of_fourJ_ne_zero {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ}
    (h : fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ ≠ 0) : m₁ + m₂ + m₃ + m₄ = 0 := by
  have := (isInv_fourJT j₁ j₂ j₃ j₄ k).weight ![m₁, m₂, m₃, m₄] (by simpa [fourJT] using h)
  simpa [Fin.sum_univ_four, add_assoc] using this

/-- Reversing all legs of a node tensor gives the sign `(-1)^{(j₀+j₁+j₂+j₃)/2}`. -/
lemma nodeT_neg {F : Type*} (col : F → ℕ) (t : F) (f : Fin 4 → F) (u : Fin 4 → ℤ) :
    nodeT col t f (fun l => -u l) =
      (-1) ^ ((col (f 0) + col (f 2) + col (f 1) + col (f 3)) / 2) * nodeT col t f u := by
  unfold nodeT; exact fourJ_neg _ _ _ _ _ _ _ _ _

/-- **Flipping a node.** Reversing the signs of all four legs of a node tensor, the edge signs of
its legs are traded for the signs `(-1)^j` of the legs that were read without sign. -/
lemma nodeT_flip {F : Type*} (col : F → ℕ) (t : F) (f : Fin 4 → F) (τ : Fin 4 → Bool)
    (x : Fin 4 → ℤ) (hx : ∀ l, x l ∈ pbox (col (f l))) :
    nodeT col t f (fun l => sg (τ l) (x l)) * ∏ l, edgeSign (col (f l)) (x l) =
      nodeT col t f (fun l => sg (!τ l) (x l)) *
        ∏ l, (if τ l then 1 else (-1) ^ col (f l)) := by
  set u : Fin 4 → ℤ := fun l => sg (τ l) (x l) with hu
  have hneg : (fun l => sg (!τ l) (x l)) = fun l => -u l := by
    funext l; simp [hu, sg_not]
  rw [hneg, nodeT_neg]
  by_cases h0 : nodeT col t f u = 0
  · simp [h0]
  have hsum := sum_of_fourJ_ne_zero h0
  have hev := even_of_fourJ_ne_zero h0
  have hxu : ∀ l, x l = sg (τ l) (u l) := by intro l; simp [hu, sg_sg]
  have hup : ∀ l, u l ∈ pbox (col (f l)) := fun l => sg_mem_pbox.2 (hx l)
  have hE : ∀ l, edgeSign (col (f l)) (x l) =
      (if τ l then (-1) ^ col (f l) else 1) * edgeSign (col (f l)) (u l) := by
    intro l; rw [hxu l]; exact edgeSign_sg (hup l)
  have hP : ∏ l, edgeSign (col (f l)) (u l) =
      (-1) ^ ((col (f 0) + col (f 2) + col (f 1) + col (f 3)) / 2) := by
    have h0' := (mem_pbox.1 (hup 0)).2.2
    have h1' := (mem_pbox.1 (hup 1)).2.2
    have h2' := (mem_pbox.1 (hup 2)).2.2
    have h3' := (mem_pbox.1 (hup 3)).2.2
    simp only [Fin.prod_univ_four, edgeSign]
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      ← zpow_natCast]
    congr 1
    push_cast
    omega
  have hQ : ∏ l, (if τ l then (1 : ℝ) else (-1) ^ col (f l)) =
      ∏ l, (if τ l then (-1) ^ col (f l) else 1) := by
    have h1 : ∀ l, (if τ l then (1 : ℝ) else (-1) ^ col (f l)) =
        (-1) ^ col (f l) * (if τ l then (-1) ^ col (f l) else 1) := by
      intro l; split_ifs
      · rw [← pow_add, ← two_mul, pow_mul]; norm_num
      · rw [mul_one]
    rw [prod_congr rfl fun l _ => h1 l, prod_mul_distrib, prod_pow_eq_pow_sum, Fin.sum_univ_four,
      Even.neg_one_pow (Nat.even_iff.2 (by omega)), one_mul]
  rw [prod_congr rfl fun l _ => hE l, prod_mul_distrib, hP, hQ]
  ring

/-! ## Factorization of sums over boxes -/

section Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Factorization.** A sum over a box of a product `φ x · ψ x`, where `φ` depends only on the
coordinates in `p` and `ψ` only on the others, is the product of the sum of `φ` (the other
coordinates set to `0`) and the sum of `ψ` (the coordinates in `p` set to `0`). -/
lemma sum_pi_mul_of_dep (B : ι → Finset ℤ) (p : ι → Prop) [DecidablePred p]
    (φ ψ : (ι → ℤ) → ℝ) (hφ : ∀ x, φ x = φ fun i => if p i then x i else 0)
    (hψ : ∀ x, ψ x = ψ fun i => if p i then 0 else x i) :
    ∑ x ∈ Fintype.piFinset B, φ x * ψ x =
      (∑ x ∈ Fintype.piFinset (fun i => if p i then B i else {0}), φ x) *
        ∑ x ∈ Fintype.piFinset (fun i => if p i then {0} else B i), ψ x := by
  rw [sum_mul_sum, ← sum_product']
  symm
  apply sum_nbij' (fun yz => fun i => if p i then yz.1 i else yz.2 i)
    (fun x => (fun i => if p i then x i else 0, fun i => if p i then 0 else x i))
  · rintro ⟨y, z⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro i
    by_cases hi : p i
    · simpa [hi] using h.1 i
    · simpa [hi] using h.2 i
  · intro x hx
    simp only [mem_product, Fintype.mem_piFinset] at hx ⊢
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases hi : p i <;> simp [hi, hx i]
  · rintro ⟨y, z⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h
    simp only [Prod.mk.injEq]
    constructor
    · funext i; by_cases hi : p i
      · simp [hi]
      · have := h.1 i; simp only [hi, ↓reduceIte, mem_singleton] at this; simp [hi, this]
    · funext i; by_cases hi : p i
      · have := h.2 i; simp only [hi, ↓reduceIte, mem_singleton] at this; simp [hi, this]
      · simp [hi]
  · intro x _
    funext i; by_cases hi : p i <;> simp [hi]
  · rintro ⟨y, z⟩ _
    simp only
    rw [hφ (fun i => if p i then y i else z i), hψ (fun i => if p i then y i else z i), hφ y, hψ z]
    congr 2 <;> funext i <;> by_cases hi : p i <;> simp [hi]

/-- **Splitting a box.** A sum over a box is a double sum: over the coordinates outside `p` (those in
`p` set to `0`), and over the coordinates in `p` (the others set to `0`), of the merged point. -/
lemma sum_pi_split (B : ι → Finset ℤ) (p : ι → Prop) [DecidablePred p] (G : (ι → ℤ) → ℝ) :
    ∑ x ∈ Fintype.piFinset B, G x =
      ∑ y ∈ Fintype.piFinset (fun i => if p i then {0} else B i),
        ∑ z ∈ Fintype.piFinset (fun i => if p i then B i else {0}),
          G (fun i => if p i then z i else y i) := by
  rw [← sum_product']
  symm
  apply sum_nbij' (fun yz => fun i => if p i then yz.2 i else yz.1 i)
    (fun x => (fun i => if p i then 0 else x i, fun i => if p i then x i else 0))
  · rintro ⟨y, z⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro i
    by_cases hi : p i
    · simpa [hi] using h.2 i
    · simpa [hi] using h.1 i
  · intro x hx
    simp only [mem_product, Fintype.mem_piFinset] at hx ⊢
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases hi : p i <;> simp [hi, hx i]
  · rintro ⟨y, z⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h
    simp only [Prod.mk.injEq]
    constructor
    · funext i; by_cases hi : p i
      · have := h.1 i; simp only [hi, ↓reduceIte, mem_singleton] at this; simp [hi, this]
      · simp [hi]
    · funext i; by_cases hi : p i
      · simp [hi]
      · have := h.2 i; simp only [hi, ↓reduceIte, mem_singleton] at this; simp [hi, this]
  · intro x _
    funext i; by_cases hi : p i <;> simp [hi]
  · rintro ⟨y, z⟩ _
    rfl

/-- Two products agree when the factors are `1` off two sets that correspond bijectively,
factor by factor. -/
lemma prod_live {α β : Type*} [Fintype α] [Fintype β] (p : α → Bool) (q : β → Bool)
    (σ : α → β) (τ : β → α) (hσ : ∀ a, p a = true → q (σ a) = true ∧ τ (σ a) = a)
    (hτ : ∀ b, q b = true → p (τ b) = true ∧ σ (τ b) = b) (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ a, p a = false → f a = 1) (hg : ∀ b, q b = false → g b = 1)
    (hfg : ∀ a, p a = true → f a = g (σ a)) : ∏ a, f a = ∏ b, g b := by
  rw [← prod_filter_of_ne (p := fun a => p a = true) fun a _ h => by
      by_contra h'; exact h (hf a (by simpa using h')),
    ← prod_filter_of_ne (p := fun b => q b = true) fun b _ h => by
      by_contra h'; exact h (hg b (by simpa using h'))]
  refine prod_nbij' σ τ (fun a ha => ?_) (fun b hb => ?_) (fun a ha => ?_) (fun b hb => ?_)
    (fun a ha => ?_)
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact (hσ a ha).1
  · simp only [mem_filter, mem_univ, true_and] at hb ⊢; exact (hτ b hb).1
  · simp only [mem_filter, mem_univ, true_and] at ha; exact (hσ a ha).2
  · simp only [mem_filter, mem_univ, true_and] at hb; exact (hτ b hb).2
  · simp only [mem_filter, mem_univ, true_and] at ha; exact hfg a ha

end Factor

/-- **Absorbing a projector into an invariant tensor.** For an invariant tensor `R` with four
incoming legs of spins `j`, the projector `Σ_k ι^{(k)} ⊗ ι^{(k)}` (intertwiners in the leg order
`(0 2 1 3)`, summed over any cutoff at least `j 0 + j 2`) contracted with `R` gives `R` back. -/
lemma absorb {j : Fin 4 → ℕ} {R : (Fin 4 → ℤ) → ℝ} (hR : IsInv j (fun _ => false) R) (cut : ℕ)
    (hcut : j 0 + j 2 ≤ cut) (v : Fin 4 → ℤ) :
    ∑ k ∈ range (cut + 1), fourJ (j 0) (j 2) (j 1) (j 3) k (v 0) (v 2) (v 1) (v 3) *
      ∑ m ∈ Fintype.piFinset (fun l => Icc (-(j l : ℤ)) (j l)),
        fourJ (j 0) (j 2) (j 1) (j 3) k (m 0) (m 2) (m 1) (m 3) * R m = R v := by
  have s0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have s1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have s2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have s3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have hX := hR.reindex (Equiv.swap (1 : Fin 4) 2)
  have e1 : j ∘ (Equiv.swap (1 : Fin 4) 2) = ![j 0, j 2, j 1, j 3] := by
    funext i; fin_cases i <;> simp [s0, s1, s2, s3]
  have e2 : ((fun _ => false : Fin 4 → Bool) ∘ (Equiv.swap (1 : Fin 4) 2)) =
      ![false, false, false, false] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2] at hX
  have h := eq_sum_fourJ hX (v ∘ Equiv.swap (1 : Fin 4) 2)
  have hvv : (v ∘ Equiv.swap (1 : Fin 4) 2) ∘ (Equiv.swap (1 : Fin 4) 2).symm = v := by
    funext i; simp
  simp only [hvv] at h
  rw [h, ← Finset.sum_subset (range_subset_range.2 (by omega : j 0 + j 2 + 1 ≤ cut + 1))]
  · refine sum_congr rfl fun k _ => ?_
    have hin : (∑ m ∈ Fintype.piFinset (fun l => Icc (-(j l : ℤ)) (j l)),
        fourJ (j 0) (j 2) (j 1) (j 3) k (m 0) (m 2) (m 1) (m 3) * R m) =
        ∑ n ∈ box4 (j 0) (j 2) (j 1) (j 3), fourJT (j 0) (j 2) (j 1) (j 3) k n *
          R (n ∘ (Equiv.swap (1 : Fin 4) 2).symm) := by
      rw [← box4_eq j, sum_box4_perm j (Equiv.swap 1 2)]
      simp only [s0, s1, s2, s3, Equiv.symm_swap, fourJT, Function.comp_apply]
    have hv : fourJT (j 0) (j 2) (j 1) (j 3) k (v ∘ Equiv.swap (1 : Fin 4) 2) =
        fourJ (j 0) (j 2) (j 1) (j 3) k (v 0) (v 2) (v 1) (v 3) := by
      simp only [fourJT, Function.comp_apply, s0, s1, s2, s3]
    rw [hin, hv, mul_comm]
  · intro k _ hk
    rw [fourJ_eq_zero_of_not_adm (fun h => by simp only [mem_range] at hk; have := h.1.2.1; omega),
      zero_mul]

/-- **The projector in another leg order.** The node projector `Σ_k ι^{(k)} ⊗ ι^{(k)}` (leg order
`(0 2 1 3)`) equals the same sum for the intertwiners in the leg order `ρ`. -/
lemma proj_perm (c : Fin 4 → ℕ) (ρ : Equiv.Perm (Fin 4)) (m m' : Fin 4 → ℤ) :
    ∑ k ∈ range (c 0 + c 2 + 1), fourJ (c 0) (c 2) (c 1) (c 3) k (m 0) (m 2) (m 1) (m 3) *
      fourJ (c 0) (c 2) (c 1) (c 3) k (m' 0) (m' 2) (m' 1) (m' 3) =
    ∑ x ∈ range (c (ρ 0) + c (ρ 1) + 1),
      fourJ (c (ρ 0)) (c (ρ 1)) (c (ρ 2)) (c (ρ 3)) x (m (ρ 0)) (m (ρ 1)) (m (ρ 2)) (m (ρ 3)) *
      fourJ (c (ρ 0)) (c (ρ 1)) (c (ρ 2)) (c (ρ 3)) x (m' (ρ 0)) (m' (ρ 1)) (m' (ρ 2))
        (m' (ρ 3)) := by
  have s0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have s1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have s2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have s3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have h := sum_fourJT_mul_perm (c ∘ Equiv.swap (1 : Fin 4) 2)
    ((Equiv.swap (1 : Fin 4) 2).symm * ρ) (m ∘ Equiv.swap (1 : Fin 4) 2)
    (m' ∘ Equiv.swap (1 : Fin 4) 2)
  simp only [fourJP, fourJT, Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
    s0, s1, s2, s3] at h
  exact h

/-- **Closing a strand of a node projector.** Summing the spin `jA` of leg `lA` with the weight
`jA + 1` and its projection, the node projector becomes the identity on the other three legs
(for admissible projections `u` there, and cutoffs large enough). -/
lemma loop_node (c : Fin 4 → ℕ) (lA : Fin 4) {u : Fin 4 → ℤ}
    (hu : ∀ l, l ≠ lA → u l ∈ pbox (c l)) (u' : Fin 4 → ℤ) (cutA cut : ℕ)
    (hA : ∑ l ∈ univ.erase lA, c l ≤ cutA)
    (hk : ∀ jA ≤ cutA, Function.update c lA jA 0 + Function.update c lA jA 2 ≤ cut) :
    ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k ∈ range (cut + 1), ∑ μ ∈ pbox jA,
      fourJ (Function.update c lA jA 0) (Function.update c lA jA 2) (Function.update c lA jA 1)
          (Function.update c lA jA 3) k (Function.update u lA μ 0) (Function.update u lA μ 2)
          (Function.update u lA μ 1) (Function.update u lA μ 3) *
        fourJ (Function.update c lA jA 0) (Function.update c lA jA 2) (Function.update c lA jA 1)
          (Function.update c lA jA 3) k (Function.update u' lA μ 0) (Function.update u' lA μ 2)
          (Function.update u' lA μ 1) (Function.update u' lA μ 3) =
      ∏ l, if l = lA ∨ u l = u' l then 1 else 0 := by
  obtain ⟨ρ, hρ3, hρi⟩ : ∃ ρ : Equiv.Perm (Fin 4), ρ 3 = lA ∧ ∀ i, i ≠ 3 → ρ i ≠ lA := by
    refine ⟨Equiv.swap lA 3, Equiv.swap_apply_right _ _, fun i hi h => hi ?_⟩
    apply (Equiv.swap lA 3).injective
    rw [h, Equiv.swap_apply_right]
  have hρ0 := hρi 0 (by decide)
  have hρ1 := hρi 1 (by decide)
  have hρ2 := hρi 2 (by decide)
  have hsum : ∑ l ∈ univ.erase lA, c l = c (ρ 0) + c (ρ 1) + c (ρ 2) := by
    have h1 := sum_erase_add univ c (mem_univ lA)
    have h2 : ∑ l, c l = c (ρ 0) + c (ρ 1) + c (ρ 2) + c lA := by
      rw [← Equiv.sum_comp ρ c, Fin.sum_univ_four, hρ3]
    omega
  have hstep : ∀ jA ∈ range (cutA + 1), ∑ k ∈ range (cut + 1), ∑ μ ∈ pbox jA,
      fourJ (Function.update c lA jA 0) (Function.update c lA jA 2) (Function.update c lA jA 1)
          (Function.update c lA jA 3) k (Function.update u lA μ 0) (Function.update u lA μ 2)
          (Function.update u lA μ 1) (Function.update u lA μ 3) *
        fourJ (Function.update c lA jA 0) (Function.update c lA jA 2) (Function.update c lA jA 1)
          (Function.update c lA jA 3) k (Function.update u' lA μ 0) (Function.update u' lA μ 2)
          (Function.update u' lA μ 1) (Function.update u' lA μ 3) =
      ∑ x ∈ range (c (ρ 0) + c (ρ 1) + 1), ∑ μ ∈ Icc (-(jA : ℤ)) jA,
        fourJ (c (ρ 0)) (c (ρ 1)) (c (ρ 2)) jA x (u (ρ 0)) (u (ρ 1)) (u (ρ 2)) μ *
        fourJ (c (ρ 0)) (c (ρ 1)) (c (ρ 2)) jA x (u' (ρ 0)) (u' (ρ 1)) (u' (ρ 2)) μ := by
    intro jA hjA
    have hjA' : jA ≤ cutA := Nat.lt_succ_iff.1 (mem_range.1 hjA)
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    rw [pbox, sum_filter]
    refine sum_congr rfl fun μ _ => ?_
    split_ifs with hp
    · rw [← sum_subset (range_subset_range.2 (by have := hk jA hjA'; omega :
        Function.update c lA jA 0 + Function.update c lA jA 2 + 1 ≤ cut + 1))]
      · rw [proj_perm (Function.update c lA jA) ρ]
        simp only [Function.update_of_ne hρ0, Function.update_of_ne hρ1,
          Function.update_of_ne hρ2, hρ3, Function.update_self]
      · intro k _ hk'
        rw [fourJ_eq_zero_of_not_adm (fun h => by
          simp only [mem_range] at hk'; have := h.1.2.1; omega), zero_mul]
    · symm
      refine sum_eq_zero fun x _ => ?_
      have h0 : fourJ (c (ρ 0)) (c (ρ 1)) (c (ρ 2)) jA x (u (ρ 0)) (u (ρ 1)) (u (ρ 2)) μ = 0 := by
        by_contra h
        have := (admProj_of_fourJ_ne_zero h).2.2.2
        unfold AdmProj at this
        exact hp this.2.2
      rw [h0, zero_mul]
  rw [sum_congr rfl fun (jA : ℕ) hjA => congrArg (((jA : ℝ) + 1) * ·) (hstep jA hjA)]
  rw [← sum_subset (range_subset_range.2 (by omega :
    c (ρ 0) + c (ρ 1) + c (ρ 2) + 1 ≤ cutA + 1))]
  · rw [loop_fourJ _ _ _ (mem_pbox.1 (hu _ hρ0)) (mem_pbox.1 (hu _ hρ1)) (mem_pbox.1 (hu _ hρ2)),
      ← Equiv.prod_comp ρ, Fin.prod_univ_four, hρ3]
    simp only [true_or, ↓reduceIte, mul_one, hρ0, hρ1, hρ2, false_or]
    by_cases h0 : u (ρ 0) = u' (ρ 0) <;> by_cases h1 : u (ρ 1) = u' (ρ 1) <;>
      by_cases h2 : u (ρ 2) = u' (ρ 2) <;> simp [h0, h1, h2]
  · intro jA _ hjA
    rw [sum_eq_zero fun x hx => sum_eq_zero fun μ _ => ?_, mul_zero]
    rw [fourJ_eq_zero_of_not_adm (fun h => by
      simp only [mem_range] at hx hjA; have := h.2.2.1; omega), zero_mul]

/-- The two spins of the first triad of a node, after the spin of leg `lA` is replaced by `jA`. -/
lemma update_triad_le (c : Fin 4 → ℕ) (lA : Fin 4) (jA : ℕ) :
    Function.update c lA jA 0 + Function.update c lA jA 2 ≤ jA + ∑ l ∈ univ.erase lA, c l := by
  have h1 := sum_erase_add univ c (mem_univ lA)
  rw [Fin.sum_univ_four] at h1
  generalize ∑ l ∈ univ.erase lA, c l = s at h1 ⊢
  fin_cases lA <;> simp at h1 ⊢ <;> omega

/-- Summing over the admissible projections is unchanged by a sign flip. -/
lemma sum_pbox_sg (b : Bool) (j : ℕ) (g : ℤ → ℝ) :
    ∑ a ∈ pbox j, g (sg b a) = ∑ μ ∈ pbox j, g μ := by
  refine sum_nbij' (sg b) (sg b) (fun a ha => sg_mem_pbox.2 ha) (fun a ha => sg_mem_pbox.2 ha)
    (fun a _ => ?_) (fun a _ => ?_) (fun a _ => rfl) <;>
  · rw [sg_sg, Bool.xor_self]; rfl

/-! ## Signed networks -/

/-- **A signed network**: edges `E`, nodes `N`, faces `F` (see the module docstring). -/
structure SNet (F E N : Type*) where
  /-- The face (triangle) of an edge. -/
  face : E → F
  /-- Whether the edge carries the sign `(-1)^{(j - x)/2}` of the invariant bilinear form. -/
  kap : E → Bool
  /-- Whether the edge is live (dead edges have projection `0`). -/
  eLive : E → Bool
  /-- The face (tetrahedron) of a node. -/
  tet : N → F
  /-- Whether the node is live (dead nodes contribute `1`). -/
  nLive : N → Bool
  /-- The edge of each leg of a node. -/
  leg : N → Fin 4 → E
  /-- Whether the leg reads the negated projection of its edge. -/
  neg : N → Fin 4 → Bool
  /-- Constraints `(e₁, e₂, b)`: `x e₂ = sg b (x e₁)`. -/
  cons : List (E × E × Bool)
  /-- Faces whose colours give the constant sign `Π (-1)^{col f}`. -/
  cst : List F

namespace SNet

variable {F E N : Type*} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
variable (S : SNet F E N) (col : F → ℕ)

/-- The projections of an edge: the admissible ones if it is live, `0` if it is dead. -/
def box (e : E) : Finset ℤ := if S.eLive e then pbox (col (S.face e)) else {0}

/-- The factor of an edge. -/
noncomputable def eFac (x : E → ℤ) (e : E) : ℝ :=
  if S.eLive e && S.kap e then edgeSign (col (S.face e)) (x e) else 1

/-- The projections read by the legs of a node. -/
def args (x : E → ℤ) (n : N) (l : Fin 4) : ℤ := sg (S.neg n l) (x (S.leg n l))

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
lemma args_def (x : E → ℤ) (n : N) : S.args x n = fun l => sg (S.neg n l) (x (S.leg n l)) := rfl

/-- The factor of a node. -/
noncomputable def nFac (x : E → ℤ) (n : N) : ℝ :=
  if S.nLive n then nodeT col (S.tet n) (fun l => S.face (S.leg n l)) (S.args x n) else 1

/-- The factor of a constraint. -/
noncomputable def cFac (x : E → ℤ) (c : E × E × Bool) : ℝ :=
  if x c.2.1 = sg c.2.2 (x c.1) then 1 else 0

/-- The summand of the evaluation. -/
noncomputable def summand (x : E → ℤ) : ℝ :=
  (∏ e, S.eFac col x e) * (∏ n, S.nFac col x n) * (S.cons.map (cFac x)).prod

/-- **The evaluation of a signed network.** -/
noncomputable def ev : ℝ :=
  fsign S.cst col * ∑ x ∈ Fintype.piFinset (S.box col), S.summand col x

/-! ## Eliminating a constraint -/

/-- Eliminating the constraint `x e₂ = sg b (x e₁)`: the edge `e₂` dies, its legs move to `e₁`
(with the sign `b`), and its flag is merged into the flag of `e₁`. -/
def subst (e₁ e₂ : E) (b : Bool) (rest : List (E × E × Bool)) : SNet F E N where
  face := S.face
  kap e := if e = e₁ then xor (S.kap e₁) (S.kap e₂) else S.kap e
  eLive e := if e = e₂ then false else S.eLive e
  tet := S.tet
  nLive := S.nLive
  leg n l := if S.leg n l = e₂ then e₁ else S.leg n l
  neg n l := if S.leg n l = e₂ then xor (S.neg n l) b else S.neg n l
  cons := rest
  cst := if S.kap e₂ && b then S.face e₂ :: S.cst else S.cst

/-- Eliminating the first constraint. -/
def elim : SNet F E N :=
  match S.cons with
  | [] => S
  | (e₁, e₂, b) :: rest => S.subst e₁ e₂ b rest

omit [Fintype E] [Fintype N] [DecidableEq N] in
lemma elim_eq {e₁ e₂ : E} {b : Bool} {rest : List (E × E × Bool)}
    (h : S.cons = (e₁, e₂, b) :: rest) : S.elim = S.subst e₁ e₂ b rest := by
  unfold elim; rw [h]

variable {S col}

omit [Fintype E] [Fintype N] [DecidableEq N] in
/-- The box of `subst` is the box of `S` with the coordinate `e₂` set to `0`. -/
lemma box_subst (e₁ e₂ : E) (b : Bool) (rest : List (E × E × Bool)) :
    (S.subst e₁ e₂ b rest).box col = Function.update (S.box col) e₂ {0} := by
  funext e
  by_cases he : e = e₂
  · subst he; simp [box, subst]
  · simp [box, subst, he]

omit [DecidableEq N] in
/-- **Eliminating a constraint** `x e₂ = sg b (x e₁)` between two live edges of the same face,
when `e₂` occurs in no other constraint. -/
theorem ev_subst {e₁ e₂ : E} {b : Bool} {rest : List (E × E × Bool)}
    (h : S.cons = (e₁, e₂, b) :: rest) (h12 : e₁ ≠ e₂) (h1 : S.eLive e₁ = true)
    (h2 : S.eLive e₂ = true) (hf : S.face e₁ = S.face e₂)
    (hr : ∀ c ∈ rest, c.1 ≠ e₂ ∧ c.2.1 ≠ e₂) :
    (S.subst e₁ e₂ b rest).ev col = S.ev col := by
  set S' := S.subst e₁ e₂ b rest
  have hx1 : ∀ x ∈ Fintype.piFinset (S'.box col), x e₁ ∈ pbox (col (S.face e₂)) := by
    intro x hx
    have := (Fintype.mem_piFinset.1 hx) e₁
    rw [box_subst, Function.update_of_ne h12] at this
    simpa [box, h1, hf] using this
  -- sum out the coordinate `e₂`
  have hsplit : ∑ x ∈ Fintype.piFinset (S.box col), S.summand col x =
      ∑ x ∈ Fintype.piFinset (S'.box col),
        S.summand col (Function.update x e₂ (sg b (x e₁))) := by
    have hs := sum_piFinset_split (S.box col) e₂
      (fun a x => S.summand col (Function.update x e₂ a)) (fun a x => by simp)
    simp only [Function.update_eq_self] at hs
    rw [hs, ← box_subst e₁ e₂ b rest]
    refine sum_congr rfl fun x hx => ?_
    have hb : S.box col e₂ = pbox (col (S.face e₂)) := by simp [box, h2]
    rw [hb]
    refine sum_eq_single (sg b (x e₁)) (fun a _ ha => ?_)
      (fun ha => absurd (sg_mem_pbox.2 (hx1 x hx)) ha)
    rw [summand, h, List.map_cons, List.prod_cons]
    simp [cFac, Function.update_of_ne h12, ha]
  -- compare the summands
  have hpt : ∀ x ∈ Fintype.piFinset (S'.box col), fsign S'.cst col * S'.summand col x =
      fsign S.cst col * S.summand col (Function.update x e₂ (sg b (x e₁))) := by
    intro x hx
    set y := Function.update x e₂ (sg b (x e₁)) with hydef
    have hy : ∀ e, e ≠ e₂ → y e = x e := fun e he => Function.update_of_ne he _ _
    -- constraints
    have hc : (S'.cons.map (cFac x)).prod = (S.cons.map (cFac y)).prod := by
      rw [h, List.map_cons, List.prod_cons]
      have h0 : cFac y (e₁, e₂, b) = 1 := by
        simp [cFac, y, Function.update_of_ne h12]
      rw [h0, one_mul]
      show (rest.map (cFac x)).prod = (rest.map (cFac y)).prod
      congr 1
      refine List.map_congr_left fun c hc => ?_
      obtain ⟨hc1, hc2⟩ := hr c hc
      simp [cFac, hy _ hc1, hy _ hc2]
    -- nodes
    have hn : ∀ n, S'.nFac col x n = S.nFac col y n := by
      intro n
      have hface : (fun l => S'.face (S'.leg n l)) = fun l => S.face (S.leg n l) := by
        funext l
        show S.face (if S.leg n l = e₂ then e₁ else S.leg n l) = _
        by_cases hle : S.leg n l = e₂ <;> simp [hle, hf]
      have hargs : S'.args x n = S.args y n := by
        funext l
        show sg (if S.leg n l = e₂ then xor (S.neg n l) b else S.neg n l)
            (x (if S.leg n l = e₂ then e₁ else S.leg n l)) = sg (S.neg n l) (y (S.leg n l))
        by_cases hle : S.leg n l = e₂
        · simp [hle, y, sg_sg]
        · simp [hle, hy _ hle]
      unfold nFac
      rw [hface, hargs]
      rfl
    -- edges
    have he : fsign S'.cst col * ∏ e, S'.eFac col x e =
        fsign S.cst col * ∏ e, S.eFac col y e := by
      have hm1 : e₁ ∈ (univ : Finset E) := mem_univ _
      have hm2 : e₂ ∈ (univ : Finset E).erase e₁ := mem_erase.2 ⟨h12.symm, mem_univ _⟩
      rw [← mul_prod_erase _ _ hm1, ← mul_prod_erase _ _ hm2,
        ← mul_prod_erase _ (S.eFac col y) hm1, ← mul_prod_erase _ (S.eFac col y) hm2]
      have hrest : ∏ e ∈ ((univ : Finset E).erase e₁).erase e₂, S'.eFac col x e =
          ∏ e ∈ ((univ : Finset E).erase e₁).erase e₂, S.eFac col y e := by
        refine prod_congr rfl fun e he => ?_
        obtain ⟨he2, he1⟩ := mem_erase.1 he
        have he1' := (mem_erase.1 he1).1
        simp [eFac, S', subst, he1', he2, hy _ he2]
      rw [hrest]
      have e1' : S'.eFac col x e₁ =
          if xor (S.kap e₁) (S.kap e₂) then edgeSign (col (S.face e₂)) (x e₁) else 1 := by
        simp [eFac, S', subst, h12, h1, hf]
      have e2' : S'.eFac col x e₂ = 1 := by simp [eFac, S', subst]
      have e1 : S.eFac col y e₁ = if S.kap e₁ then edgeSign (col (S.face e₂)) (x e₁) else 1 := by
        simp [eFac, y, Function.update_of_ne h12, h1, hf]
      have e2 : S.eFac col y e₂ = if S.kap e₂ then
          (if b then (-1) ^ col (S.face e₂) else 1) * edgeSign (col (S.face e₂)) (x e₁)
          else 1 := by
        simp only [eFac, h2, y, Function.update_self, Bool.true_and]
        rw [edgeSign_sg (hx1 x hx)]
      have cs : fsign S'.cst col =
          (if S.kap e₂ && b then (-1) ^ col (S.face e₂) else 1) * fsign S.cst col := by
        simp only [S', subst]
        split_ifs <;> simp
      rw [e1', e2', e1, e2, cs]
      have hs : edgeSign (col (S.face e₂)) (x e₁) = 1 ∨ edgeSign (col (S.face e₂)) (x e₁) = -1 :=
        mul_self_eq_one_iff.1 (edgeSign_mul_self _ _)
      have hp : ((-1 : ℝ) ^ col (S.face e₂)) = 1 ∨ ((-1 : ℝ) ^ col (S.face e₂)) = -1 :=
        neg_one_pow_eq_or ℝ _
      generalize edgeSign (col (S.face e₂)) (x e₁) = s at hs ⊢
      generalize ((-1 : ℝ) ^ col (S.face e₂)) = p at hp ⊢
      cases S.kap e₁ <;> cases S.kap e₂ <;> cases b <;> rcases hs with rfl | rfl <;>
        rcases hp with rfl | rfl <;> simp
    unfold summand
    rw [hc]
    calc fsign S'.cst col * ((∏ e, S'.eFac col x e) * (∏ n, S'.nFac col x n) *
          (S.cons.map (cFac y)).prod)
        = (fsign S'.cst col * ∏ e, S'.eFac col x e) * (∏ n, S'.nFac col x n) *
          (S.cons.map (cFac y)).prod := by ring
      _ = (fsign S.cst col * ∏ e, S.eFac col y e) * (∏ n, S.nFac col y n) *
          (S.cons.map (cFac y)).prod := by rw [he, prod_congr rfl fun n _ => hn n]
      _ = _ := by ring
  unfold ev
  rw [hsplit, mul_sum, mul_sum]
  exact sum_congr rfl hpt

/-! ## Flips and parity substitutions -/

variable (S) in
/-- The list containing `f` if `b` holds. -/
def optL (b : Bool) (f : F) : List F := if b then [f] else []

variable (S) in
/-- The faces of the legs `l` of `n₀` with `p l`. -/
def legL (n₀ : N) (p : Fin 4 → Bool) : List F :=
  optL (p 0) (S.face (S.leg n₀ 0)) ++ optL (p 1) (S.face (S.leg n₀ 1)) ++
    optL (p 2) (S.face (S.leg n₀ 2)) ++ optL (p 3) (S.face (S.leg n₀ 3))

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
lemma fsign_legL (n₀ : N) (p : Fin 4 → Bool) :
    fsign (S.legL n₀ p) col = ∏ l, if p l then (-1) ^ col (S.face (S.leg n₀ l)) else 1 := by
  have h : ∀ b f, fsign (optL b f) col = if b then (-1) ^ col f else 1 := by
    intro b f; cases b <;> simp [optL]
  simp only [legL, fsign_append, Fin.prod_univ_four, h]

variable (S) in
/-- Flipping a node: its legs change sign, the flags of their edges toggle, and the faces of the
legs that were read without sign enter the constant. -/
def flipNode (n₀ : N) : SNet F E N where
  face := S.face
  kap e := xor (S.kap e) (decide (∃ l, S.leg n₀ l = e))
  eLive := S.eLive
  tet := S.tet
  nLive := S.nLive
  leg := S.leg
  neg n l := if n = n₀ then !S.neg n l else S.neg n l
  cons := S.cons
  cst := S.cst ++ S.legL n₀ fun l => !S.neg n₀ l

/-- **Flipping a live node** whose four legs lie on distinct live edges keeps the evaluation. -/
theorem ev_flipNode {n₀ : N} (hn : S.nLive n₀ = true) (hl : ∀ l, S.eLive (S.leg n₀ l) = true)
    (hinj : Function.Injective (S.leg n₀)) : (S.flipNode n₀).ev col = S.ev col := by
  set S' := S.flipNode n₀
  have hbox : S'.box col = S.box col := rfl
  unfold ev
  rw [hbox, mul_sum, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  have hxe : ∀ l, x (S.leg n₀ l) ∈ pbox (col (S.face (S.leg n₀ l))) := by
    intro l
    have := (Fintype.mem_piFinset.1 hx) (S.leg n₀ l)
    simpa [box, hl l] using this
  -- edges
  have hE : ∀ e, S.eFac col x e = S'.eFac col x e *
      (if e ∈ univ.image (S.leg n₀) then edgeSign (col (S.face e)) (x e) else 1) := by
    intro e
    by_cases he : e ∈ univ.image (S.leg n₀)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 he
      have hk : S'.kap (S.leg n₀ l) = !S.kap (S.leg n₀ l) := by
        simp only [S', flipNode]
        have : decide (∃ l', S.leg n₀ l' = S.leg n₀ l) = true := decide_eq_true ⟨l, rfl⟩
        rw [this, Bool.xor_true]
      have hl' : S'.eLive (S.leg n₀ l) = true := hl l
      simp only [eFac, he, ↓reduceIte, hk, hl l, hl', Bool.true_and]
      change _ = (if (!S.kap (S.leg n₀ l)) = true then
        edgeSign (col (S.face (S.leg n₀ l))) (x (S.leg n₀ l)) else 1) * _
      cases S.kap (S.leg n₀ l) <;> simp [edgeSign_mul_self]
    · have hne : ¬∃ l, S.leg n₀ l = e := fun ⟨l, hl'⟩ => he (mem_image.2 ⟨l, mem_univ _, hl'⟩)
      have hk : S'.kap e = S.kap e := by
        simp only [S', flipNode, hne, decide_false, Bool.xor_false]
      simp only [eFac, he, ↓reduceIte, mul_one, hk]
      rfl
  have hEprod : ∏ e, S.eFac col x e = (∏ e, S'.eFac col x e) *
      ∏ l, edgeSign (col (S.face (S.leg n₀ l))) (x (S.leg n₀ l)) := by
    rw [prod_congr rfl fun e _ => hE e, prod_mul_distrib, prod_ite_mem, univ_inter,
      prod_image fun a _ b _ h => hinj h]
  -- nodes
  have hN : ∀ n ∈ univ.erase n₀, S'.nFac col x n = S.nFac col x n := by
    intro n hn'
    have hne := (mem_erase.1 hn').1
    simp [nFac, S', flipNode, args_def, hne]
  have hN0 : S'.nFac col x n₀ = nodeT col (S.tet n₀) (fun l => S.face (S.leg n₀ l))
      (fun l => sg (!S.neg n₀ l) (x (S.leg n₀ l))) := by
    simp [nFac, S', flipNode, args_def, hn]
  have hS0 : S.nFac col x n₀ = nodeT col (S.tet n₀) (fun l => S.face (S.leg n₀ l))
      (fun l => sg (S.neg n₀ l) (x (S.leg n₀ l))) := by
    simp [nFac, args_def, hn]
  have key := nodeT_flip col (S.tet n₀) (fun l => S.face (S.leg n₀ l)) (S.neg n₀)
    (fun l => x (S.leg n₀ l)) hxe
  have hcst : fsign S'.cst col = fsign S.cst col *
      ∏ l, (if S.neg n₀ l then 1 else (-1) ^ col (S.face (S.leg n₀ l))) := by
    simp only [S', flipNode]
    rw [fsign_append, fsign_legL]
    congr 1
    refine prod_congr rfl fun l _ => ?_
    cases S.neg n₀ l <;> simp
  have hc : S'.cons = S.cons := rfl
  unfold summand
  rw [hEprod, ← mul_prod_erase _ (S.nFac col x) (mem_univ n₀),
    ← mul_prod_erase _ (S'.nFac col x) (mem_univ n₀),
    prod_congr rfl hN, hN0, hS0, hcst, hc]
  linear_combination (-(fsign S.cst col * (∏ e, S'.eFac col x e) *
    (∏ n ∈ univ.erase n₀, S.nFac col x n) * (S.cons.map (cFac x)).prod)) * key

variable (S) in
/-- Flipping a variable: the projection of the edge `e₀` changes sign. -/
def flipVar (e₀ : E) : SNet F E N where
  face := S.face
  kap := S.kap
  eLive := S.eLive
  tet := S.tet
  nLive := S.nLive
  leg := S.leg
  neg n l := if S.leg n l = e₀ then !S.neg n l else S.neg n l
  cons := S.cons.map fun c =>
    (c.1, c.2.1, xor c.2.2 (xor (decide (c.1 = e₀)) (decide (c.2.1 = e₀))))
  cst := if S.eLive e₀ && S.kap e₀ then S.face e₀ :: S.cst else S.cst

omit [DecidableEq N] in
/-- **Flipping a variable** keeps the evaluation. -/
theorem ev_flipVar (e₀ : E) : (S.flipVar e₀).ev col = S.ev col := by
  set S' := S.flipVar e₀
  have hbox : S'.box col = S.box col := rfl
  set φ : (E → ℤ) → (E → ℤ) := fun x => Function.update x e₀ (-x e₀) with hφ
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x; funext e; by_cases he : e = e₀
    · subst he; simp [φ]
    · simp [φ, Function.update_of_ne he]
  have hmem : ∀ x ∈ Fintype.piFinset (S.box col), φ x ∈ Fintype.piFinset (S.box col) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro e
    by_cases he : e = e₀
    · subst he
      have := hx e
      simp only [φ, Function.update_self]
      unfold box at this ⊢
      split_ifs at this ⊢
      · exact sg_mem_pbox (b := true) |>.2 this
      · simp_all
    · simpa [φ, Function.update_of_ne he] using hx e
  unfold ev
  rw [hbox, mul_sum, mul_sum]
  refine sum_nbij' φ φ hmem hmem (fun x _ => hφφ x) (fun x _ => hφφ x) fun x hx => ?_
  have hy : ∀ e, e ≠ e₀ → φ x e = x e := fun e he => Function.update_of_ne he _ _
  have hy0 : φ x e₀ = -x e₀ := Function.update_self _ _ _
  -- constraints
  have hc : (S'.cons.map (cFac x)).prod = (S.cons.map (cFac (φ x))).prod := by
    simp only [S', flipVar, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    obtain ⟨c1, c2, b⟩ := c
    simp only [Function.comp, cFac]
    by_cases h1 : c1 = e₀ <;> by_cases h2 : c2 = e₀
    · subst h1; subst h2
      cases b <;> simp [hy0, sg]
      split_ifs <;> first | rfl | (exfalso; omega)
    · subst h1; rw [hy0, hy _ h2]
      cases b <;> simp [h2, sg]
    · subst h2; rw [hy0, hy _ h1]
      cases b <;> simp [h1, sg]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [hy _ h1, hy _ h2]; simp [h1, h2]
  -- nodes
  have hn : ∀ n, S'.nFac col x n = S.nFac col (φ x) n := by
    intro n
    unfold nFac
    have hargs : S'.args x n = S.args (φ x) n := by
      funext l
      simp only [args, S', flipVar]
      by_cases hl : S.leg n l = e₀
      · simp only [hl, ↓reduceIte, hy0, sg_not]
        cases S.neg n l <;> simp [sg]
      · simp only [hl, ↓reduceIte, hy _ hl]
    rw [hargs]; rfl
  -- edges
  have he : fsign S'.cst col * ∏ e, S'.eFac col x e = fsign S.cst col * ∏ e, S.eFac col (φ x) e := by
    rw [← mul_prod_erase _ _ (mem_univ e₀), ← mul_prod_erase _ (S.eFac col (φ x)) (mem_univ e₀)]
    have hrest : ∏ e ∈ univ.erase e₀, S'.eFac col x e = ∏ e ∈ univ.erase e₀, S.eFac col (φ x) e := by
      refine prod_congr rfl fun e he => ?_
      simp [eFac, S', flipVar, hy _ (mem_erase.1 he).1]
    rw [hrest]
    simp only [S', flipVar, eFac, hy0]
    by_cases hlk : (S.eLive e₀ && S.kap e₀) = true
    · have hx0 : x e₀ ∈ pbox (col (S.face e₀)) := by
        have := (Fintype.mem_piFinset.1 hx) e₀
        simp only [Bool.and_eq_true] at hlk
        simpa [box, hlk.1] using this
      simp only [hlk, ↓reduceIte]
      rw [fsign_cons,
        show -x e₀ = sg true (x e₀) from rfl, edgeSign_sg hx0]
      simp only [↓reduceIte]
      ring
    · simp [hlk]
  unfold summand
  rw [hc]
  calc fsign S'.cst col * ((∏ e, S'.eFac col x e) * (∏ n, S'.nFac col x n) *
        (S.cons.map (cFac (φ x))).prod)
      = (fsign S'.cst col * ∏ e, S'.eFac col x e) * (∏ n, S'.nFac col x n) *
        (S.cons.map (cFac (φ x))).prod := by ring
    _ = (fsign S.cst col * ∏ e, S.eFac col (φ x) e) * (∏ n, S.nFac col (φ x) n) *
        (S.cons.map (cFac (φ x))).prod := by rw [he, prod_congr rfl fun n _ => hn n]
    _ = _ := by ring

variable (S) in
/-- Adding the four faces of the legs of a node to the constant. -/
def addParity (n₀ : N) : SNet F E N := { S with cst := S.cst ++ S.legL n₀ fun _ => true }

/-- **Parity substitution.** The spins of the legs of a nonzero node tensor have even sum, so
adding them to the constant keeps the evaluation. -/
theorem ev_addParity {n₀ : N} (hn : S.nLive n₀ = true) : (S.addParity n₀).ev col = S.ev col := by
  have hs : ∀ x, (S.addParity n₀).summand col x = S.summand col x := fun _ => rfl
  unfold ev
  have hb : (S.addParity n₀).box col = S.box col := rfl
  rw [hb, sum_congr rfl fun x _ => hs x]
  show fsign (S.cst ++ S.legL n₀ fun _ => true) col * _ = _
  rw [fsign_append, fsign_legL]
  simp only [↓reduceIte]
  by_cases hev : (col (S.face (S.leg n₀ 0)) + col (S.face (S.leg n₀ 2)) +
    col (S.face (S.leg n₀ 1)) + col (S.face (S.leg n₀ 3))) % 2 = 0
  · rw [prod_pow_eq_pow_sum, Fin.sum_univ_four, Even.neg_one_pow (Nat.even_iff.2 (by omega)),
      mul_one]
  · have h0 : ∀ x, S.summand col x = 0 := by
      intro x
      unfold summand
      rw [← mul_prod_erase _ _ (mem_univ n₀)]
      have : S.nFac col x n₀ = 0 := by
        simp only [nFac, hn, ↓reduceIte, nodeT]
        by_contra h
        exact hev (even_of_fourJ_ne_zero h)
      rw [this]; ring
    simp [h0]

/-! ## Gluing two nodes through a block -/

/-- The constant sign only sees the colours of its faces. -/
lemma fsign_congr {l : List F} {c c' : F → ℕ} (h : ∀ f ∈ l, c f = c' f) : fsign l c = fsign l c' := by
  unfold fsign; congr 1; exact List.map_congr_left fun f hf => by rw [h f hf]

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
lemma eFac_congr {c c' : F → ℕ} {x x' : E → ℤ} {e : E}
    (h : S.eLive e = true → c (S.face e) = c' (S.face e) ∧ x e = x' e) :
    S.eFac c x e = S.eFac c' x' e := by
  unfold eFac
  by_cases he : S.eLive e = true
  · obtain ⟨h1, h2⟩ := h he; rw [h1, h2]
  · simp [he]

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
lemma nFac_congr {c c' : F → ℕ} {x x' : E → ℤ} {n : N}
    (h : S.nLive n = true → c (S.tet n) = c' (S.tet n) ∧
      ∀ l, c (S.face (S.leg n l)) = c' (S.face (S.leg n l)) ∧ x (S.leg n l) = x' (S.leg n l)) :
    S.nFac c x n = S.nFac c' x' n := by
  unfold nFac
  by_cases hn : S.nLive n = true
  · obtain ⟨ht, hl⟩ := h hn
    simp only [hn, ↓reduceIte, nodeT, args_def, ht, (hl _).1, (hl _).2]
  · simp [hn]

variable (S) in
/-- **Gluing** the nodes `n₁` and `n₂` (of the same tetrahedron): both die, and each leg of `n₂`
is identified with the matching leg of `n₁` by a constraint (the legs read the same projection). -/
def glue (n₁ n₂ : N) : SNet F E N := { S with
  nLive := fun n => if n = n₁ ∨ n = n₂ then false else S.nLive n
  cons := List.ofFn (fun l => (S.leg n₁ l, S.leg n₂ l, xor (S.neg n₁ l) (S.neg n₂ l))) ++ S.cons }

variable (S col) in
/-- The weight of a block (edges `bE`, nodes `bN`) without its node `n₁`. -/
noncomputable def qIn (bE : E → Bool) (bN : N → Bool) (n₁ : N) (z : E → ℤ) : ℝ :=
  (∏ e, if bE e then S.eFac col z e else 1) * ∏ n, if bN n ∧ n ≠ n₁ then S.nFac col z n else 1

variable (S col) in
/-- The weight outside a block (edges not in `bE`, nodes not in `bN`), without the node `n₂`. -/
noncomputable def qOut (bE : E → Bool) (bN : N → Bool) (n₂ : N) (y : E → ℤ) : ℝ :=
  (∏ e, if bE e then 1 else S.eFac col y e) *
    (∏ n, if bN n = false ∧ n ≠ n₂ then S.nFac col y n else 1) * (S.cons.map (cFac y)).prod

variable (S col) in
/-- **The tensor a block leaves at its node `n₁`**: the block weight summed over the projections
of the block edges whose legs at `n₁` read `m`. -/
noncomputable def rem (bE : E → Bool) (bN : N → Bool) (n₁ : N) (m : Fin 4 → ℤ) : ℝ :=
  ∑ z ∈ Fintype.piFinset (fun e => if bE e then S.box col e else {0}),
    S.qIn col bE bN n₁ z * ∏ l, if S.args z n₁ l = m l then 1 else 0

lemma sg_xor_iff (a b : Bool) (u w : ℤ) : w = sg (xor a b) u ↔ sg a u = sg b w := by
  cases a <;> cases b <;> simp only [sg, Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **Gluing through a block.** Let `n₁, n₂` be live nodes of the tetrahedron `t`, whose colour
enters nowhere else, with legs on the same faces. Let `n₁` lie in a block (edges `bE`, nodes `bN`)
that meets the rest only at `n₁` and holds no constraint, and suppose the block leaves an invariant
tensor at `n₁`. Then summing the colour of `t` up to the cutoff glues `n₁` to `n₂`. -/
theorem ev_glue [DecidableEq F] {n₁ n₂ : N} {t : F} (bE : E → Bool) (bN : N → Bool) (cut : ℕ)
    (hb1 : bN n₁ = true) (hb2 : bN n₂ = false)
    (hblk : ∀ n, S.nLive n = true → ∀ l, bE (S.leg n l) = bN n)
    (hcons : ∀ c ∈ S.cons, bE c.1 = false ∧ bE c.2.1 = false)
    (hlegs : ∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true)
    (hn1 : S.nLive n₁ = true) (hn2 : S.nLive n₂ = true) (ht1 : S.tet n₁ = t) (ht2 : S.tet n₂ = t)
    (hf : ∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l))
    (hte : ∀ e, S.eLive e = true → S.face e ≠ t)
    (htn : ∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t)
    (htc : t ∉ S.cst)
    (hcut : col (S.face (S.leg n₁ 0)) + col (S.face (S.leg n₁ 2)) ≤ cut)
    (hR : IsInv (fun l => col (S.face (S.leg n₁ l))) (fun _ => false) (S.rem col bE bN n₁)) :
    ∑ k ∈ range (cut + 1), S.ev (Function.update col t k) = (S.glue n₁ n₂).ev col := by
  have h12 : n₁ ≠ n₂ := fun h => by rw [h, hb2] at hb1; exact Bool.false_ne_true hb1
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, c = fun l => col (S.face (S.leg n₁ l)) := ⟨_, rfl⟩
  have hcl : ∀ l, col (S.face (S.leg n₁ l)) = c l := fun l => by rw [hc]
  rw [← hc] at hR
  rw [hcl, hcl] at hcut
  -- the colour of `t` enters only at `n₁` and `n₂`
  have hbox : ∀ k, S.box (Function.update col t k) = S.box col := by
    intro k; funext e; unfold box
    by_cases he : S.eLive e = true
    · simp only [he, ↓reduceIte, Function.update_of_ne (hte e he)]
    · simp [he]
  have hfs : ∀ k, fsign S.cst (Function.update col t k) = fsign S.cst col := fun k =>
    fsign_congr fun f hf => Function.update_of_ne (fun h : f = t => htc (h ▸ hf)) _ _
  have hEk : ∀ k (x : E → ℤ) e, S.eFac (Function.update col t k) x e = S.eFac col x e :=
    fun k x e => eFac_congr fun he => ⟨Function.update_of_ne (hte e he) _ _, rfl⟩
  have hNk : ∀ k (x : E → ℤ) n, n ≠ n₁ → n ≠ n₂ →
      S.nFac (Function.update col t k) x n = S.nFac col x n := fun k x n h1 h2 =>
    nFac_congr fun hn => ⟨Function.update_of_ne (htn n hn h1 h2) _ _,
      fun l => ⟨Function.update_of_ne (hte _ (hlegs n hn l)) _ _, rfl⟩⟩
  have hι : ∀ k (x : E → ℤ) n, n = n₁ ∨ n = n₂ → S.nFac (Function.update col t k) x n =
      fourJ (c 0) (c 2) (c 1) (c 3) k (S.args x n 0) (S.args x n 2) (S.args x n 1)
        (S.args x n 3) := by
    intro k x n hn
    have hu : ∀ l, Function.update col t k (S.face (S.leg n₁ l)) = c l := fun l => by
      rw [Function.update_of_ne (hte _ (hlegs _ hn1 l)), hcl]
    rcases hn with rfl | rfl
    · simp only [nFac, hn1, ↓reduceIte, nodeT, ht1, Function.update_self, hu]
    · simp only [nFac, hn2, ↓reduceIte, nodeT, ht2, Function.update_self, hf, hu]
  -- the merged point
  have hmz : ∀ (c' : F → ℕ) (z y : E → ℤ) n, bN n = true →
      S.nFac c' (fun e => if bE e then z e else y e) n = S.nFac c' z n := fun c' z y n hb =>
    nFac_congr fun hn => ⟨rfl, fun l => ⟨rfl, by simp [hblk n hn l, hb]⟩⟩
  have hmy : ∀ (c' : F → ℕ) (z y : E → ℤ) n, bN n = false →
      S.nFac c' (fun e => if bE e then z e else y e) n = S.nFac c' y n := fun c' z y n hb =>
    nFac_congr fun hn => ⟨rfl, fun l => ⟨rfl, by simp [hblk n hn l, hb]⟩⟩
  have hE : ∀ (z y : E → ℤ) e, S.eFac col (fun e => if bE e then z e else y e) e =
      (if bE e then S.eFac col z e else 1) * (if bE e then 1 else S.eFac col y e) := by
    intro z y e
    by_cases hb : bE e = true
    · simp only [hb, ↓reduceIte, mul_one]
      exact eFac_congr fun _ => ⟨rfl, by simp [hb]⟩
    · simp only [hb, ↓reduceIte, one_mul, Bool.false_eq_true]
      exact eFac_congr fun _ => ⟨rfl, by simp [hb]⟩
  have hC : ∀ (z y : E → ℤ), (S.cons.map (cFac fun e => if bE e then z e else y e)).prod =
      (S.cons.map (cFac y)).prod := by
    intro z y
    congr 1
    refine List.map_congr_left fun c hc => ?_
    simp [cFac, (hcons c hc).1, (hcons c hc).2]
  have key1 : ∀ k (z y : E → ℤ), S.summand (Function.update col t k)
      (fun e => if bE e then z e else y e) =
      S.qIn col bE bN n₁ z * S.qOut col bE bN n₂ y *
        (S.nFac (Function.update col t k) z n₁ * S.nFac (Function.update col t k) y n₂) := by
    intro k z y
    have hN : ∀ n, S.nFac (Function.update col t k) (fun e => if bE e then z e else y e) n =
        (if bN n ∧ n ≠ n₁ then S.nFac col z n else 1) *
          (if bN n = false ∧ n ≠ n₂ then S.nFac col y n else 1) *
          ((if n = n₁ then S.nFac (Function.update col t k) z n₁ else 1) *
            (if n = n₂ then S.nFac (Function.update col t k) y n₂ else 1)) := by
      intro n
      by_cases h1 : n = n₁
      · subst h1
        rw [hmz _ _ _ _ hb1]; simp [h12, hb1]
      by_cases h2 : n = n₂
      · subst h2
        rw [hmy _ _ _ _ hb2]; simp [h1, hb2]
      rw [hNk k _ n h1 h2]
      cases hbn : bN n
      · rw [hmy _ _ _ _ hbn]; simp [h1, h2]
      · rw [hmz _ _ _ _ hbn]; simp [h1, h2]
    unfold summand qIn qOut
    simp only [hEk, hE, hN, prod_mul_distrib, prod_ite_eq', mem_univ, ↓reduceIte, hC]
    ring
  -- the glued side
  have hgN : ∀ (z y : E → ℤ) n, (S.glue n₁ n₂).nFac col (fun e => if bE e then z e else y e) n =
      (if bN n ∧ n ≠ n₁ then S.nFac col z n else 1) *
        (if bN n = false ∧ n ≠ n₂ then S.nFac col y n else 1) := by
    intro z y n
    by_cases h1 : n = n₁
    · subst h1; simp [nFac, glue, hb1]
    by_cases h2 : n = n₂
    · subst h2; simp [nFac, glue, hb2]
    have : (S.glue n₁ n₂).nFac col (fun e => if bE e then z e else y e) n =
        S.nFac col (fun e => if bE e then z e else y e) n := by
      unfold nFac
      simp only [glue, h1, h2, or_self, ↓reduceIte]
      rfl
    rw [this]
    cases hbn : bN n
    · rw [hmy _ _ _ _ hbn]; simp [h1, h2]
    · rw [hmz _ _ _ _ hbn]; simp [h1, h2]
  have hgC : ∀ (z y : E → ℤ),
      ((S.glue n₁ n₂).cons.map (cFac fun e => if bE e then z e else y e)).prod =
        (∏ l, if S.args z n₁ l = S.args y n₂ l then 1 else 0) * (S.cons.map (cFac y)).prod := by
    intro z y
    simp only [glue, List.map_append, List.prod_append, List.map_ofFn, List.prod_ofFn]
    rw [hC]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have h1l : bE (S.leg n₁ l) = true := by rw [hblk n₁ hn1 l, hb1]
    have h2l : bE (S.leg n₂ l) = false := by rw [hblk n₂ hn2 l, hb2]
    simp only [Function.comp_apply, cFac, h1l, h2l, ↓reduceIte, Bool.false_eq_true, args,
      sg_xor_iff]
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have key2 : ∀ (z y : E → ℤ), (S.glue n₁ n₂).summand col (fun e => if bE e then z e else y e) =
      S.qIn col bE bN n₁ z * S.qOut col bE bN n₂ y *
        ∏ l, if S.args z n₁ l = S.args y n₂ l then 1 else 0 := by
    intro z y
    have hgE : ∀ x e, (S.glue n₁ n₂).eFac col x e = S.eFac col x e := fun _ _ => rfl
    unfold summand qIn qOut
    simp only [hgE, hE, hgN, prod_mul_distrib, hgC]
    ring
  -- the block tensor
  have hmem : ∀ z ∈ Fintype.piFinset (fun e => if bE e then S.box col e else {0}),
      S.args z n₁ ∈ Fintype.piFinset (fun l => Icc (-(c l : ℤ)) (c l)) := by
    intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    intro l
    have h1l : bE (S.leg n₁ l) = true := by rw [hblk n₁ hn1 l, hb1]
    have := hz (S.leg n₁ l)
    simp only [h1l, ↓reduceIte, box, hlegs n₁ hn1 l] at this
    have h' : S.args z n₁ l ∈ pbox (col (S.face (S.leg n₁ l))) := by
      rw [args, sg_mem_pbox]; exact this
    rw [mem_pbox, hcl] at h'
    exact mem_Icc.2 ⟨h'.1, h'.2.1⟩
  have fib : ∀ k, ∑ z ∈ Fintype.piFinset (fun e => if bE e then S.box col e else {0}),
      S.qIn col bE bN n₁ z * fourJ (c 0) (c 2) (c 1) (c 3) k (S.args z n₁ 0) (S.args z n₁ 2)
        (S.args z n₁ 1) (S.args z n₁ 3) =
      ∑ m ∈ Fintype.piFinset (fun l => Icc (-(c l : ℤ)) (c l)),
        fourJ (c 0) (c 2) (c 1) (c 3) k (m 0) (m 2) (m 1) (m 3) * S.rem col bE bN n₁ m := by
    intro k
    simp only [rem, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun z hz => ?_
    have hp : ∀ m : Fin 4 → ℤ, (∏ l, if S.args z n₁ l = m l then (1 : ℝ) else 0) =
        if S.args z n₁ = m then 1 else 0 := by
      intro m
      rw [prod_boole]
      simp only [mem_univ, true_implies, funext_iff]
    simp only [hp, mul_ite, mul_one, mul_zero, sum_ite_eq, hmem z hz, ↓reduceIte]
    ring
  -- assembling
  have hι1 : ∀ k (x : E → ℤ), S.nFac (Function.update col t k) x n₁ =
      fourJ (c 0) (c 2) (c 1) (c 3) k (S.args x n₁ 0) (S.args x n₁ 2) (S.args x n₁ 1)
        (S.args x n₁ 3) := fun k x => hι k x n₁ (Or.inl rfl)
  have hι2 : ∀ k (x : E → ℤ), S.nFac (Function.update col t k) x n₂ =
      fourJ (c 0) (c 2) (c 1) (c 3) k (S.args x n₂ 0) (S.args x n₂ 2) (S.args x n₂ 1)
        (S.args x n₂ 3) := fun k x => hι k x n₂ (Or.inr rfl)
  have hL : ∀ k, S.ev (Function.update col t k) = fsign S.cst col *
      ∑ y ∈ Fintype.piFinset (fun e => if bE e then {0} else S.box col e),
        ∑ z ∈ Fintype.piFinset (fun e => if bE e then S.box col e else {0}),
          S.qIn col bE bN n₁ z * S.qOut col bE bN n₂ y *
            (fourJ (c 0) (c 2) (c 1) (c 3) k (S.args z n₁ 0) (S.args z n₁ 2) (S.args z n₁ 1)
              (S.args z n₁ 3) *
             fourJ (c 0) (c 2) (c 1) (c 3) k (S.args y n₂ 0) (S.args y n₂ 2) (S.args y n₂ 1)
              (S.args y n₂ 3)) := by
    intro k
    rw [ev, hfs, hbox, sum_pi_split (S.box col) (fun e => bE e = true)]
    simp only [key1, hι1, hι2]
  have hRgl : (S.glue n₁ n₂).ev col = fsign S.cst col *
      ∑ y ∈ Fintype.piFinset (fun e => if bE e then {0} else S.box col e),
        S.qOut col bE bN n₂ y * S.rem col bE bN n₁ (S.args y n₂) := by
    have hb : (S.glue n₁ n₂).box col = S.box col := rfl
    have hcs : (S.glue n₁ n₂).cst = S.cst := rfl
    rw [ev, hb, hcs, sum_pi_split (S.box col) (fun e => bE e = true)]
    simp only [key2]
    refine congrArg (fsign S.cst col * ·) (sum_congr rfl fun y _ => ?_)
    simp only [rem, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    ring
  rw [hRgl, sum_congr rfl fun k _ => hL k, ← mul_sum]
  refine congrArg (fsign S.cst col * ·) ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← absorb hR cut hcut (S.args y n₂), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← fib k, mul_sum, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  ring

/-! ## Closing a strand -/

variable (S) in
/-- **Closing a strand** between the nodes `n₁, n₂` along leg `lA`: as in `glue n₁ n₂`, and the
edge of leg `lA` of `n₁` dies while its face leaves the constant sign. -/
def loop [DecidableEq F] (n₁ n₂ : N) (lA : Fin 4) : SNet F E N := { S.glue n₁ n₂ with
  eLive := Function.update S.eLive (S.leg n₁ lA) false
  cst := S.cst.filter (· ≠ S.face (S.leg n₁ lA)) }

/-- **Closing a strand.** Let the live nodes `n₁, n₂` of the tetrahedron `t` share the edge `eA`
(face `fA`, no edge sign) on leg `lA`, read it with the same sign, and have their other legs on
the same faces. If the colours of `t` and `fA` enter nowhere else and `fA` occurs an even number
of times in the constant sign, then summing the colour `jA` of `fA` with the weight `jA + 1` and
the colour of `t` (both up to large enough cutoffs) closes the strand. -/
theorem ev_loop [DecidableEq F] {n₁ n₂ : N} {t fA : F} {eA : E} (lA : Fin 4) (cutA cut : ℕ)
    (h12 : n₁ ≠ n₂) (hlegs : ∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true)
    (hn1 : S.nLive n₁ = true) (hn2 : S.nLive n₂ = true) (ht1 : S.tet n₁ = t) (ht2 : S.tet n₂ = t)
    (hf : ∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l))
    (he1 : S.leg n₁ lA = eA) (he2 : S.leg n₂ lA = eA) (hfA : S.face eA = fA)
    (hneg : S.neg n₂ lA = S.neg n₁ lA) (hkap : S.kap eA = false)
    (hlA : ∀ l, l ≠ lA → S.leg n₁ l ≠ eA ∧ S.leg n₂ l ≠ eA)
    (hAo : ∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → ∀ l, S.leg n l ≠ eA)
    (hAc : ∀ c ∈ S.cons, c.1 ≠ eA ∧ c.2.1 ≠ eA) (hAt : fA ≠ t)
    (hte : ∀ e, S.eLive e = true → e ≠ eA → S.face e ≠ t ∧ S.face e ≠ fA)
    (htn : ∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t ∧ S.tet n ≠ fA)
    (htc : t ∉ S.cst) (hcA : Even (S.cst.count fA))
    (hA : ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cutA)
    (hk : cutA + ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cut) :
    ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k ∈ range (cut + 1),
      S.ev (Function.update (Function.update col fA jA) t k) = (S.loop n₁ n₂ lA).ev col := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, c = fun l => col (S.face (S.leg n₁ l)) := ⟨_, rfl⟩
  have hcl : ∀ l, col (S.face (S.leg n₁ l)) = c l := fun l => by rw [hc]
  simp only [hcl] at hA hk
  -- the looped network
  have lLive : (S.loop n₁ n₂ lA).eLive = Function.update S.eLive eA false := by rw [← he1]; rfl
  have lnLive : (S.loop n₁ n₂ lA).nLive = fun n => if n = n₁ ∨ n = n₂ then false else S.nLive n :=
    rfl
  have lCons : (S.loop n₁ n₂ lA).cons =
      List.ofFn (fun l => (S.leg n₁ l, S.leg n₂ l, xor (S.neg n₁ l) (S.neg n₂ l))) ++ S.cons := rfl
  have lCst : (S.loop n₁ n₂ lA).cst = S.cst.filter (· ≠ fA) := by rw [← hfA, ← he1]; rfl
  have hliveA : S.eLive eA = true := he1 ▸ hlegs _ hn1 lA
  -- colours
  have hcol : ∀ (jA k : ℕ) (f : F), f ≠ t → f ≠ fA →
      Function.update (Function.update col fA jA) t k f = col f := fun jA k f h1 h2 => by
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have hc' : ∀ (jA k : ℕ) l, Function.update (Function.update col fA jA) t k (S.face (S.leg n₁ l))
      = Function.update c lA jA l := by
    intro jA k l
    by_cases hl : l = lA
    · rw [hl, he1, hfA, Function.update_of_ne hAt, Function.update_self, Function.update_self]
    · have h := hte _ (hlegs _ hn1 l) (hlA l hl).1
      rw [hcol jA k _ h.1 h.2, hcl, Function.update_of_ne hl]
  have hfs : ∀ (jA k : ℕ), fsign S.cst (Function.update (Function.update col fA jA) t k) =
      fsign (S.loop n₁ n₂ lA).cst col := by
    intro jA k
    rw [fsign_filter_of_even _ hcA, lCst]
    refine fsign_congr fun f hf => ?_
    have hf' := List.mem_filter.1 hf
    exact hcol _ _ f (fun h => htc (h ▸ hf'.1)) (by simpa using hf'.2)
  -- the boxes
  have hboxA : ∀ (jA k : ℕ), S.box (Function.update (Function.update col fA jA) t k) eA =
      pbox jA := by
    intro jA k
    simp only [box, hliveA, ↓reduceIte, hfA, Function.update_of_ne hAt, Function.update_self]
  have hboxL : ∀ (jA k : ℕ),
      Function.update (S.box (Function.update (Function.update col fA jA) t k)) eA {0} =
        (S.loop n₁ n₂ lA).box col := by
    intro jA k; funext e
    unfold box
    by_cases he : e = eA
    · rw [he, Function.update_self, lLive, Function.update_self]; rfl
    · rw [Function.update_of_ne he, lLive, Function.update_of_ne he]
      by_cases hl : S.eLive e = true
      · have h := hte e hl he
        simp only [hl, ↓reduceIte, hcol _ _ _ h.1 h.2]
        rfl
      · simp only [hl, Bool.false_eq_true, ↓reduceIte]
  -- the factors
  have hE : ∀ (jA k : ℕ) (y : E → ℤ) (a : ℤ) e,
      S.eFac (Function.update (Function.update col fA jA) t k) (Function.update y eA a) e =
        (S.loop n₁ n₂ lA).eFac col y e := by
    intro jA k y a e
    by_cases he : e = eA
    · rw [he]; simp [eFac, hkap, lLive]
    · unfold eFac
      rw [lLive, Function.update_of_ne he, Function.update_of_ne he]
      by_cases hl : S.eLive e = true
      · have h := hte e hl he
        rw [hcol _ _ _ h.1 h.2]; rfl
      · simp [hl]
  have hN : ∀ (jA k : ℕ) (y : E → ℤ) (a : ℤ) n, n ≠ n₁ → n ≠ n₂ →
      S.nFac (Function.update (Function.update col fA jA) t k) (Function.update y eA a) n =
        (S.loop n₁ n₂ lA).nFac col y n := by
    intro jA k y a n h1 h2
    have : (S.loop n₁ n₂ lA).nFac col y n = S.nFac col y n := by
      unfold nFac
      simp only [lnLive, h1, h2, or_self, ↓reduceIte]
      rfl
    rw [this]
    refine nFac_congr fun hn => ⟨hcol _ _ _ (htn n hn h1 h2).1 (htn n hn h1 h2).2, fun l => ?_⟩
    have h := hte _ (hlegs n hn l) (hAo n hn h1 h2 l)
    exact ⟨hcol _ _ _ h.1 h.2, Function.update_of_ne (hAo n hn h1 h2 l) _ _⟩
  have hN12 : ∀ (y : E → ℤ) n, n = n₁ ∨ n = n₂ → (S.loop n₁ n₂ lA).nFac col y n = 1 := by
    intro y n hn; simp [nFac, lnLive, hn]
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℕ → (Fin 4 → ℤ) → ℤ → ℝ, I = fun jA k u μ =>
      fourJ (Function.update c lA jA 0) (Function.update c lA jA 2) (Function.update c lA jA 1)
        (Function.update c lA jA 3) k (Function.update u lA μ 0) (Function.update u lA μ 2)
        (Function.update u lA μ 1) (Function.update u lA μ 3) := ⟨_, rfl⟩
  have hι1 : ∀ (jA k : ℕ) (y : E → ℤ) (a : ℤ),
      S.nFac (Function.update (Function.update col fA jA) t k) (Function.update y eA a) n₁ =
        I jA k (S.args y n₁) (sg (S.neg n₁ lA) a) := by
    intro jA k y a
    have harg : ∀ l, S.args (Function.update y eA a) n₁ l =
        Function.update (S.args y n₁) lA (sg (S.neg n₁ lA) a) l := by
      intro l
      by_cases hl : l = lA
      · rw [hl, Function.update_self, args, he1, Function.update_self]
      · rw [Function.update_of_ne hl, args, args, Function.update_of_ne (hlA l hl).1]
    rw [hI]
    simp only [nFac, hn1, ↓reduceIte, nodeT, ht1, Function.update_self, hc', harg]
  have hι2 : ∀ (jA k : ℕ) (y : E → ℤ) (a : ℤ),
      S.nFac (Function.update (Function.update col fA jA) t k) (Function.update y eA a) n₂ =
        I jA k (S.args y n₂) (sg (S.neg n₁ lA) a) := by
    intro jA k y a
    have harg : ∀ l, S.args (Function.update y eA a) n₂ l =
        Function.update (S.args y n₂) lA (sg (S.neg n₁ lA) a) l := by
      intro l
      by_cases hl : l = lA
      · rw [hl, Function.update_self, args, he2, Function.update_self, hneg]
      · rw [Function.update_of_ne hl, args, args, Function.update_of_ne (hlA l hl).2]
    rw [hI]
    simp only [nFac, hn2, ↓reduceIte, nodeT, ht2, Function.update_self, hf, hc', harg]
  have hC : ∀ (y : E → ℤ) (a : ℤ),
      (S.cons.map (cFac (Function.update y eA a))).prod = (S.cons.map (cFac y)).prod := by
    intro y a
    congr 1
    refine List.map_congr_left fun c hc => ?_
    simp only [cFac, Function.update_of_ne (hAc c hc).1, Function.update_of_ne (hAc c hc).2]
  obtain ⟨Q, hQ⟩ : ∃ Q : (E → ℤ) → ℝ, Q = fun y => (∏ e, (S.loop n₁ n₂ lA).eFac col y e) *
      (∏ n, (S.loop n₁ n₂ lA).nFac col y n) * (S.cons.map (cFac y)).prod := ⟨_, rfl⟩
  have key1 : ∀ (jA k : ℕ) (y : E → ℤ) (a : ℤ),
      S.summand (Function.update (Function.update col fA jA) t k) (Function.update y eA a) =
        Q y * (I jA k (S.args y n₁) (sg (S.neg n₁ lA) a) *
          I jA k (S.args y n₂) (sg (S.neg n₁ lA) a)) := by
    intro jA k y a
    have hNall : ∀ n,
        S.nFac (Function.update (Function.update col fA jA) t k) (Function.update y eA a) n =
          (S.loop n₁ n₂ lA).nFac col y n *
            ((if n = n₁ then I jA k (S.args y n₁) (sg (S.neg n₁ lA) a) else 1) *
              (if n = n₂ then I jA k (S.args y n₂) (sg (S.neg n₁ lA) a) else 1)) := by
      intro n
      by_cases h1 : n = n₁
      · rw [h1, hN12 y n₁ (Or.inl rfl), hι1]; simp [h12]
      by_cases h2 : n = n₂
      · rw [h2, hN12 y n₂ (Or.inr rfl), hι2]; simp [Ne.symm h12]
      rw [hN jA k y a n h1 h2]; simp [h1, h2]
    rw [hQ]
    unfold summand
    simp only [hE, hNall, prod_mul_distrib, prod_ite_eq', mem_univ, ↓reduceIte, hC]
    ring
  have hLC : ∀ y : E → ℤ, ((S.loop n₁ n₂ lA).cons.map (cFac y)).prod =
      (∏ l, if l = lA ∨ S.args y n₁ l = S.args y n₂ l then 1 else 0) *
        (S.cons.map (cFac y)).prod := by
    intro y
    simp only [lCons, List.map_append, List.prod_append, List.map_ofFn, List.prod_ofFn]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Function.comp_apply, cFac, sg_xor_iff]
    by_cases hl : l = lA
    · have h : sg (S.neg n₁ l) (y (S.leg n₁ l)) = sg (S.neg n₂ l) (y (S.leg n₂ l)) := by
        rw [hl, he1, he2, hneg]
      simp only [h, ↓reduceIte]
      simp only [hl, true_or, ↓reduceIte]
    · simp only [hl, false_or, args]
  -- the evaluations
  have hev : ∀ (jA k : ℕ), S.ev (Function.update (Function.update col fA jA) t k) =
      fsign (S.loop n₁ n₂ lA).cst col * ∑ y ∈ Fintype.piFinset ((S.loop n₁ n₂ lA).box col),
        ∑ μ ∈ pbox jA, Q y * (I jA k (S.args y n₁) μ * I jA k (S.args y n₂) μ) := by
    intro jA k
    have hs := sum_piFinset_split (S.box (Function.update (Function.update col fA jA) t k)) eA
      (fun a x => S.summand (Function.update (Function.update col fA jA) t k)
        (Function.update x eA a)) (fun a μ => by simp only [Function.update_idem])
    simp only [Function.update_eq_self] at hs
    rw [ev, hfs, hs, hboxA, hboxL]
    refine congrArg (fsign (S.loop n₁ n₂ lA).cst col * ·) (sum_congr rfl fun y _ => ?_)
    simp only [key1]
    exact sum_pbox_sg (S.neg n₁ lA) jA
      (fun μ => Q y * (I jA k (S.args y n₁) μ * I jA k (S.args y n₂) μ))
  have hR : (S.loop n₁ n₂ lA).ev col = fsign (S.loop n₁ n₂ lA).cst col *
      ∑ y ∈ Fintype.piFinset ((S.loop n₁ n₂ lA).box col),
        Q y * ∏ l, if l = lA ∨ S.args y n₁ l = S.args y n₂ l then 1 else 0 := by
    rw [ev]
    refine congrArg (fsign (S.loop n₁ n₂ lA).cst col * ·) (sum_congr rfl fun y _ => ?_)
    rw [hQ, summand, hLC]
    ring
  have hy : ∀ y ∈ Fintype.piFinset ((S.loop n₁ n₂ lA).box col),
      ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k ∈ range (cut + 1), ∑ μ ∈ pbox jA,
        I jA k (S.args y n₁) μ * I jA k (S.args y n₂) μ =
      ∏ l, if l = lA ∨ S.args y n₁ l = S.args y n₂ l then 1 else 0 := by
    intro y hy
    have hu : ∀ l, l ≠ lA → S.args y n₁ l ∈ pbox (c l) := by
      intro l hl
      have h := Fintype.mem_piFinset.1 hy (S.leg n₁ l)
      simp only [box, lLive, Function.update_of_ne (hlA l hl).1, hlegs _ hn1 l, ↓reduceIte] at h
      rw [args, sg_mem_pbox, ← hcl]
      exact h
    rw [hI]
    exact loop_node c lA hu (S.args y n₂) cutA cut hA fun jA hjA =>
      (update_triad_le c lA jA).trans (by omega)
  rw [hR, ← sum_congr rfl fun y hy' => congrArg (Q y * ·) (hy y hy')]
  simp only [hev]
  simp only [mul_sum]
  conv_lhs => arg 2; ext jA; rw [sum_comm]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun jA _ => sum_congr rfl fun k _ =>
    sum_congr rfl fun μ _ => ?_
  ring

variable (S) in
/-- Dropping the first constraint (used when it reads `x e = x e`). -/
def dropTriv : SNet F E N := { S with cons := S.cons.tail }

omit [DecidableEq N] in
/-- A first constraint `(e, e, false)` always holds, so dropping it keeps the evaluation. -/
theorem ev_dropTriv {e : E} {rest : List (E × E × Bool)} (h : S.cons = (e, e, false) :: rest) :
    S.dropTriv.ev col = S.ev col := by
  have hs : ∀ x, S.dropTriv.summand col x = S.summand col x := by
    intro x
    have hc : S.dropTriv.cons = rest := by simp [dropTriv, h]
    unfold summand
    rw [hc, h, List.map_cons, List.prod_cons]
    simp only [cFac, sg, Bool.false_eq_true, ↓reduceIte, one_mul]
    rfl
  unfold ev
  simp only [hs]
  rfl

/-! ## Relabelling -/

omit [DecidableEq N] in
/-- **Relabelling.** Two constraint-free networks have the same evaluation when their live edges
and live nodes correspond bijectively with the same faces, edge signs, tetrahedra, legs and leg
signs, and each face occurs with the same parity in their constant signs. -/
theorem ev_relabel [DecidableEq F] {E' N' : Type*} [Fintype E'] [DecidableEq E'] [Fintype N']
    [DecidableEq N'] (S' : SNet F E' N') (σ : E → E') (τ : E' → E) (π : N → N') (ρ : N' → N)
    (hσ : ∀ e, S.eLive e = true → S'.eLive (σ e) = true ∧ τ (σ e) = e)
    (hτ : ∀ e', S'.eLive e' = true → S.eLive (τ e') = true ∧ σ (τ e') = e')
    (hπ : ∀ n, S.nLive n = true → S'.nLive (π n) = true ∧ ρ (π n) = n)
    (hρ : ∀ n', S'.nLive n' = true → S.nLive (ρ n') = true ∧ π (ρ n') = n')
    (hface : ∀ e, S.eLive e = true → S'.face (σ e) = S.face e ∧ S'.kap (σ e) = S.kap e)
    (hnode : ∀ n, S.nLive n = true → S'.tet (π n) = S.tet n ∧
      ∀ l, S'.leg (π n) l = σ (S.leg n l) ∧ S'.neg (π n) l = S.neg n l)
    (hlegs : ∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true)
    (hc : S.cons = []) (hc' : S'.cons = [])
    (hcst : ∀ f ∈ S.cst ++ S'.cst, S.cst.count f % 2 = S'.cst.count f % 2) :
    S.ev col = S'.ev col := by
  have hτface : ∀ e', S'.eLive e' = true → S'.face e' = S.face (τ e') := fun e' he' => by
    have h := (hface _ (hτ e' he').1).1
    rwa [(hτ e' he').2] at h
  unfold ev
  rw [fsign_eq_of_count col hcst]
  refine congrArg (fsign S'.cst col * ·) ?_
  refine sum_nbij' (fun x e' => if S'.eLive e' then x (τ e') else 0)
    (fun x' e => if S.eLive e then x' (σ e) else 0) (fun x hx => ?_) (fun x' hx' => ?_)
    (fun x hx => ?_) (fun x' hx' => ?_) (fun x hx => ?_)
  · rw [Fintype.mem_piFinset] at hx ⊢
    intro e'
    by_cases he' : S'.eLive e' = true
    · have h := hx (τ e')
      simp only [box, (hτ e' he').1, ↓reduceIte] at h
      simp only [box, he', ↓reduceIte, hτface e' he', h]
    · simp [box, he']
  · rw [Fintype.mem_piFinset] at hx' ⊢
    intro e
    by_cases he : S.eLive e = true
    · have h := hx' (σ e)
      simp only [box, (hσ e he).1, ↓reduceIte, (hface e he).1] at h
      simp only [box, he, ↓reduceIte, h]
    · simp [box, he]
  · funext e
    by_cases he : S.eLive e = true
    · simp only [he, ↓reduceIte, (hσ e he).1, (hσ e he).2]
    · have h := Fintype.mem_piFinset.1 hx e
      simp only [box, he, Bool.false_eq_true, ↓reduceIte, mem_singleton] at h
      simp [he, h]
  · funext e'
    by_cases he' : S'.eLive e' = true
    · simp only [he', ↓reduceIte, (hτ e' he').1, (hτ e' he').2]
    · have h := Fintype.mem_piFinset.1 hx' e'
      simp only [box, he', Bool.false_eq_true, ↓reduceIte, mem_singleton] at h
      simp [he', h]
  · unfold summand
    rw [hc, hc']
    simp only [List.map_nil, List.prod_nil, mul_one]
    congr 1
    · refine prod_live S.eLive S'.eLive σ τ hσ hτ _ _ (fun e he => by simp [eFac, he])
        (fun e' he' => by simp [eFac, he']) fun e he => ?_
      simp only [eFac, he, (hσ e he).1, (hface e he).1, (hface e he).2, ↓reduceIte,
        (hσ e he).2]
    · refine prod_live S.nLive S'.nLive π ρ hπ hρ _ _ (fun n hn => by simp [nFac, hn])
        (fun n' hn' => by simp [nFac, hn']) fun n hn => ?_
      have hl1 : ∀ l, S'.eLive (σ (S.leg n l)) = true := fun l => (hσ _ (hlegs n hn l)).1
      have hl2 : ∀ l, τ (σ (S.leg n l)) = S.leg n l := fun l => (hσ _ (hlegs n hn l)).2
      have hl3 : ∀ l, S'.face (σ (S.leg n l)) = S.face (S.leg n l) := fun l =>
        (hface _ (hlegs n hn l)).1
      have hn1 : ∀ l, S'.leg (π n) l = σ (S.leg n l) := fun l => ((hnode n hn).2 l).1
      have hn2 : ∀ l, S'.neg (π n) l = S.neg n l := fun l => ((hnode n hn).2 l).2
      simp only [nFac, hn, (hπ n hn).1, ↓reduceIte, nodeT, args, (hnode n hn).1, hn1, hn2, hl1,
        hl2, hl3]

end SNet

/-! ## The vertex network -/

/-- A sum over a box of projections on `Fin (n + 1)`, peeled at the first coordinate. -/
lemma sum_piFinset_vecCons {n : ℕ} (B : Fin (n + 1) → Finset ℤ) (G : (Fin (n + 1) → ℤ) → ℝ) :
    ∑ x ∈ Fintype.piFinset B, G x =
      ∑ a ∈ B 0, ∑ y ∈ Fintype.piFinset (fun i => B i.succ), G (Matrix.vecCons a y) := by
  rw [← sum_product']
  symm
  apply sum_nbij' (fun p => Matrix.vecCons p.1 p.2) (fun x => (x 0, Fin.tail x))
  · rintro ⟨a, y⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h.1
    · simpa using h.2 i
  · intro x hx
    simp only [mem_product, Fintype.mem_piFinset] at hx ⊢
    exact ⟨hx 0, fun i => hx i.succ⟩
  · rintro ⟨a, y⟩ _
    simp
  · intro x _
    exact Fin.cons_self_tail x
  · rintro ⟨a, y⟩ _
    rfl

/-- A sum over the box of projections on `Fin 0` has the single term `![]`. -/
lemma sum_piFinset_fin_zero (B : Fin 0 → Finset ℤ) (G : (Fin 0 → ℤ) → ℝ) :
    ∑ x ∈ Fintype.piFinset B, G x = G ![] := by
  have : Fintype.piFinset B = {![]} := by
    ext x
    simp only [Fintype.mem_piFinset, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
  rw [this, sum_singleton]

/-- A nonzero node tensor has admissible projections on all its legs. -/
lemma nodeT_adm {F : Type*} {col : F → ℕ} {t : F} {f : Fin 4 → F} {m : Fin 4 → ℤ}
    (h : nodeT col t f m ≠ 0) (l : Fin 4) : AdmProj (col (f l)) (m l) := by
  have hs := (isInv_fourJT (col (f 0)) (col (f 2)) (col (f 1)) (col (f 3)) (col t)).supp
    ![m 0, m 2, m 1, m 3] (by simpa [fourJT, nodeT] using h)
  fin_cases l
  · simpa using hs 0
  · simpa using hs 2
  · simpa using hs 1
  · simpa using hs 3

namespace SNet

variable {F E N : Type*} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
variable (S : SNet F E N) (col : F → ℕ)

/-- All projections `|x| ≤ j` on a live edge (admissible or not), `0` on a dead one. -/
def ibox (e : E) : Finset ℤ := if S.eLive e then Icc (-(col (S.face e) : ℤ)) (col (S.face e)) else {0}

variable {S col}

omit [DecidableEq N] in
/-- When every live edge is a leg of a live node, the evaluation may sum over all projections
`|x| ≤ j` instead of the admissible ones: the node tensors vanish on the others. -/
theorem sum_ibox (hcov : ∀ e, S.eLive e = true → ∃ n l, S.nLive n = true ∧ S.leg n l = e) :
    ∑ x ∈ Fintype.piFinset (S.ibox col), S.summand col x =
      ∑ x ∈ Fintype.piFinset (S.box col), S.summand col x := by
  symm
  apply sum_subset
  · intro x hx
    simp only [Fintype.mem_piFinset, box, ibox] at hx ⊢
    intro e
    have h := hx e
    split_ifs at h ⊢
    · exact (mem_filter.1 h).1
    · exact h
  · intro x hx hx'
    simp only [Fintype.mem_piFinset, not_forall] at hx hx'
    obtain ⟨e, he⟩ := hx'
    have hl : S.eLive e = true := by
      by_contra hl
      have h := hx e
      simp only [ibox, box, hl, ↓reduceIte] at h he
      exact he h
    have hna : ¬AdmProj (col (S.face e)) (x e) := fun h =>
      he (by simpa [box, hl] using mem_pbox.2 h)
    obtain ⟨n, l, hn, hnl⟩ := hcov e hl
    have hz : S.nFac col x n = 0 := by
      simp only [nFac, hn, ↓reduceIte]
      by_contra h
      have := nodeT_adm h l
      simp only [args, hnl] at this
      exact hna (mem_pbox.1 (sg_mem_pbox.1 (mem_pbox.2 this)))
    simp only [summand]
    rw [prod_eq_zero (mem_univ n) hz]
    ring

end SNet

/-- The position pairs `(p, q)`, `p < q`, of the ten triangles of a 4-simplex (the triangle
opposite the vertices `p` and `q`), in the order of the sums of `contrP`. -/
def vtriP : Fin 10 → Fin 5 := ![0, 0, 0, 0, 2, 1, 2, 1, 3, 1]

/-- The second positions of the triangles, see `vtriP`. -/
def vtriQ : Fin 10 → Fin 5 := ![2, 4, 1, 3, 4, 2, 3, 4, 4, 3]

/-- The triangle on leg `l` of tetrahedron `i` of a 4-simplex: the one opposite the positions `i`
and `i.succAbove l` (see `vleg_spec`). -/
def vleg : Fin 5 → Fin 4 → Fin 10 :=
  ![![2, 0, 3, 1], ![2, 5, 9, 7], ![0, 5, 6, 4], ![3, 9, 6, 8], ![1, 7, 4, 8]]

/-- Whether leg `l` of tetrahedron `i` reads the negated projection: the leg sign
`σPlus i (i.succAbove l)` is `-1` (see `vneg_spec`). -/
def vneg : Fin 5 → Fin 4 → Bool :=
  ![![false, true, false, true], ![true, true, false, true], ![false, false, false, true],
    ![true, true, true, true], ![false, false, false, false]]

/-- The legs of the vertex network are the triangles of the right position pairs. -/
lemma vleg_spec (i : Fin 5) (l : Fin 4) :
    vtriP (vleg i l) < vtriQ (vleg i l) ∧
      ((vtriP (vleg i l) = i ∧ vtriQ (vleg i l) = i.succAbove l) ∨
        (vtriQ (vleg i l) = i ∧ vtriP (vleg i l) = i.succAbove l)) := by
  revert i l; decide

/-- The leg signs of the vertex network are those of `σPlus`. -/
lemma vneg_spec (i : Fin 5) (l : Fin 4) : vneg i l = decide (σPlus i (i.succAbove l) = -1) := by
  revert i l; decide

namespace SNet

variable {F : Type*}

/-- **The vertex network** of a 4-simplex whose triangles carry the labels `fc` (in the order
`vtriP`, `vtriQ`) and whose tetrahedra (opposite each position) carry the labels `tt`: ten edges with
the sign of the bilinear form, five nodes, legs `vleg` with signs `vneg`. -/
def vnet (fc : Fin 10 → F) (tt : Fin 5 → F) : SNet F (Fin 10) (Fin 5) where
  face := fc
  kap _ := true
  eLive _ := true
  tet := tt
  nLive _ := true
  leg := vleg
  neg := vneg
  cons := []
  cst := []

/-- **The vertex network evaluates to the vertex contraction** `contrP σPlus J K`, for the spins
`J (vtriP e) (vtriQ e)` of its triangles and `K i` of its tetrahedra. -/
theorem ev_vnet (fc : Fin 10 → F) (tt : Fin 5 → F) (col : F → ℕ) (J : Fin 5 → Fin 5 → ℕ)
    (K : Fin 5 → ℕ) (hJ : ∀ e, col (fc e) = J (vtriP e) (vtriQ e)) (hK : ∀ i, col (tt i) = K i) :
    (vnet fc tt).ev col = contrP σPlus J K := by
  unfold ev
  rw [show (vnet fc tt).cst = [] from rfl, fsign_nil, one_mul, ← sum_ibox fun e _ =>
    (by decide : ∀ e : Fin 10, ∃ n l, true = true ∧ vleg n l = e) e]
  rw [show (vnet fc tt).ibox col = fun e => Icc (-(J (vtriP e) (vtriQ e) : ℤ)) (J (vtriP e) (vtriQ e))
    from funext fun e => by simp [ibox, vnet, hJ]]
  simp only [sum_piFinset_vecCons, sum_piFinset_fin_zero]
  unfold contrP
  refine sum_congr rfl fun a02 _ => sum_congr rfl fun a04 _ => sum_congr rfl fun a01 _ =>
    sum_congr rfl fun a03 _ => sum_congr rfl fun a24 _ => sum_congr rfl fun a12 _ =>
    sum_congr rfl fun a23 _ => sum_congr rfl fun a14 _ => sum_congr rfl fun a34 _ =>
    sum_congr rfl fun a13 _ => ?_
  simp only [summand, eFac, nFac, nodeT, args, vnet, Fin.prod_univ_succ, Fin.prod_univ_zero,
    hJ, hK, Bool.and_self, ↓reduceIte, List.map_nil, List.prod_nil, mul_one]
  simp only [Fin.reduceSucc, Matrix.cons_val, vtriP, vtriQ, vleg, vneg, sg, Bool.false_eq_true,
    ↓reduceIte, σPlus, one_mul, neg_one_mul]
  ring

/-! ## Disjoint unions -/

section Union

variable {E N ι : Type*} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype ι]
  [DecidableEq ι]

/-- **The disjoint union** of a family of networks (meant for networks without constraints and
constant signs, see `ev_union`). -/
def union (S : ι → SNet F E N) : SNet F (ι × E) (ι × N) where
  face p := (S p.1).face p.2
  kap p := (S p.1).kap p.2
  eLive p := (S p.1).eLive p.2
  tet q := (S q.1).tet q.2
  nLive q := (S q.1).nLive q.2
  leg q l := (q.1, (S q.1).leg q.2 l)
  neg q l := (S q.1).neg q.2 l
  cons := []
  cst := []

omit [DecidableEq N] in
/-- **A disjoint union evaluates to the product** of its parts, when these carry no constraints
and no constant signs. -/
theorem ev_union (S : ι → SNet F E N) (col : F → ℕ) (h : ∀ i, (S i).cons = [] ∧ (S i).cst = []) :
    (union S).ev col = ∏ i, (S i).ev col := by
  have hR : ∀ i, (S i).ev col = ∑ y ∈ Fintype.piFinset ((S i).box col), (S i).summand col y :=
    fun i => by rw [ev, (h i).2, fsign_nil, one_mul]
  simp only [hR]
  rw [prod_univ_sum, ev, show (union S).cst = [] from rfl, fsign_nil, one_mul]
  apply sum_nbij' (fun x i e => x (i, e)) (fun Y p => Y p.1 p.2)
  · intro x hx
    simp only [Fintype.mem_piFinset] at hx ⊢
    exact fun i e => hx (i, e)
  · intro Y hY
    simp only [Fintype.mem_piFinset] at hY ⊢
    exact fun p => hY p.1 p.2
  · intro x _
    rfl
  · intro Y _
    rfl
  · intro x _
    have hc : ∀ i, ((S i).cons.map (cFac fun e => x (i, e))).prod = 1 := fun i => by
      rw [(h i).1]; rfl
    simp only [summand, hc, mul_one, Fintype.prod_prod_type, ← prod_mul_distrib]
    rw [show (union S).cons = [] from rfl, List.map_nil, List.prod_nil, mul_one]
    rfl

end Union

end SNet

/-! ## Turning several legs around -/

section FlipV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {j : ι → ℕ} {d : ι → Bool}
  {X : (ι → ℤ) → ℝ}

/-- Turning the legs `i` with `b i` around (`flipAt` on each of them):
`(flipV a b X)(m) = Π_{b i} (-1)^((a i + m i)/2) · X(i ↦ ± m i)`. -/
noncomputable def flipV (a : ι → ℕ) (b : ι → Bool) (X : (ι → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  (∏ i, if b i then (-1 : ℝ) ^ (((a i : ℤ) + m i) / 2) else 1) * X (fun i => sg (b i) (m i))

/-- Turning one more leg around. -/
lemma flipV_insert (a : ι → ℕ) {s : Finset ι} {i : ι} (hi : i ∉ s) (X : (ι → ℤ) → ℝ) :
    flipV a (fun k => decide (k ∈ insert i s)) X =
      flipAt (a i) i (flipV a (fun k => decide (k ∈ s)) X) := by
  funext m
  simp only [flipV, flipAt, decide_eq_true_eq]
  rw [prod_ite_mem, prod_ite_mem, univ_inter, univ_inter, prod_insert hi]
  have h1 : ∏ k ∈ s, (-1 : ℝ) ^ (((a k : ℤ) + Function.update m i (-m i) k) / 2) =
      ∏ k ∈ s, (-1 : ℝ) ^ (((a k : ℤ) + m k) / 2) :=
    prod_congr rfl fun k hk => by
      rw [Function.update_of_ne (show k ≠ i from fun h => hi (h ▸ hk))]
  have h2 : (fun k => sg (decide (k ∈ s)) (Function.update m i (-m i) k)) =
      fun k => sg (decide (k ∈ insert i s)) (m k) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [sg, hi]
    · simp [hk]
  rw [h1, h2, mul_assoc]

/-- **Turning several legs around keeps a tensor invariant**, with those legs' directions
reversed. -/
theorem isInv_flipV (hX : IsInv j d X) (b : ι → Bool) :
    IsInv j (fun i => xor (d i) (b i)) (flipV j b X) := by
  obtain ⟨s, rfl⟩ : ∃ s : Finset ι, (fun k => decide (k ∈ s)) = b :=
    ⟨univ.filter (b · = true), funext fun k => by simp⟩
  induction s using Finset.induction_on with
  | empty =>
    have hd : (fun i => xor (d i) (decide (i ∈ (∅ : Finset ι)))) = d := by funext i; simp
    rw [hd]
    exact hX.congr fun m => by simp only [Lightlike.SpinFoam.flipV, notMem_empty, decide_false,
      Bool.false_eq_true, ↓reduceIte, prod_const_one, one_mul, sg]
  | insert i s hi ih =>
    rw [flipV_insert j hi]
    have hd : (fun k => xor (d k) (decide (k ∈ insert i s))) =
        Function.update (fun k => xor (d k) (decide (k ∈ s))) i
          (!(fun k => xor (d k) (decide (k ∈ s))) i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp [hi]
      · simp [hk]
    rw [hd]
    exact ih.flip i

/-- Turning legs around with the sign `edgeSign` of the bilinear form at the projection read:
`(eflipV a b X)(m) = Π_{b i} (-1)^((a i - m i)/2) · X(i ↦ ± m i)`. -/
noncomputable def eflipV (a : ι → ℕ) (b : ι → Bool) (X : (ι → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  (∏ i, if b i then edgeSign (a i) (m i) else 1) * X (fun i => sg (b i) (m i))

/-- **Turning legs around with the sign `edgeSign` keeps a tensor invariant** (it differs from
`flipV` by the constant `Π_{b i} (-1)^{a i}` on the support). -/
theorem isInv_eflipV (hX : IsInv j d X) (b : ι → Bool) :
    IsInv j (fun i => xor (d i) (b i)) (eflipV j b X) := by
  refine ((isInv_flipV hX b).smul (∏ i, if b i then (-1 : ℝ) ^ j i else 1)).congr fun m => ?_
  unfold eflipV Lightlike.SpinFoam.flipV
  by_cases h0 : X (fun i => sg (b i) (m i)) = 0
  · simp [h0]
  · have hs := hX.supp _ h0
    rw [← mul_assoc, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    by_cases hb : b i = true
    · have ha := hs i
      simp only [hb, sg, ↓reduceIte] at ha
      have hpar : ((j i : ℤ) - m i) % 2 = 0 := by unfold AdmProj at ha; omega
      have e1 : (-1 : ℝ) ^ (((j i : ℤ) + m i) / 2) = edgeSign (j i) (-m i) := by
        unfold edgeSign; rw [sub_neg_eq_add]
      simp only [hb, ↓reduceIte, e1, edgeSign_neg hpar, ← mul_assoc, ← pow_add, ← two_mul,
        pow_mul, neg_one_sq, one_pow, one_mul]
    · simp [hb]

end FlipV

/-- The intertwiner of a node is an invariant tensor with four incoming legs. -/
lemma isInv_nodeT {F : Type*} (col : F → ℕ) (t : F) (f : Fin 4 → F) :
    IsInv (fun l => col (f l)) (fun _ => false) (nodeT col t f) := by
  have h := isInv_fourJP (fun l => col (f l)) (Equiv.swap 1 2) (col t)
  have hc : (![false, false, false, false] : Fin 4 → Bool) = fun _ => false := by
    funext i; fin_cases i <;> rfl
  rw [hc] at h
  refine h.congr fun m => ?_
  simp [nodeT, fourJP, fourJT, Equiv.swap_apply_of_ne_of_ne]

/-- A sum over a box against the indicator of one point. -/
lemma sum_pi_delta {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → Finset ℤ) (v : ι → ℤ)
    (H : (ι → ℤ) → ℝ) :
    ∑ w ∈ Fintype.piFinset C, (∏ l, if w l = v l then (1 : ℝ) else 0) * H w =
      if v ∈ Fintype.piFinset C then H v else 0 := by
  have hp : ∀ w : ι → ℤ, (∏ l, if w l = v l then (1 : ℝ) else 0) = if w = v then 1 else 0 := by
    intro w
    by_cases hw : w = v
    · subst hw; simp
    · obtain ⟨l, hl⟩ : ∃ l, w l ≠ v l := by
        by_contra h; exact hw (funext fun l => by simpa using (not_exists.mp h) l)
      rw [ite_eq_right hw]
      exact prod_eq_zero (mem_univ l) (by simp [hl])
  simp only [hp, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq']

/-! ## The remainder of a vertex network

Removing one node `i` of the vertex network leaves a network with four open legs (the triangles
of the tetrahedron `i`) and six internal edges (`vint i`). Its tensor is invariant
(`isInv_rem_vnet`): it is a network of invariant tensors in the sense of `netEval`, once the legs
reading an unsigned projection are turned around. -/

/-- The six triangles of a 4-simplex off the tetrahedron `i`, in increasing order. -/
def vint : Fin 5 → Fin 6 → Fin 10 :=
  ![![4, 5, 6, 7, 8, 9], ![0, 1, 3, 4, 6, 8], ![1, 2, 3, 7, 8, 9], ![0, 1, 2, 4, 5, 7],
    ![0, 2, 3, 5, 6, 9]]

/-- The leg of the tetrahedron `i` on the triangle `e` (`0` if `e` is not on it). -/
def vpos : Fin 5 → Fin 10 → Fin 4 :=
  ![![1, 3, 0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 3, 0, 2],
    ![0, 0, 0, 0, 3, 1, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0, 3, 1],
    ![0, 0, 0, 0, 2, 0, 0, 1, 3, 0]]

/-- The position of the triangle `e` in `vint i` (`0` if `e` is on the tetrahedron `i`). -/
def vipos : Fin 5 → Fin 10 → Fin 6 :=
  ![![0, 0, 0, 0, 0, 1, 2, 3, 4, 5], ![0, 1, 0, 2, 3, 0, 4, 0, 5, 0],
    ![0, 0, 1, 2, 0, 0, 0, 3, 4, 5], ![0, 1, 2, 0, 3, 4, 0, 5, 0, 0],
    ![0, 0, 1, 2, 0, 3, 4, 0, 0, 5]]

lemma vpos_vleg (i : Fin 5) (l : Fin 4) : vpos i (vleg i l) = l := by revert i l; decide

lemma vint_spec (i : Fin 5) (p : Fin 6) :
    vleg i (vpos i (vint i p)) ≠ vint i p ∧ vipos i (vint i p) = p := by revert i p; decide

lemma vint_vipos (i : Fin 5) (e : Fin 10) (h : vleg i (vpos i e) ≠ e) : vint i (vipos i e) = e := by
  revert i e; decide

/-- The two legs on a triangle carry opposite signs. -/
lemma vneg_opp (i : Fin 5) (k l : Fin 4)
    (h : vleg i (vpos i (vleg (i.succAbove k) l)) = vleg (i.succAbove k) l) :
    vneg i (vpos i (vleg (i.succAbove k) l)) = !vneg (i.succAbove k) l := by
  revert i k l; decide

/-- The leg-ends of the vertex network without its node `i`: leg `l` of the node
`i.succAbove k` is either the open leg of `i` on the same triangle, or an end of an internal
triangle, outgoing when the leg reads the unsigned projection. -/
def vlegEnd (i : Fin 5) (p : Σ _ : Fin 4, Fin 4) : Fin 4 ⊕ (Fin 6 × Bool) :=
  if vleg i (vpos i (vleg (i.succAbove p.1) p.2)) = vleg (i.succAbove p.1) p.2 then
    Sum.inl (vpos i (vleg (i.succAbove p.1) p.2))
  else Sum.inr (vipos i (vleg (i.succAbove p.1) p.2), !vneg (i.succAbove p.1) p.2)

lemma vlegEnd_bij (i : Fin 5) : Function.Bijective (vlegEnd i) := by revert i; decide

/-- The leg-ends of the vertex network without its node `i`, as an equivalence. -/
noncomputable def vlegEq (i : Fin 5) : (Σ _ : Fin 4, Fin 4) ≃ Fin 4 ⊕ (Fin 6 × Bool) :=
  Equiv.ofBijective (vlegEnd i) (vlegEnd_bij i)

/-- A product over the ten triangles, read at the legs with the unsigned projection. -/
lemma vprod_edges (G : Fin 10 → ℝ) :
    ∏ e, G e = ∏ n : Fin 5, ∏ l : Fin 4, if vneg n l then 1 else G (vleg n l) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.reduceSucc, Matrix.cons_val, vleg, vneg,
    Bool.false_eq_true, ↓reduceIte, mul_one, one_mul]
  ring

namespace SNet

variable {F : Type*} (fc : Fin 10 → F) (tt : Fin 5 → F) (col : F → ℕ)

/-- The tensor of the node `n` of the vertex network with the legs that read the unsigned
projection turned around. -/
noncomputable def vT (n : Fin 5) : (Fin 4 → ℤ) → ℝ :=
  flipV (fun l => col (fc (vleg n l))) (fun l => !vneg n l)
    (nodeT col (tt n) (fun l => fc (vleg n l)))

lemma isInv_vT (n : Fin 5) :
    IsInv (fun l => col (fc (vleg n l))) (fun l => !vneg n l) (vT fc tt col n) := by
  have h := isInv_flipV (isInv_nodeT col (tt n) (fun l => fc (vleg n l))) (fun l => !vneg n l)
  simp only [Bool.false_xor] at h
  exact h

lemma vT_neg (n : Fin 5) (z : Fin 10 → ℤ) :
    vT fc tt col n (fun l => -z (vleg n l)) =
      (∏ l, if vneg n l then 1 else edgeSign (col (fc (vleg n l))) (z (vleg n l))) *
        nodeT col (tt n) (fun l => fc (vleg n l)) (fun l => sg (vneg n l) (z (vleg n l))) := by
  unfold vT flipV
  congr 1
  · refine prod_congr rfl fun l _ => ?_
    cases h : vneg n l <;> simp [h, edgeSign, sub_eq_add_neg]
  · congr 1
    funext l
    cases h : vneg n l <;> simp [h]

/-- The network of the vertex network without its node `i`. -/
noncomputable def vrN (i : Fin 5) : (Fin 4 → ℤ) → ℝ :=
  netEval (vlegEq i) (fun p => col (fc (vint i p))) (fun k => vT fc tt col (i.succAbove k))

lemma isInv_vrN (i : Fin 5) :
    IsInv (fun l => col (fc (vleg i l))) (fun l => vneg i l) (vrN fc tt col i) := by
  refine isInv_netEval (vlegEq i) _ (fun k => isInv_vT fc tt col (i.succAbove k)) ?_ ?_
  · rintro ⟨k, l⟩
    simp only [vlegEq, Equiv.ofBijective_apply, vlegEnd]
    split_ifs with h
    · simp [h]
    · simp [vint_vipos i _ h]
  · rintro ⟨k, l⟩
    simp only [vlegEq, Equiv.ofBijective_apply, vlegEnd]
    split_ifs with h
    · simp [vneg_opp i k l h]
    · simp

/-- Merging the projections on the legs of the tetrahedron `i` with those of the other
triangles. -/
def vmerge (i : Fin 5) (w : Fin 4 → ℤ) (y : Fin 6 → ℤ) (e : Fin 10) : ℤ :=
  if vleg i (vpos i e) = e then w (vpos i e) else y (vipos i e)

lemma vmerge_leg (i : Fin 5) (w : Fin 4 → ℤ) (y : Fin 6 → ℤ) (l : Fin 4) :
    vmerge i w y (vleg i l) = w l := by
  simp [vmerge, vpos_vleg]

lemma vmerge_int (i : Fin 5) (w : Fin 4 → ℤ) (y : Fin 6 → ℤ) (p : Fin 6) :
    vmerge i w y (vint i p) = y p := by
  simp [vmerge, (vint_spec i p).1, (vint_spec i p).2]

/-- A sum over the projections of the ten triangles, split at the tetrahedron `i`. -/
lemma sum_vsplit (i : Fin 5) (J : Fin 10 → ℕ) (G : (Fin 10 → ℤ) → ℝ) :
    ∑ z ∈ Fintype.piFinset (fun e => pbox (J e)), G z =
      ∑ w ∈ Fintype.piFinset (fun l => pbox (J (vleg i l))),
        ∑ y ∈ Fintype.piFinset (fun p => pbox (J (vint i p))), G (vmerge i w y) := by
  rw [← sum_product']
  symm
  apply sum_nbij' (fun wy => vmerge i wy.1 wy.2) (fun z => (fun l => z (vleg i l), fun p => z (vint i p)))
  · rintro ⟨w, y⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro e
    unfold vmerge
    split_ifs with he
    · simpa [he] using h.1 (vpos i e)
    · simpa [vint_vipos i e he] using h.2 (vipos i e)
  · intro z hz
    simp only [mem_product, Fintype.mem_piFinset] at hz ⊢
    exact ⟨fun l => hz _, fun p => hz _⟩
  · rintro ⟨w, y⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨funext fun l => vmerge_leg i w y l, funext fun p => vmerge_int i w y p⟩
  · intro z _
    funext e
    unfold vmerge
    split_ifs with he
    · dsimp only; rw [he]
    · dsimp only; rw [vint_vipos i e he]
  · intro _ _
    rfl

lemma vlegEq_inr {i : Fin 5} {q : Σ _ : Fin 4, Fin 4} {p : Fin 6} {b : Bool}
    (h : vlegEq i q = Sum.inr (p, b)) : vleg (i.succAbove q.1) q.2 = vint i p := by
  simp only [vlegEq, Equiv.ofBijective_apply, vlegEnd] at h
  split_ifs at h with h'
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  rw [← h.1, vint_vipos i _ h']

lemma vlegVal (i : Fin 5) (v : Fin 4 → ℤ) (μ : Fin 6 → ℤ) (k l : Fin 4) :
    legVal (vlegEq i) (fun l => -v l) μ ⟨k, l⟩ = -vmerge i v (-μ) (vleg (i.succAbove k) l) := by
  simp only [legVal, vlegEq, Equiv.ofBijective_apply, vlegEnd, vmerge]
  split_ifs <;> simp

/-- The network `vrN` as a sum over the admissible projections of the six inner triangles. -/
lemma vrN_eq (i : Fin 5) (v : Fin 4 → ℤ) :
    vrN fc tt col i (fun l => -v l) =
      ∑ y ∈ Fintype.piFinset (fun p => pbox (col (fc (vint i p)))),
        ∏ k, vT fc tt col (i.succAbove k) (fun l => -vmerge i v y (vleg (i.succAbove k) l)) := by
  unfold vrN netEval
  rw [← sum_subset (s₁ := Fintype.piFinset (fun p => pbox (col (fc (vint i p))))) ?_ ?_]
  · apply sum_nbij' (fun μ => -μ) (fun y => -y)
    · intro μ hμ
      simp only [Fintype.mem_piFinset] at hμ ⊢
      intro p
      simpa [mem_pbox, admProj_neg] using hμ p
    · intro y hy
      simp only [Fintype.mem_piFinset] at hy ⊢
      intro p
      simpa [mem_pbox, admProj_neg] using hy p
    · intro μ _; simp
    · intro y _; simp
    · intro μ _
      refine prod_congr rfl fun k _ => ?_
      congr 1
      funext l
      exact vlegVal i v μ k l
  · intro μ hμ
    simp only [Fintype.mem_piFinset] at hμ ⊢
    exact fun p => (mem_filter.1 (hμ p)).1
  · intro μ _ hμ'
    simp only [Fintype.mem_piFinset, not_forall] at hμ'
    obtain ⟨p, hp⟩ := hμ'
    obtain ⟨⟨k, l⟩, hkl⟩ : ∃ q, vlegEq i q = Sum.inr (p, true) := ⟨_, Equiv.apply_symm_apply _ _⟩
    refine prod_eq_zero (mem_univ k) ((isInv_vT fc tt col (i.succAbove k)).eq_zero (i := l) ?_)
    have h := vlegEq_inr hkl
    simp only at h
    simp only [legVal, hkl, Sum.elim_inr, h]
    exact fun h => hp (mem_pbox.2 h)

lemma qIn_vnet (i : Fin 5) (z : Fin 10 → ℤ) :
    (vnet fc tt).qIn col (fun _ => true) (fun _ => true) i z =
      (∏ l, if vneg i l then 1 else edgeSign (col (fc (vleg i l))) (z (vleg i l))) *
        ∏ k, vT fc tt col (i.succAbove k) (fun l => -z (vleg (i.succAbove k) l)) := by
  simp only [qIn, eFac, nFac, args_def, vnet, Bool.and_self, ↓reduceIte, true_and]
  rw [vprod_edges (fun e => edgeSign (col (fc e)) (z e)), Fin.prod_univ_succAbove _ i,
    Fin.prod_univ_succAbove _ i]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, one_mul, Fin.succAbove_ne, not_false_eq_true,
    vT_neg, prod_mul_distrib]
  ring

/-- **The remainder of the vertex network** at its node `i` is the network `vrN` with the legs of
`i` that read the unsigned projection turned around. -/
lemma rem_vnet_eq (i : Fin 5) (m : Fin 4 → ℤ) :
    (vnet fc tt).rem col (fun _ => true) (fun _ => true) i m =
      eflipV (fun l => col (fc (vleg i l))) (fun l => !vneg i l) (vrN fc tt col i) m := by
  have h1 : (vnet fc tt).rem col (fun _ => true) (fun _ => true) i m =
      ∑ z ∈ Fintype.piFinset (fun e => pbox (col (fc e))),
        (vnet fc tt).qIn col (fun _ => true) (fun _ => true) i z *
          ∏ l, if sg (vneg i l) (z (vleg i l)) = m l then (1 : ℝ) else 0 := rfl
  have h2 : ∀ w : Fin 4 → ℤ, (∑ y ∈ Fintype.piFinset (fun p => pbox (col (fc (vint i p)))),
      (vnet fc tt).qIn col (fun _ => true) (fun _ => true) i (vmerge i w y) *
        ∏ l, if sg (vneg i l) (vmerge i w y (vleg i l)) = m l then (1 : ℝ) else 0) =
      (∏ l, if w l = sg (vneg i l) (m l) then (1 : ℝ) else 0) *
        ((∏ l, if vneg i l then 1 else edgeSign (col (fc (vleg i l))) (w l)) *
          ∑ y ∈ Fintype.piFinset (fun p => pbox (col (fc (vint i p)))),
            ∏ k, vT fc tt col (i.succAbove k) (fun l => -vmerge i w y (vleg (i.succAbove k) l))) := by
    intro w
    simp only [qIn_vnet, vmerge_leg, sg_eq_iff, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring
  rw [h1, sum_vsplit i (fun e => col (fc e))]
  simp only [h2]
  rw [sum_pi_delta]
  unfold eflipV
  split_ifs with hv
  · rw [show (fun l => sg (!vneg i l) (m l)) = fun l => -(sg (vneg i l) (m l)) from
      funext fun l => sg_not _ _, vrN_eq]
    congr 1
    refine prod_congr rfl fun l _ => ?_
    cases h : vneg i l <;> simp [h]
  · simp only [Fintype.mem_piFinset, not_forall] at hv
    obtain ⟨l, hl⟩ := hv
    rw [(isInv_vrN fc tt col i).eq_zero (i := l), mul_zero]
    rw [sg_not, admProj_neg]
    exact fun h => hl (mem_pbox.2 h)

/-- **The remainder of the vertex network at any node is invariant**: the hypothesis of
`ev_glue` for a block made of one vertex network. -/
theorem isInv_rem_vnet (i : Fin 5) :
    IsInv (fun l => col ((vnet fc tt).face ((vnet fc tt).leg i l))) (fun _ => false)
      ((vnet fc tt).rem col (fun _ => true) (fun _ => true) i) := by
  have h := (isInv_eflipV (isInv_vrN fc tt col i) (fun l => !vneg i l)).dual
  have hd : (fun l => !xor (vneg i l) (!vneg i l)) = fun _ => false := by
    funext l; cases vneg i l <;> rfl
  rw [hd] at h
  exact h.congr fun m => rem_vnet_eq fc tt col i m

section Block

variable {ι F E N : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N]

/-- **The remainder of an untouched block.** If a network on blocks agrees with `B` on the edges
and nodes of its block `b`, and the legs of these nodes stay in the block, then its remainder at a
node of the block is that of `B`. -/
theorem rem_block (S : SNet F (ι × E) (ι × N)) (B : SNet F E N) (col : F → ℕ) (b : ι) (n₁ : N)
    (hface : ∀ e, S.face (b, e) = B.face e) (hkap : ∀ e, S.kap (b, e) = B.kap e)
    (hlive : ∀ e, S.eLive (b, e) = B.eLive e) (htet : ∀ n, S.tet (b, n) = B.tet n)
    (hnLive : ∀ n, S.nLive (b, n) = B.nLive n) (hleg : ∀ n l, S.leg (b, n) l = (b, B.leg n l))
    (hneg : ∀ n l, S.neg (b, n) l = B.neg n l) :
    S.rem col (fun p => decide (p.1 = b)) (fun q => decide (q.1 = b)) (b, n₁) =
      B.rem col (fun _ => true) (fun _ => true) n₁ := by
  funext m
  unfold rem
  symm
  apply sum_nbij' (fun y p => if p.1 = b then y p.2 else 0) (fun z e => z (b, e))
  · intro y hy
    simp only [Fintype.mem_piFinset] at hy ⊢
    rintro ⟨i, e⟩
    by_cases hi : i = b
    · subst hi; simpa [box, hlive, hface] using hy e
    · simp [hi]
  · intro z hz
    simp only [Fintype.mem_piFinset] at hz ⊢
    intro e
    simpa [box, hlive, hface] using hz (b, e)
  · intro y _; funext e; simp
  · intro z hz
    simp only [Fintype.mem_piFinset] at hz
    funext ⟨i, e⟩
    by_cases hi : i = b
    · subst hi; simp
    · have := hz (i, e)
      simp only [hi, decide_false, Bool.false_eq_true, ↓reduceIte, mem_singleton] at this ⊢
      exact this.symm
  · intro y _
    have hA : ∀ n l, S.args (fun p => if p.1 = b then y p.2 else 0) (b, n) l = B.args y n l :=
      fun n l => by simp [args, hleg, hneg]
    have hE : ∀ e, S.eFac col (fun p => if p.1 = b then y p.2 else 0) (b, e) = B.eFac col y e :=
      fun e => by simp [eFac, hlive, hkap, hface]
    have hN : ∀ n, S.nFac col (fun p => if p.1 = b then y p.2 else 0) (b, n) = B.nFac col y n := by
      intro n
      have hf : (fun l => S.face (S.leg (b, n) l)) = fun l => B.face (B.leg n l) :=
        funext fun l => by rw [hleg, hface]
      have ha : S.args (fun p => if p.1 = b then y p.2 else 0) (b, n) = B.args y n :=
        funext fun l => hA n l
      simp only [nFac, hnLive, htet, hf, ha]
    simp only [qIn, hA]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type,
      Fintype.prod_eq_single b (fun i hi => by simp [hi]),
      Fintype.prod_eq_single b (fun i hi => by simp [hi])]
    simp [hE, hN]

/-- **The remainder of an untouched vertex block is invariant**: the hypothesis `hR` of `ev_glue`
for a node of a block that still is the vertex network `vnet fc tt`. -/
theorem isInv_rem_block (S : SNet F (ι × Fin 10) (ι × Fin 5)) (fc : Fin 10 → F) (tt : Fin 5 → F)
    (col : F → ℕ) (b : ι) (i : Fin 5) (hface : ∀ e, S.face (b, e) = fc e)
    (hkap : ∀ e, S.kap (b, e) = true) (hlive : ∀ e, S.eLive (b, e) = true)
    (htet : ∀ n, S.tet (b, n) = tt n) (hnLive : ∀ n, S.nLive (b, n) = true)
    (hleg : ∀ n l, S.leg (b, n) l = (b, vleg n l)) (hneg : ∀ n l, S.neg (b, n) l = vneg n l) :
    IsInv (fun l => col (S.face (S.leg (b, i) l))) (fun _ => false)
      (S.rem col (fun p => decide (p.1 = b)) (fun q => decide (q.1 = b)) (b, i)) := by
  rw [rem_block S (vnet fc tt) col b i hface hkap hlive htet hnLive hleg hneg]
  have hj : (fun l => col (S.face (S.leg (b, i) l))) =
      fun l => col ((vnet fc tt).face ((vnet fc tt).leg i l)) :=
    funext fun l => by rw [hleg, hface]; rfl
  rw [hj]
  exact isInv_rem_vnet fc tt col i

end Block

/-! ## Chains of steps

Lists of elementary steps with a Boolean check of their hypotheses, so that a whole chain on a
concrete network is justified by one `decide`. -/

section Chain

variable {F E N : Type*} [DecidableEq F] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]

/-- Eliminating the first `k` constraints one by one: a head `(e, e, b)` is dropped, any other
head is eliminated by `subst`. -/
def elimN : ℕ → SNet F E N → SNet F E N
  | 0, S => S
  | k + 1, S => match S.cons with
    | [] => S
    | (e₁, e₂, b) :: rest => if e₁ = e₂ then elimN k S.dropTriv else elimN k (S.subst e₁ e₂ b rest)

/-- The check that `elimN k` keeps the evaluation: a dropped head is `(e, e, false)`, an
eliminated head satisfies the hypotheses of `ev_subst`. -/
def elimOK : ℕ → SNet F E N → Bool
  | 0, _ => true
  | k + 1, S => match S.cons with
    | [] => true
    | (e₁, e₂, b) :: rest =>
      if e₁ = e₂ then !b && elimOK k S.dropTriv
      else S.eLive e₁ && S.eLive e₂ && decide (S.face e₁ = S.face e₂) &&
        rest.all (fun c => decide (c.1 ≠ e₂) && decide (c.2.1 ≠ e₂)) &&
        elimOK k (S.subst e₁ e₂ b rest)

omit [DecidableEq N] in
/-- **Eliminating constraints** by a checked chain keeps the evaluation. -/
theorem ev_elimN (col : F → ℕ) : ∀ (k : ℕ) (S : SNet F E N), elimOK k S = true →
    (elimN k S).ev col = S.ev col
  | 0, S, _ => rfl
  | k + 1, S, h => by
    rcases hc : S.cons with _ | ⟨⟨e₁, e₂, b⟩, rest⟩
    · simp only [elimN, hc]
    · simp only [elimOK, hc] at h
      simp only [elimN, hc]
      by_cases h12 : e₁ = e₂
      · subst h12
        simp only [↓reduceIte, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
        rw [ev_elimN col k _ h.2, ev_dropTriv (h.1 ▸ hc)]
      · simp only [h12, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
        obtain ⟨⟨⟨⟨h1, h2⟩, hf⟩, hr⟩, hk⟩ := h
        rw [ev_elimN col k _ hk, ev_subst hc h12 h1 h2 hf fun c hc' => by
          simpa using hr c hc']

/-- Flipping the nodes of a list in turn. -/
def flipNodes : SNet F E N → List N → SNet F E N
  | S, [] => S
  | S, n :: l => flipNodes (S.flipNode n) l

/-- The check that `flipNodes` keeps the evaluation (the hypotheses of `ev_flipNode`). -/
def flipNodesOK : SNet F E N → List N → Bool
  | _, [] => true
  | S, n :: l => S.nLive n && decide (∀ i, S.eLive (S.leg n i) = true) &&
      decide (Function.Injective (S.leg n)) && flipNodesOK (S.flipNode n) l

omit [DecidableEq F] in
/-- **Flipping a checked list of nodes** keeps the evaluation. -/
theorem ev_flipNodes (col : F → ℕ) : ∀ (S : SNet F E N) (l : List N), flipNodesOK S l = true →
    (flipNodes S l).ev col = S.ev col
  | S, [], _ => rfl
  | S, n :: l, h => by
    simp only [flipNodesOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [flipNodes, ev_flipNodes col _ l h.2, ev_flipNode h.1.1.1 h.1.1.2 h.1.2]

/-- Flipping the variables of a list in turn. -/
def flipVars : SNet F E N → List E → SNet F E N
  | S, [] => S
  | S, e :: l => flipVars (S.flipVar e) l

omit [DecidableEq F] [DecidableEq N] in
/-- **Flipping a list of variables** keeps the evaluation. -/
theorem ev_flipVars (col : F → ℕ) : ∀ (S : SNet F E N) (l : List E), (flipVars S l).ev col = S.ev col
  | S, [] => rfl
  | S, e :: l => by rw [flipVars, ev_flipVars col _ l, ev_flipVar]

/-- Adding the parities of the nodes of a list in turn. -/
def addParities : SNet F E N → List N → SNet F E N
  | S, [] => S
  | S, n :: l => addParities (S.addParity n) l

/-- The check that `addParities` keeps the evaluation: the nodes are live. -/
def addParitiesOK : SNet F E N → List N → Bool
  | _, [] => true
  | S, n :: l => S.nLive n && addParitiesOK (S.addParity n) l

omit [DecidableEq F] in
/-- **Adding the parities of a checked list of nodes** keeps the evaluation. -/
theorem ev_addParities (col : F → ℕ) : ∀ (S : SNet F E N) (l : List N), addParitiesOK S l = true →
    (addParities S l).ev col = S.ev col
  | S, [], _ => rfl
  | S, n :: l, h => by
    simp only [addParitiesOK, Bool.and_eq_true] at h
    rw [addParities, ev_addParities col _ l h.2, ev_addParity h.1]

end Chain

end SNet

end Lightlike.SpinFoam
