import Lightlike.FieldTheory.Gaussian.FeynmanExpansion

/-!
# Wick contractions as fixed-point-free involutions, with edge weights (toward Polyak's Proposition 2.17)

A full Wick contraction of `n` positions is a fixed-point-free involution `f` of `Fin n` (Physlib's
`isFullInvolutionEquiv`), and its weight is the product over the edges `s(i, f i)` (`edges`) of `S_{x_i x_{f i}}`
(`edgeWeight`, for a symmetric `S`):
* `pairWeight_eq_prod_edges`: `pairWeight S x c = ∏_{e ∈ edges f_c} edgeWeight S x e`;
* `pairSum_eq_sum_involutions`: `pairSum S x = Σ_{f fixed-point free involution} ∏_{e ∈ edges f} edgeWeight S x e`.

This is the step from the labelled contractions of `integral_homogPoly_pow` to graphs: the pairings of the legs
`Fin m × Fin d` of `m` vertices, on which the vertex-preserving permutations act.
-/

namespace Lightlike.FieldTheory

open Finset WickContraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of an unordered pair of positions with labels `x`: `S_{x_p x_q}`, for symmetric `S`. -/
def edgeWeight (S : Matrix ι ι ℝ) (hS : S.IsSymm) {α : Type*} (x : α → ι) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun p q => S (x p) (x q), fun p q => (hS.apply (x p) (x q)).symm⟩

@[simp] lemma edgeWeight_mk (S : Matrix ι ι ℝ) (hS : S.IsSymm) {α : Type*} (x : α → ι) (p q : α) :
    edgeWeight S hS x s(p, q) = S (x p) (x q) := rfl

/-- The edges `s(i, f i)` of a map `f` (an involution: the pairs of a pairing). -/
def edges {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) : Finset (Sym2 α) :=
  univ.image fun i => s(i, f i)

lemma mem_edges {α : Type*} [Fintype α] [DecidableEq α] {f : α → α} {e : Sym2 α} :
    e ∈ edges f ↔ ∃ i, s(i, f i) = e := by
  simp [edges]

/-- For a full contraction, the involution sends the first position of a pair to the second. -/
lemma toInvolution_fst {n : ℕ} (c : WickContraction n) (a : c.1) :
    (c.toInvolution).1 (c.fstFieldOfContract a) = c.sndFieldOfContract a := by
  simp [toInvolution, fstFieldOfContract_getDual?]

lemma toInvolution_snd {n : ℕ} (c : WickContraction n) (a : c.1) :
    (c.toInvolution).1 (c.sndFieldOfContract a) = c.fstFieldOfContract a := by
  simp [toInvolution, sndFieldOfContract_getDual?]

/-- **The weight of a full contraction is a product over the edges of its involution.** -/
lemma pairWeight_eq_prod_edges (S : Matrix ι ι ℝ) (hS : S.IsSymm) {n : ℕ} (x : Fin n → ι)
    {c : WickContraction n} (hc : c.IsFull) :
    pairWeight S x c = ∏ e ∈ edges (c.toInvolution).1, edgeWeight S hS x e := by
  set f := (c.toInvolution).1 with hf
  -- the edges are the images of the pairs
  have himage : edges f = univ.image fun a : c.1 => s(c.fstFieldOfContract a, c.sndFieldOfContract a) := by
    ext e
    rw [mem_edges, mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (c.getDual?_isSome_iff i).1 (isSome_getDual_of_isFull hc i)
      have hai : a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} :=
        c.finset_eq_fstFieldOfContract_sndFieldOfContract a
      rw [hai, mem_insert, mem_singleton] at ha
      refine ⟨a, mem_univ _, ?_⟩
      rcases ha with h | h
      · rw [h, hf, toInvolution_fst]
      · rw [h, hf, toInvolution_snd, Sym2.eq_swap]
    · rintro ⟨a, -, rfl⟩
      exact ⟨c.fstFieldOfContract a, by rw [hf, toInvolution_fst]⟩
  have hinj : Set.InjOn (fun a : c.1 => s(c.fstFieldOfContract a, c.sndFieldOfContract a)) (univ : Finset c.1) := by
    intro a _ b _ hab
    simp only at hab
    apply Subtype.ext
    rw [c.finset_eq_fstFieldOfContract_sndFieldOfContract a, c.finset_eq_fstFieldOfContract_sndFieldOfContract b]
    rcases Sym2.eq_iff.1 hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Finset.pair_comm]
  rw [himage, prod_image hinj]
  rfl

/-- **The pairing sum as a sum over fixed-point-free involutions**, with the edge weights. -/
theorem pairSum_eq_sum_involutions (S : Matrix ι ι ℝ) (hS : S.IsSymm) {n : ℕ} (x : Fin n → ι) :
    pairSum S x = ∑ f : {f : Fin n → Fin n // Function.Involutive f ∧ ∀ i, f i ≠ i},
      ∏ e ∈ edges f.1, edgeWeight S hS x e := by
  rw [pairSum]
  refine Fintype.sum_equiv isFullInvolutionEquiv _ _ fun c => ?_
  rw [pairWeight_eq_prod_edges S hS x c.2]
  rfl


/-- Conjugating a map by an equivalence carries its edges along. -/
lemma prod_edges_conj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Matrix ι ι ℝ) (hS : S.IsSymm) (e : α ≃ β) (f : α → α) (x : β → ι) :
    ∏ s ∈ edges (e ∘ f ∘ e.symm), edgeWeight S hS x s = ∏ s ∈ edges f, edgeWeight S hS (x ∘ e) s := by
  have himage : edges (e ∘ f ∘ e.symm) = (edges f).image (Sym2.map e) := by
    ext s
    simp only [edges, mem_image, mem_univ, true_and, Function.comp_apply, exists_exists_eq_and, Sym2.map_mk]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    · rintro ⟨j, rfl⟩; exact ⟨e j, by simp⟩
  rw [himage, prod_image (Sym2.map.injective e.injective).injOn]
  refine prod_congr rfl fun s _ => ?_
  induction s using Sym2.ind
  rfl

/-- Fixed-point-free involutions along an equivalence. -/
def pairingCongr {α β : Type*} (e : α ≃ β) :
    {f : α → α // Function.Involutive f ∧ ∀ i, f i ≠ i} ≃ {g : β → β // Function.Involutive g ∧ ∀ i, g i ≠ i} :=
  (Equiv.arrowCongr e e).subtypeEquiv fun f => by
    simp only [Equiv.arrowCongr_apply, Function.comp_def]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => by simp [h1 _], fun i hi => h2 (e.symm i) ?_⟩
      simpa using congrArg e.symm hi
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, fun h hh => h2 (e h) (by simp [hh])⟩
      simpa using h1 (e h)

/-- The pairings of the `m d` legs `Fin m × Fin d` of `m` vertices of degree `d`. -/
abbrev LegPairing (m d : ℕ) : Type :=
  {f : Fin m × Fin d → Fin m × Fin d // Function.Involutive f ∧ ∀ h, f h ≠ h}

noncomputable instance {m d : ℕ} : Fintype (LegPairing m d) := Fintype.ofFinite _

/-- The labels of the legs: `ℓ_i (v, a) = i v a`. -/
def legLab {m d : ℕ} (i : Fin m → Fin d → ι) (h : Fin m × Fin d) : ι := i h.1 h.2

/-- **The pairing sum on the legs**: for the leg labels of a vertex labelling `i`,
`pairSum S (legLabels i) = Σ_{f pairing of the legs} ∏_{e ∈ edges f} edgeWeight S ℓ_i e`. -/
theorem pairSum_legLabels (S : Matrix ι ι ℝ) (hS : S.IsSymm) {m d : ℕ} (i : Fin m → Fin d → ι) :
    pairSum S (legLabels i) = ∑ f : LegPairing m d, ∏ e ∈ edges f.1, edgeWeight S hS (legLab i) e := by
  classical
  rw [pairSum_eq_sum_involutions S hS]
  refine (Fintype.sum_equiv (pairingCongr finProdFinEquiv).symm _ _ fun f => ?_)
  have hf : f.1 = finProdFinEquiv ∘ ((pairingCongr finProdFinEquiv).symm f).1 ∘ finProdFinEquiv.symm := by
    funext k
    show f.1 k = finProdFinEquiv (finProdFinEquiv.symm (f.1 (finProdFinEquiv (finProdFinEquiv.symm k))))
    simp only [Equiv.apply_symm_apply]
  have hl : legLabels i ∘ finProdFinEquiv = legLab i := by
    funext h; simp [legLabels, legLab]
  rw [hf, prod_edges_conj, hl]


section Graphs

open MulAction

variable {m d : ℕ}

/-- The leg permutations that map vertices to vertices (the wreath product `S_d ≀ S_m`). -/
def legPerm (m d : ℕ) : Subgroup (Equiv.Perm (Fin m × Fin d)) where
  carrier := {σ | ∃ π : Equiv.Perm (Fin m), ∀ v a, (σ (v, a)).1 = π v}
  one_mem' := ⟨1, fun _ _ => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨π, hπ⟩ ⟨ρ, hρ⟩
    refine ⟨π * ρ, fun v a => ?_⟩
    show (σ (τ (v, a))).1 = π (ρ v)
    rw [← hρ v a]
    exact hπ _ _
  inv_mem' := by
    rintro σ ⟨π, hπ⟩
    refine ⟨π⁻¹, fun v a => ?_⟩
    have h := hπ (σ⁻¹ (v, a)).1 (σ⁻¹ (v, a)).2
    rw [Prod.mk.eta, show σ (σ⁻¹ (v, a)) = (v, a) from σ.apply_symm_apply (v, a)] at h
    rw [Equiv.Perm.eq_inv_iff_eq]
    exact h.symm

/-- The vertex-preserving permutations act on the pairings of the legs by conjugation. -/
instance : MulAction (legPerm m d) (LegPairing m d) where
  smul g f := ⟨g.1 ∘ f.1 ∘ g.1.symm, fun h => by
      simp only [Function.comp_apply, Equiv.symm_apply_apply, f.2.1 (g.1.symm h), Equiv.apply_symm_apply],
    fun h hh => by
      apply f.2.2 (g.1.symm h)
      have := congrArg g.1.symm hh
      simpa using this⟩
  one_smul _ := by apply Subtype.ext; rfl
  mul_smul _ _ _ := by apply Subtype.ext; rfl

lemma legPerm_fst (g : legPerm m d) (v : Fin m) (a : Fin d) :
    (g.1 (v, a)).1 = (Classical.choose g.2) v :=
  Classical.choose_spec g.2 v a

/-- The permutation of the legs at `v` made by `g`. -/
noncomputable def legPermAt (g : legPerm m d) (v : Fin m) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (fun a => (g.1 (v, a)).2) (Finite.injective_iff_bijective.1 fun a b hab => by
    have : g.1 (v, a) = g.1 (v, b) := Prod.ext ((legPerm_fst g v a).trans (legPerm_fst g v b).symm) hab
    simpa using g.1.injective this)

/-- `|S_d ≀ S_m| = (d!)^m m!` for `d > 0`. -/
noncomputable def legPermEquiv (hd : 0 < d) :
    legPerm m d ≃ Equiv.Perm (Fin m) × (Fin m → Equiv.Perm (Fin d)) where
  toFun g := (Classical.choose g.2, legPermAt g)
  invFun p := ⟨Equiv.prodShear p.1 p.2, p.1, fun _ _ => rfl⟩
  left_inv g := by
    apply Subtype.ext
    refine Equiv.ext fun ⟨v, a⟩ => Prod.ext ?_ rfl
    exact (legPerm_fst g v a).symm
  right_inv p := by
    have hπ : Classical.choose (⟨p.1, fun _ _ => rfl⟩ :
        ∃ π : Equiv.Perm (Fin m), ∀ v a, (Equiv.prodShear p.1 p.2 (v, a)).1 = π v) = p.1 := by
      refine Equiv.ext fun v => ?_
      exact ((Classical.choose_spec (⟨p.1, fun _ _ => rfl⟩ :
        ∃ π : Equiv.Perm (Fin m), ∀ v a, (Equiv.prodShear p.1 p.2 (v, a)).1 = π v)) v ⟨0, hd⟩).symm
    exact Prod.ext hπ (funext fun v => Equiv.ext fun a => rfl)

lemma card_legPerm (hd : 0 < d) : Nat.card (legPerm m d) = d.factorial ^ m * m.factorial := by
  rw [Nat.card_congr (legPermEquiv hd), Nat.card_prod, Nat.card_fun, Nat.card_perm, Nat.card_perm]
  simp [mul_comm]

/-- **The class formula with weights**: for a `G`-invariant `F`, `Σ_x F x = Σ_{ω ∈ X/G} (|G|/|G_ω|) F(ω)`. -/
theorem sum_eq_sum_orbits {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    [Fintype (Quotient (orbitRel G X))] (F : X → ℝ) (hF : ∀ (g : G) x, F (g • x) = F x) :
    ∑ x, F x = ∑ ω : Quotient (orbitRel G X),
      ((Nat.card G : ℝ) / Nat.card (stabilizer G ω.out)) * F ω.out := by
  classical
  rw [← Finset.sum_fiberwise univ (fun x => (Quotient.mk (orbitRel G X) x)) F]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have horb : ∀ x, Quotient.mk (orbitRel G X) x = ω ↔ x ∈ orbit G ω.out := fun x => by
    rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel G X), Quotient.out_eq]
  have hfib : ∀ x ∈ univ.filter (fun x => Quotient.mk (orbitRel G X) x = ω), F x = F ω.out := by
    intro x hx
    rw [mem_filter, horb] at hx
    obtain ⟨g, rfl⟩ := hx.2
    exact hF g ω.out
  rw [Finset.sum_congr rfl hfib, sum_const, nsmul_eq_mul]
  congr 1
  have hcard : (univ.filter (fun x => Quotient.mk (orbitRel G X) x = ω)).card =
      Nat.card (orbit G ω.out) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [mem_filter]; simp [horb])
  have hos : Nat.card (stabilizer G ω.out) * Nat.card (orbit G ω.out) = Nat.card G := by
    rw [Nat.card_coe_set_eq, ← index_stabilizer]; exact Subgroup.card_mul_index _
  have hpos : (0 : ℝ) < Nat.card (stabilizer G ω.out) := by exact_mod_cast Nat.card_pos
  rw [hcard, eq_div_iff hpos.ne']
  exact_mod_cast (mul_comm _ _).trans hos

/-- **The weight of a Feynman graph** (a pairing `f` of the legs), summed over the labels:
`W(f) = Σ_i (∏_v c_{i_v}) ∏_{e ∈ edges f} S_e`. -/
def graphWeight (S : Matrix ι ι ℝ) (hS : S.IsSymm) (c : (Fin d → ι) → ℝ) (f : LegPairing m d) : ℝ :=
  ∑ i : Fin m → Fin d → ι, (∏ v, c (i v)) * ∏ e ∈ edges f.1, edgeWeight S hS (legLab i) e

/-- Relabelling the vertex labels by a leg permutation. -/
def relabel (g : legPerm m d) : (Fin m → Fin d → ι) ≃ (Fin m → Fin d → ι) where
  toFun i v a := i (g.1 (v, a)).1 (g.1 (v, a)).2
  invFun i v a := i (g.1.symm (v, a)).1 (g.1.symm (v, a)).2
  left_inv i := by funext v a; simp
  right_inv i := by funext v a; simp

/-- **The graph weight is invariant** under the vertex-preserving permutations, for a symmetric tensor `c`. -/
theorem graphWeight_smul (S : Matrix ι ι ℝ) (hS : S.IsSymm) {c : (Fin d → ι) → ℝ}
    (hc : ∀ (j : Fin d → ι) (τ : Equiv.Perm (Fin d)), c (j ∘ τ) = c j) (g : legPerm m d) (f : LegPairing m d) :
    graphWeight S hS c (g • f) = graphWeight S hS c f := by
  unfold graphWeight
  have hedge : ∀ i : Fin m → Fin d → ι, ∏ e ∈ edges (g • f).1, edgeWeight S hS (legLab i) e =
      ∏ e ∈ edges f.1, edgeWeight S hS (legLab (relabel g i)) e := fun i => by
    rw [show (g • f).1 = g.1 ∘ f.1 ∘ g.1.symm from rfl, prod_edges_conj]
    rfl
  have hcoef : ∀ i : Fin m → Fin d → ι, ∏ v, c (relabel g i v) = ∏ v, c (i v) := fun i => by
    have h1 : ∀ v, relabel g i v = i ((Classical.choose g.2) v) ∘ legPermAt g v := fun v => by
      funext a
      show i (g.1 (v, a)).1 (g.1 (v, a)).2 = i ((Classical.choose g.2) v) ((g.1 (v, a)).2)
      rw [legPerm_fst]
    simp_rw [h1, hc]
    exact Equiv.prod_comp (Classical.choose g.2) (fun v => c (i v))
  simp_rw [hedge]
  refine (Fintype.sum_equiv (relabel g) _ _ fun i => ?_)
  rw [hcoef]

/-- **The Feynman graph expansion** (Polyak, Proposition 2.17, eq. (19), p. 9, for a homogeneous potential):
for a symmetric coefficient tensor `c` and `V = Σ_i c_i x_{i 0} ⋯ x_{i (d-1)}`,
`E_S[(V/d!)^m]/m! = Σ_Γ W(Γ)/|Aut Γ|`, the sum over the Feynman graphs (orbits of pairings of the `md` legs under
`S_d ≀ S_m`) with `m` vertices of degree `d`. -/
theorem integral_homogPoly_pow_graphs {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hSym : S.IsSymm) (hd : 0 < d)
    {c : (Fin d → ι) → ℝ} (hc : ∀ (j : Fin d → ι) (τ : Equiv.Perm (Fin d)), c (j ∘ τ) = c j) (m : ℕ)
    [Fintype (Quotient (orbitRel (legPerm m d) (LegPairing m d)))] :
    (∫ x, (homogPoly c x / d.factorial) ^ m ∂(ProbabilityTheory.multivariateGaussian 0 S)) / m.factorial =
      ∑ Γ : Quotient (orbitRel (legPerm m d) (LegPairing m d)),
        graphWeight S hSym c Γ.out / Nat.card (stabilizer (legPerm m d) Γ.out) := by
  classical
  have h1 : ∫ x, (homogPoly c x / d.factorial) ^ m ∂(ProbabilityTheory.multivariateGaussian 0 S) =
      (∑ f : LegPairing m d, graphWeight S hSym c f) / (d.factorial : ℝ) ^ m := by
    simp_rw [div_pow]
    rw [MeasureTheory.integral_div, integral_homogPoly_pow hS]
    congr 1
    simp_rw [pairSum_legLabels S hSym, Finset.mul_sum]
    rw [Finset.sum_comm]
    first | rfl | simp only [graphWeight]
  rw [h1, sum_eq_sum_orbits _ (graphWeight_smul S hSym hc), card_legPerm hd]
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun Γ _ => ?_
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end Graphs

end Lightlike.FieldTheory
