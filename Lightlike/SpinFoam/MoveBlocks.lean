import Lightlike.SpinFoam.Move33

/-!
# Checked rewriting steps on unions of vertex networks

The steps of `SNet.lean` (gluing, closing a strand, relabelling) on the union of `m` vertex
networks with bitmask faces `Fin 64`, with their hypotheses bundled as decidable propositions
(`GlueOK`, `LoopOK`, `RelOK`), so that the kernel checks them for a concrete network. These are
the `m`-block versions of the steps used for the 3-3 move (`Move33.lean`); the 2-4 and 1-5 moves
use `m = 4` and `m = 5`.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam

open SNet

namespace MoveBlocks

/-- Edges of a union of `m` vertex networks. -/
abbrev EB (m : ℕ) := Fin m × Fin 10

/-- Nodes of a union of `m` vertex networks. -/
abbrev NB (m : ℕ) := Fin m × Fin 5

set_option linter.unusedSectionVars false

variable {m : ℕ} [NeZero m]

/-- All edges of `EB m`, as a list. -/
def allEB (m : ℕ) : List (EB m) := (List.finRange m).flatMap fun a => (List.finRange 10).map fun b => (a, b)

/-- All nodes of `NB m`, as a list. -/
def allNB (m : ℕ) : List (NB m) := (List.finRange m).flatMap fun a => (List.finRange 5).map fun b => (a, b)

lemma mem_allEB {m : ℕ} (e : EB m) : e ∈ allEB m := by
  obtain ⟨a, b⟩ := e
  simp [allEB]

lemma mem_allNB {m : ℕ} (n : NB m) : n ∈ allNB m := by
  obtain ⟨a, b⟩ := n
  simp [allNB]

/-- Deciding a statement for all edges through `allEB m`. -/
local instance (priority := high) decForallEB (P : (EB m) → Prop) [DecidablePred P] :
    Decidable (∀ e, P e) :=
  decidable_of_iff ((allEB m).all fun e => decide (P e)) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h e => h e (mem_allEB e), fun h e _ => h e⟩)

/-- Deciding a statement for all nodes through `allNB m`. -/
local instance (priority := high) decForallNB (P : (NB m) → Prop) [DecidablePred P] :
    Decidable (∀ n, P n) :=
  decidable_of_iff ((allNB m).all fun n => decide (P n)) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h n => h n (mem_allNB n), fun h n _ => h n⟩)

/-- The hypotheses of `ev_glue` for gluing the node `n₁` of an untouched block `b` (still the
vertex network of `Fin 6 ∖ {v}`) to the node `n₂` along the tetrahedron `t`. -/
abbrev GlueOK (S : SNet (Fin 64) (EB m) (NB m)) (b : Fin m) (v : Fin 6) (n₁ n₂ : (NB m)) (t : Fin 64) :
    Prop :=
  n₁.1 = b ∧ n₂.1 ≠ b ∧ (∀ e, S.face (b, e) = fcB v e) ∧ (∀ e, S.kap (b, e) = true) ∧
  (∀ e, S.eLive (b, e) = true) ∧ (∀ n, S.tet (b, n) = ttB v n) ∧ (∀ n, S.nLive (b, n) = true) ∧
  (∀ n l, S.leg (b, n) l = (b, vleg n l)) ∧ (∀ n l, S.neg (b, n) l = vneg n l) ∧
  (∀ n, S.nLive n = true → ∀ l, ((S.leg n l).1 = b ↔ n.1 = b)) ∧
  (∀ c ∈ S.cons, c.1.1 ≠ b ∧ c.2.1.1 ≠ b) ∧
  (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧ S.nLive n₂ = true ∧
  S.tet n₁ = t ∧ S.tet n₂ = t ∧ (∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l)) ∧
  (∀ e, S.eLive e = true → S.face e ≠ t) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t) ∧ t ∉ S.cst

set_option synthInstance.maxSize 2048 in
/-- `GlueOK` is decidable. -/
instance (S : SNet (Fin 64) (EB m) (NB m)) (b : Fin m) (v : Fin 6) (n₁ n₂ : (NB m)) (t : Fin 64) :
    Decidable (GlueOK S b v n₁ n₂ t) := by
  unfold GlueOK; infer_instance

/-- **Gluing through an untouched block**, with the hypotheses checked as `GlueOK`. -/
theorem ev_glue_of {S : SNet (Fin 64) (EB m) (NB m)} {b : Fin m} {v : Fin 6} {n₁ n₂ : (NB m)} {t : Fin 64}
    (h : GlueOK S b v n₁ n₂ t) (col : Fin 64 → ℕ) (cut : ℕ)
    (hcut : ∑ l, col (S.face (S.leg n₁ l)) ≤ cut) :
    ∑ k ∈ range (cut + 1), S.ev (Function.update col t k) = (S.glue n₁ n₂).ev col := by
  obtain ⟨hb1, hb2, hface, hkap, hlive, htet, hnLive, hleg, hneg, hblk, hcons, hlegs, hn2, ht1,
    ht2, hf, hte, htn, htc⟩ := h
  obtain ⟨b', i⟩ := n₁
  dsimp only at hb1
  subst hb1
  rw [Fin.sum_univ_four] at hcut
  have htc' : t ∉ S.cst := htc
  have hb1' : (fun q : (NB m) => decide (q.1 = b')) (b', i) = true := by simp
  have hb2' : (fun q : (NB m) => decide (q.1 = b')) n₂ = false := by simpa using hb2
  have hc : ∀ c ∈ S.cons, (fun p : (EB m) => decide (p.1 = b')) c.1 = false ∧
      (fun p : (EB m) => decide (p.1 = b')) c.2.1 = false :=
    fun c hc => ⟨decide_eq_false (hcons c hc).1, decide_eq_false (hcons c hc).2⟩
  have hbl : ∀ n, S.nLive n = true → ∀ l,
      (fun p : (EB m) => decide (p.1 = b')) (S.leg n l) = (fun q : (NB m) => decide (q.1 = b')) n :=
    fun n hn l => decide_eq_decide.mpr (hblk n hn l)
  exact ev_glue (S := S) (col := col) (n₁ := (b', i)) (n₂ := n₂) (t := t)
    (fun p => decide (p.1 = b')) (fun q => decide (q.1 = b')) cut hb1' hb2' hbl hc hlegs
    (hnLive i) hn2 ht1 ht2 hf hte htn htc' (by omega)
    (isInv_rem_block S (fcB v) (ttB v) col b' i hface hkap hlive htet hnLive hleg hneg)

/-- The hypotheses of `ev_loop` for closing the strand of leg `lA` between `n₁` and `n₂`, with
tetrahedron `t` and strand face `fA`. -/
abbrev LoopOK (S : SNet (Fin 64) (EB m) (NB m)) (n₁ n₂ : (NB m)) (lA : Fin 4) (t fA : Fin 64) : Prop :=
  n₁ ≠ n₂ ∧ (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧
  S.nLive n₁ = true ∧ S.nLive n₂ = true ∧ S.tet n₁ = t ∧ S.tet n₂ = t ∧
  (∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l)) ∧ S.leg n₂ lA = S.leg n₁ lA ∧
  S.face (S.leg n₁ lA) = fA ∧ S.neg n₂ lA = S.neg n₁ lA ∧ S.kap (S.leg n₁ lA) = false ∧
  (∀ l, l ≠ lA → S.leg n₁ l ≠ S.leg n₁ lA ∧ S.leg n₂ l ≠ S.leg n₁ lA) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → ∀ l, S.leg n l ≠ S.leg n₁ lA) ∧
  (∀ c ∈ S.cons, c.1 ≠ S.leg n₁ lA ∧ c.2.1 ≠ S.leg n₁ lA) ∧ fA ≠ t ∧
  (∀ e, S.eLive e = true → e ≠ S.leg n₁ lA → S.face e ≠ t ∧ S.face e ≠ fA) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t ∧ S.tet n ≠ fA) ∧
  t ∉ S.cst ∧ S.cst.count fA % 2 = 0

set_option synthInstance.maxSize 2048 in
/-- `LoopOK` is decidable. -/
instance (S : SNet (Fin 64) (EB m) (NB m)) (n₁ n₂ : (NB m)) (lA : Fin 4) (t fA : Fin 64) :
    Decidable (LoopOK S n₁ n₂ lA t fA) := by
  unfold LoopOK; infer_instance

/-- **Closing a strand**, with the hypotheses checked as `LoopOK`. -/
theorem ev_loop_of {S : SNet (Fin 64) (EB m) (NB m)} {n₁ n₂ : (NB m)} {lA : Fin 4} {t fA : Fin 64}
    (h : LoopOK S n₁ n₂ lA t fA) (col : Fin 64 → ℕ) (cutA cut : ℕ)
    (hA : ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cutA)
    (hk : cutA + ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cut) :
    ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k ∈ range (cut + 1),
      S.ev (Function.update (Function.update col fA jA) t k) = (S.loop n₁ n₂ lA).ev col := by
  obtain ⟨h12, hlegs, hn1, hn2, ht1, ht2, hf, he2, hfA, hneg, hkap, hlA, hAo, hAc, hAt, hte, htn,
    htc, hcA⟩ := h
  have htc' : t ∉ S.cst := htc
  have hcA' : Even (S.cst.count fA) := Nat.even_iff.mpr hcA
  exact ev_loop (S := S) (col := col) (n₁ := n₁) (n₂ := n₂) (t := t) (fA := fA) lA cutA cut h12
    hlegs hn1 hn2 ht1 ht2 hf rfl he2 hfA hneg hkap hlA hAo hAc hAt hte htn htc' hcA' hA hk

/-- The first live edge of `S` on the face `f` (junk `(0, 0)` if there is none). -/
def findE (S : SNet (Fin 64) (EB m) (NB m)) (f : Fin 64) : (EB m) :=
  ((allEB m).find? fun e => S.eLive e && decide (S.face e = f)).getD (0, 0)

/-- The first live node of `S` on the tetrahedron `t` (junk `(0, 0)` if there is none). -/
def findN (S : SNet (Fin 64) (EB m) (NB m)) (t : Fin 64) : (NB m) :=
  ((allNB m).find? fun n => S.nLive n && decide (S.tet n = t)).getD (0, 0)

/-- The edge of `S'` on the face of the edge `e` of `S` (the two networks may have different
numbers of blocks). -/
def relE {m' : ℕ} [NeZero m'] (S : SNet (Fin 64) (EB m) (NB m)) (S' : SNet (Fin 64) (EB m') (NB m'))
    (e : EB m) : EB m' := findE S' (S.face e)

/-- The node of `S'` on the tetrahedron of the node `n` of `S`. -/
def relN {m' : ℕ} [NeZero m'] (S : SNet (Fin 64) (EB m) (NB m)) (S' : SNet (Fin 64) (EB m') (NB m'))
    (n : NB m) : NB m' := findN S' (S.tet n)

/-- The hypotheses of `ev_relabel` for the relabelling of `S` and `S'` by faces and
tetrahedra. -/
abbrev RelOK {m' : ℕ} [NeZero m'] (S : SNet (Fin 64) (EB m) (NB m))
    (S' : SNet (Fin 64) (EB m') (NB m')) : Prop :=
  (∀ e, S.eLive e = true → S'.eLive (relE S S' e) = true ∧ relE S' S (relE S S' e) = e) ∧
  (∀ e', S'.eLive e' = true → S.eLive (relE S' S e') = true ∧ relE S S' (relE S' S e') = e') ∧
  (∀ n, S.nLive n = true → S'.nLive (relN S S' n) = true ∧ relN S' S (relN S S' n) = n) ∧
  (∀ n', S'.nLive n' = true → S.nLive (relN S' S n') = true ∧ relN S S' (relN S' S n') = n') ∧
  (∀ e, S.eLive e = true → S'.face (relE S S' e) = S.face e ∧ S'.kap (relE S S' e) = S.kap e) ∧
  (∀ n, S.nLive n = true → S'.tet (relN S S' n) = S.tet n ∧
    ∀ l, S'.leg (relN S S' n) l = relE S S' (S.leg n l) ∧ S'.neg (relN S S' n) l = S.neg n l) ∧
  (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧ S.cons = [] ∧ S'.cons = [] ∧
  (∀ f ∈ S.cst ++ S'.cst, S.cst.count f % 2 = S'.cst.count f % 2)

set_option synthInstance.maxSize 2048 in
/-- `RelOK` is decidable. -/
instance {m' : ℕ} [NeZero m'] (S : SNet (Fin 64) (EB m) (NB m)) (S' : SNet (Fin 64) (EB m') (NB m')) :
    Decidable (RelOK S S') := by
  unfold RelOK; infer_instance

/-- **Relabelling by faces**, with the hypotheses checked as `RelOK`. -/
theorem ev_rel_of {m' : ℕ} [NeZero m'] {S : SNet (Fin 64) (EB m) (NB m)}
    {S' : SNet (Fin 64) (EB m') (NB m')} (h : RelOK S S') (col : Fin 64 → ℕ) :
    S.ev col = S'.ev col := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ev_relabel S' (relE S S') (relE S' S) (relN S S') (relN S' S) h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10

/-! ### A free closed strand -/

lemma card_pbox (j : ℕ) : #(pbox j) = j + 1 := by
  have : pbox j = (range (j + 1)).image (fun k : ℕ => (j : ℤ) - 2 * k) := by
    ext μ
    simp only [pbox, mem_filter, mem_Icc, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨((j - μ) / 2).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [this, card_image_of_injective, card_range]
  intro a b h
  simp only at h
  omega

section Free

variable {F E N : Type*} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]

/-- The network with the edge `e` dead. -/
def _root_.Lightlike.SpinFoam.SNet.killE (S : SNet F E N) (e : E) : SNet F E N :=
  { S with eLive := Function.update S.eLive e false }

lemma summand_congr_off (S : SNet F E N) (col : F → ℕ) (e : E) (he : S.kap e = false)
    (hn : ∀ n, S.nLive n = true → ∀ l, S.leg n l ≠ e)
    (hc : ∀ c ∈ S.cons, c.1 ≠ e ∧ c.2.1 ≠ e) {x x' : E → ℤ} (hx : ∀ e', e' ≠ e → x e' = x' e') :
    S.summand col x = S.summand col x' := by
  unfold SNet.summand
  congr 1
  congr 1
  · refine prod_congr rfl fun e' _ => ?_
    by_cases h : e' = e
    · subst h
      simp [SNet.eFac, he]
    · simp only [SNet.eFac, hx e' h]
  · refine prod_congr rfl fun n _ => ?_
    simp only [SNet.nFac]
    split_ifs with hl
    · have : S.args x n = S.args x' n := funext fun l => by
        simp only [SNet.args, hx _ (hn n hl l)]
      rw [this]
    · rfl
  · congr 1
    refine List.map_congr_left fun c hcm => ?_
    simp only [SNet.cFac, hx _ (hc c hcm).1, hx _ (hc c hcm).2]

/-- **A free closed strand contributes its dimension**: a live edge with trivial sign, on no leg
of a live node and in no constraint, multiplies the evaluation by `col face + 1`. -/
theorem ev_killE (S : SNet F E N) (col : F → ℕ) (e : E) (hl : S.eLive e = true)
    (he : S.kap e = false) (hn : ∀ n, S.nLive n = true → ∀ l, S.leg n l ≠ e)
    (hc : ∀ c ∈ S.cons, c.1 ≠ e ∧ c.2.1 ≠ e) :
    S.ev col = ((col (S.face e) : ℝ) + 1) * (S.killE e).ev col := by
  have hsum : ∀ x, (S.killE e).summand col x = S.summand col x := by
    intro x
    unfold SNet.summand
    congr 1
    congr 1
    · refine prod_congr rfl fun e' _ => ?_
      by_cases h : e' = e
      · subst h
        simp [SNet.eFac, he, SNet.killE]
      · simp [SNet.eFac, SNet.killE, Function.update_of_ne h]
  have hbox : (S.killE e).box col = fun i => if i = e then {0} else S.box col i := by
    funext i
    by_cases h : i = e
    · subst h; simp [SNet.box, SNet.killE]
    · simp [SNet.box, SNet.killE, h]
  unfold SNet.ev
  have hcst : (S.killE e).cst = S.cst := rfl
  rw [hcst, mul_left_comm]
  congr 1
  rw [sum_pi_split (S.box col) (fun i => i = e), hbox]
  simp only [hsum]
  have h1 : ∀ y z : E → ℤ, S.summand col (fun i => if i = e then z i else y i) =
      S.summand col y := fun y z =>
    summand_congr_off S col e he hn hc fun e' h => by simp [h]
  simp only [h1]
  have hcard : #(Fintype.piFinset fun i => if i = e then S.box col i else ({0} : Finset ℤ)) =
      col (S.face e) + 1 := by
    rw [Fintype.card_piFinset, prod_eq_single e]
    · simp [SNet.box, hl, card_pbox]
    · intro b _ hb
      simp [hb]
    · simp
  simp only [sum_const, hcard, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_sum]

end Free

end MoveBlocks

end Lightlike.SpinFoam
