import Lightlike.SpinFoam.ForcingMoves

/-!
# Forcing under the 3-3 move: the finite local lemma

The six vertices of a 3-3 move are `s_0, s_1, s_2` (the triangle `σ` that the move removes) and
`c_0, c_1, c_2` (the triangle `τ` it creates). Of the twenty triangles on them, `σ` and `τ` change;
the other eighteen are *mixed*: `m c p` is `{s_i, s_j, c}` with `{i, j} = {0,1,2} ∖ {p}` and `n x q` is
`{c_k, c_l, x}` with `{k, l} = {0,1,2} ∖ {q}`. The nine tetrahedra `{s_i, s_j, c_k, c_l}` lie in the
complex before and after the move. They are the *common* tetrahedra; the tetrahedron `{s_i, s_j, c_k,
c_l}` for `p, q` has the four triangles `m k p`, `m l p`, `n i q`, `n j q`.

Here the mixed triangles are Boolean variables (`true`: the triangle is in the set), and the lemma
is the finite statement behind the characterization of when forcing survives the 3-3 move: a set
that is closed under the nine common tetrahedra and contains a full row of `m` (all three `m c p`
for one `c`: the three triangles of the tetrahedron `σ ∪ {c}` other than `σ`) and a full row of `n`
has no row of `m` or of `n` with exactly two triangles, so adding `σ` (or `τ`) to it creates no
further forcing in the tetrahedra `σ ∪ {c}` (or `τ ∪ {x}`).
-/

namespace Lightlike.SpinFoam.Forcing33

/-- A tetrahedron with the four triangles `a b c d` (`true`: in the set) forces nothing when it is
not the case that exactly one of them is missing. -/
def ok4 (a b c d : Bool) : Bool := decide (a.toNat + b.toNat + c.toNat + d.toNat ≠ 3)

/-- A row of three triangles has exactly two in the set: then the tetrahedron containing `σ` (or
`τ`) forces the third as soon as `σ` (or `τ`) is in the set. -/
def ne2 (a b c : Bool) : Bool := decide (a.toNat + b.toNat + c.toNat ≠ 2)

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **The finite local lemma of the 3-3 move.** If the eighteen mixed triangles form a set that is
closed under the nine common tetrahedra (`ok4` for each), contains a full row of `m` and a full row
of `n`, then no row of `m` and no row of `n` has exactly two triangles in the set (`ne2`). The
variables are Booleans, with the constraint of each tetrahedron placed as early as possible; the
kernel checks it by `decide`. -/
theorem local33_prop :
    ∀ m00 : Bool, ∀ m10 : Bool, ∀ m20 : Bool, ∀ m01 : Bool, ∀ m11 : Bool, ∀ m21 : Bool, ∀ m02 : Bool, ∀ m12 : Bool, ∀ m22 : Bool, ∀ n00 : Bool, ∀ n10 : Bool, ok4 m12 m22 n00 n10 = true → ∀ n20 : Bool, ok4 m10 m20 n10 n20 = true → ok4 m11 m21 n00 n20 = true → ∀ n01 : Bool, ∀ n11 : Bool, ok4 m02 m22 n01 n11 = true → ∀ n21 : Bool, ok4 m00 m20 n11 n21 = true → ok4 m01 m21 n01 n21 = true → ∀ n02 : Bool, ∀ n12 : Bool, ok4 m02 m12 n02 n12 = true → ∀ n22 : Bool, ok4 m00 m10 n12 n22 = true → ok4 m01 m11 n02 n22 = true → ((m00 && m01 && m02) || (m10 && m11 && m12) || (m20 && m21 && m22)) = true → ((n00 && n01 && n02) || (n10 && n11 && n12) || (n20 && n21 && n22)) = true → (ne2 m00 m01 m02 && ne2 m10 m11 m12 && ne2 m20 m21 m22 && ne2 n00 n01 n02 && ne2 n10 n11 n12 && ne2 n20 n21 n22) = true := by decide +kernel

/-- **The local lemma, with the eighteen variables and the nine tetrahedra explicit.** `m c p` and
`n x q` say that the mixed triangle `m c p` or `n x q` is in the set; `h p q` says that the common
tetrahedron `{s_i, s_j, c_k, c_l}` of `p, q` has not exactly three triangles in the set. -/
theorem local33_vars (m00 m01 m02 m10 m11 m12 m20 m21 m22 n00 n01 n02 n10 n11 n12 n20 n21 n22 : Bool)
    (h00 : ok4 m10 m20 n10 n20 = true) (h01 : ok4 m00 m20 n11 n21 = true) (h02 : ok4 m00 m10 n12 n22 = true) (h10 : ok4 m11 m21 n00 n20 = true) (h11 : ok4 m01 m21 n01 n21 = true) (h12 : ok4 m01 m11 n02 n22 = true) (h20 : ok4 m12 m22 n00 n10 = true) (h21 : ok4 m02 m22 n01 n11 = true) (h22 : ok4 m02 m12 n02 n12 = true)
    (hM : ((m00 && m01 && m02) || (m10 && m11 && m12) || (m20 && m21 && m22)) = true) (hN : ((n00 && n01 && n02) || (n10 && n11 && n12) || (n20 && n21 && n22)) = true) :
    ne2 m00 m01 m02 = true ∧ ne2 m10 m11 m12 = true ∧ ne2 m20 m21 m22 = true ∧ ne2 n00 n01 n02 = true ∧ ne2 n10 n11 n12 = true ∧ ne2 n20 n21 n22 = true := by
  have key := local33_prop m00 m10 m20 m01 m11 m21 m02 m12 m22 n00 n10 h20 n20 h00 h10 n01 n11 h21 n21 h01 h11 n02 n12 h22 n22 h02 h12 hM hN
  simpa [Bool.and_eq_true, and_assoc] using key

/-- **Wrong-input control for `local33`.** Without a full row of `n`, the conclusion fails. Take
`m 2 p` present for all `p`, `m 1 1` and `m 1 2` present, and nothing else: the nine common
tetrahedra force nothing (`ok4`), there is a full row of `m` and none of `n`, and the row `m 1 *` has
exactly two triangles, so adding `σ` forces `m 1 0`. -/
theorem local33_control :
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false false false false = true ∧
    ok4 true true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ok4 true true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ((true && true && true) || (false && true && true) || (false && false && false)) = true ∧
    ((false && false && false) || (false && false && false) || (false && false && false)) = false ∧
    ne2 false true true = false := by decide

/-! ## Forcing by an arbitrary set of tetrahedra -/

end Lightlike.SpinFoam.Forcing33

open Finset

namespace Lightlike.SpinFoam

variable {V : Type*} [DecidableEq V]

/-- Forcing by an arbitrary set `P` of tetrahedra: `ForcesIn P U T` says that the triangles `U` follow
from `T` by "a tetrahedron of `P` with three of its triangles in the set forces the fourth". For the
tetrahedra of a complex it is `Forces` (`forces_iff_forcesIn`). -/
inductive ForcesIn (P : Finset (Finset V)) (U : Finset (Finset V)) : Finset (Finset V) → Prop
  /-- Every triangle of `U` is already in the set. -/
  | done {T : Finset (Finset V)} (h : U ⊆ T) : ForcesIn P U T
  /-- The tetrahedron `t` of `P` forces its triangle `f`. -/
  | step {T : Finset (Finset V)} (t f : Finset V) (ht : t ∈ P) (hf : f ∈ t.powersetCard 3)
      (hT : ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T) (h : ForcesIn P U (insert f T)) : ForcesIn P U T

/-- A set `W` of triangles is closed under the tetrahedra `P`: no tetrahedron of `P` has exactly three
of its triangles in `W`. -/
def ClosedUnder (P : Finset (Finset V)) (W : Finset (Finset V)) : Prop :=
  ∀ t ∈ P, ∀ f ∈ t.powersetCard 3, (∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ W) → f ∈ W

namespace ForcesIn

variable {P P' : Finset (Finset V)} {U U' T T' : Finset (Finset V)} {t f : Finset V}

/-- **Soundness.** A set closed under `P` that contains `T` contains everything `T` forces. -/
theorem sound (h : ForcesIn P U T) {W : Finset (Finset V)} (hW : ClosedUnder P W) (hT : T ⊆ W) :
    U ⊆ W := by
  induction h with
  | done h => exact h.trans hT
  | step t f ht hf hg _ ih =>
    exact ih (insert_subset (hW t ht f hf fun g hg' hne => hT (hg g hg' hne)) hT)

/-- Forcing is monotone in the tetrahedra and in the starting set. -/
theorem mono (h : ForcesIn P U T) (hP : P ⊆ P') (hT : T ⊆ T') : ForcesIn P' U T' := by
  induction h generalizing T' with
  | done h => exact .done (h.trans hT)
  | step t f ht hf hg _ ih =>
    exact .step t f (hP ht) hf (fun g hg' hne => hT (hg g hg' hne)) (ih (insert_subset_insert f hT))

/-- A smaller target set is forced when a larger one is, or when it is already in the set. -/
theorem mono_target (h : ForcesIn P U T) (hU : U' ⊆ U ∪ T) : ForcesIn P U' T := by
  induction h generalizing U' with
  | done hU0 =>
    refine .done fun x hx => ?_
    rcases Finset.mem_union.mp (hU hx) with hx' | hx'
    · exact hU0 hx'
    · exact hx'
  | step t f ht hf hg _ ih =>
    refine .step t f ht hf hg (ih fun x hx => ?_)
    rcases Finset.mem_union.mp (hU hx) with hx' | hx'
    · exact Finset.mem_union_left _ hx'
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx')

/-- Forcing composes: what `T` forces, together with `T`, forces whatever `T ∪ U` forces. -/
theorem of_union (h : ForcesIn P U T) (h' : ForcesIn P U' (T ∪ U)) : ForcesIn P U' T := by
  induction h with
  | done hU => rwa [Finset.union_eq_left.mpr hU] at h'
  | step t f ht hf hg _ ih =>
    refine .step t f ht hf hg (ih ?_)
    exact h'.mono subset_rfl (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
      · exact Finset.mem_union_right _ hx)

/-- A set forced from `T` can be forced in one step from `T ∪ U` when `U` already contains the other
three triangles of a tetrahedron. -/
theorem single (ht : t ∈ P) (hf : f ∈ t.powersetCard 3) (hU : ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T) :
    ForcesIn P {f} T :=
  .step t f ht hf hU (.done (by simp))

/-- If `U` and `U'` are forced from `T`, so is `U ∪ U'`. -/
theorem union (h₁ : ForcesIn P U T) (h₂ : ForcesIn P U' T) : ForcesIn P (U ∪ U') T := by
  induction h₁ with
  | done hU =>
    exact h₂.mono_target (fun x hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_right _ (hU hx)
      · exact Finset.mem_union_left _ hx)
  | step t f ht hf hg _ ih => exact .step t f ht hf hg (ih (h₂.mono subset_rfl (subset_insert _ _)))

/-- A finite set is forced when each of its members is. -/
theorem of_singles (h : ∀ g ∈ U, ForcesIn P {g} T) : ForcesIn P U T := by
  induction U using Finset.induction_on with
  | empty => exact .done (empty_subset _)
  | insert g U hg ih =>
    rw [insert_eq]
    exact (h g (mem_insert_self _ _)).union (ih fun g' hg' => h g' (mem_insert_of_mem hg'))

/-- The triangle `f` of a tetrahedron `t` of `P` is forced from `T` when the other three are. -/
theorem of_forced_others (ht : t ∈ P) (hf : f ∈ t.powersetCard 3)
    (h : ∀ g ∈ t.powersetCard 3, g ≠ f → ForcesIn P {g} T) : ForcesIn P {f} T := by
  have hU : ForcesIn P ((t.powersetCard 3).erase f) T :=
    of_singles fun g hg => h g (mem_of_mem_erase hg) (ne_of_mem_erase hg)
  refine hU.of_union (single ht hf fun g hg hne => ?_)
  exact mem_union_right _ (mem_erase.mpr ⟨hne, hg⟩)

end ForcesIn

/-- A list of forcing steps `(t, f)` for the tetrahedra `P`, checked one after the other: a decision
procedure whose success proves `ForcesIn` (`forcesIn_of_forcesInBy`). -/
def forcesInBy (P U : Finset (Finset V)) :
    List (Finset V × Finset V) → Finset (Finset V) → Bool
  | [], T => decide (U ⊆ T)
  | (t, f) :: l, T => decide (t ∈ P ∧ f ∈ t.powersetCard 3 ∧
      ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T) && forcesInBy P U l (insert f T)

/-- A successful `forcesInBy` check proves `ForcesIn`. -/
theorem forcesIn_of_forcesInBy {P U : Finset (Finset V)} {l : List (Finset V × Finset V)}
    {T : Finset (Finset V)} (h : forcesInBy P U l T = true) : ForcesIn P U T := by
  induction l generalizing T with
  | nil => exact .done (of_decide_eq_true h)
  | cons p l ih =>
    obtain ⟨t, f⟩ := p
    simp only [forcesInBy, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ht, hf, hg⟩ := of_decide_eq_true h1
    exact .step t f ht hf hg (ih h2)

/-! ## The six vertices as `Fin 6` -/

namespace Forcing33

/-- The triangle `σ = {s_0, s_1, s_2}`: the positions `0, 1, 2`. -/
def sigX : Finset (Fin 6) := {0, 1, 2}

/-- The triangle `τ = {c_0, c_1, c_2}`: the positions `3, 4, 5`. -/
def tauX : Finset (Fin 6) := {3, 4, 5}

/-- The mixed triangle `m k p = {s_i, s_j, c_k}`, `{i, j} = {0,1,2} ∖ {p}`. -/
def mX (k p : Fin 3) : Finset (Fin 6) :=
  univ.filter fun v => v.val = 3 + k.val ∨ (v.val < 3 ∧ v.val ≠ p.val)

/-- The mixed triangle `n x q = {s_x, c_k, c_l}`, `{k, l} = {0,1,2} ∖ {q}`. -/
def nX (x q : Fin 3) : Finset (Fin 6) :=
  univ.filter fun v => v.val = x.val ∨ (3 ≤ v.val ∧ v.val - 3 ≠ q.val)

/-- The common tetrahedron `{s_i, s_j, c_k, c_l}`, `{i, j} = {0,1,2} ∖ {p}`, `{k, l} = {0,1,2} ∖ {q}`. -/
def tetC (p q : Fin 3) : Finset (Fin 6) :=
  univ.filter fun v => (v.val < 3 ∧ v.val ≠ p.val) ∨ (3 ≤ v.val ∧ v.val - 3 ≠ q.val)

/-- The tetrahedron `σ ∪ {c_k}` of the complex before the move. -/
def tetS (k : Fin 3) : Finset (Fin 6) := univ.filter fun v => v.val < 3 ∨ v.val = 3 + k.val

/-- The tetrahedron `τ ∪ {s_x}` of the complex after the move. -/
def tetT (x : Fin 3) : Finset (Fin 6) := univ.filter fun v => 3 ≤ v.val ∨ v.val = x.val

lemma tri_tetS : ∀ k : Fin 3, (tetS k).powersetCard 3 = insert sigX (univ.image (mX k)) := by
  decide

lemma tri_tetT : ∀ x : Fin 3, (tetT x).powersetCard 3 = insert tauX (univ.image (nX x)) := by
  decide

lemma tri_tetC : ∀ p q : Fin 3, (tetC p q).powersetCard 3 =
    (univ.erase q).image (fun k => mX k p) ∪ (univ.erase p).image (fun i => nX i q) := by
  decide

lemma mX_ne_sigX : ∀ k p : Fin 3, mX k p ≠ sigX := by decide

lemma nX_ne_tauX : ∀ x q : Fin 3, nX x q ≠ tauX := by decide

lemma nX_ne_sigX : ∀ x q : Fin 3, nX x q ≠ sigX := by decide

lemma mX_inj : ∀ k p p' : Fin 3, mX k p = mX k p' → p = p' := by decide

lemma nX_inj : ∀ x q q' : Fin 3, nX x q = nX x q' → q = q' := by decide

/-- The two indices other than `q`, in increasing order. -/
def a1 (q : Fin 3) : Fin 3 := if q = 0 then 1 else 0

/-- The two indices other than `q`, in increasing order. -/
def a2 (q : Fin 3) : Fin 3 := if q = 2 then 1 else 2

lemma ne_iff_a : ∀ q k : Fin 3, k ≠ q ↔ k = a1 q ∨ k = a2 q := by decide

/-- A tetrahedron with four triangles `a b c d` that is closed (whenever three are in, the fourth is
in) does not have exactly three of them in. -/
lemma ok4_of_closed (a b c d : Bool) (h1 : b = true → c = true → d = true → a = true)
    (h2 : a = true → c = true → d = true → b = true) (h3 : a = true → b = true → d = true → c = true)
    (h4 : a = true → b = true → c = true → d = true) : ok4 a b c d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [ok4]

/-- A row of three triangles that is not `ne2` can be completed from any two of them. -/
lemma fill_of_ne2 (a b c : Bool) (h : ne2 a b c = true) :
    (b = true → c = true → a = true) ∧ (a = true → c = true → b = true) ∧
      (a = true → b = true → c = true) := by
  cases a <;> cases b <;> cases c <;> simp_all [ne2]

lemma natAdd_mem_tauX : ∀ j : Fin 3, Fin.natAdd 3 j ∈ tauX := by decide

lemma castAdd_mem_sigX : ∀ i : Fin 3, Fin.castAdd 3 i ∈ sigX := by decide

lemma tetS_eq : ∀ k : Fin 3, tetS k = insert (Fin.natAdd 3 k) sigX := by decide

lemma tetT_eq : ∀ x : Fin 3, tetT x = insert (Fin.castAdd 3 x) tauX := by decide

lemma sigX_union_tauX : sigX ∪ tauX = univ := by decide

lemma exists_natAdd : ∀ i ∈ tauX, ∃ j : Fin 3, i = Fin.natAdd 3 j := by decide

lemma exists_castAdd : ∀ i ∈ sigX, ∃ j : Fin 3, i = Fin.castAdd 3 j := by decide

lemma tetS_of : ∀ j : Fin 3, ∀ u : Finset (Fin 6), u ⊆ univ.erase (Fin.natAdd 3 j) → sigX ⊆ u →
    #u = 4 → ∃ k, u = tetS k := by decide

lemma tetT_of : ∀ i : Fin 3, ∀ u : Finset (Fin 6), u ⊆ univ.erase (Fin.castAdd 3 i) → tauX ⊆ u →
    #u = 4 → ∃ x, u = tetT x := by decide

lemma tetS_sub : ∀ k j : Fin 3, j ≠ k → tetS k ⊆ univ.erase (Fin.natAdd 3 j) := by decide

lemma tetT_sub : ∀ x i : Fin 3, i ≠ x → tetT x ⊆ univ.erase (Fin.castAdd 3 i) := by decide

lemma card_tetS : ∀ k : Fin 3, #(tetS k) = 4 := by decide

lemma card_tetT : ∀ x : Fin 3, #(tetT x) = 4 := by decide

lemma tetC_sub : ∀ p q : Fin 3, tetC p q ⊆ univ.erase (Fin.natAdd 3 q) := by decide

lemma not_sig_tetC : ∀ p q : Fin 3, ¬ sigX ⊆ tetC p q := by decide

lemma mX_sub : ∀ k p j : Fin 3, j ≠ k → mX k p ⊆ univ.erase (Fin.natAdd 3 j) := by decide

lemma nX_sub : ∀ x q : Fin 3, nX x q ⊆ univ.erase (Fin.natAdd 3 q) := by decide

lemma card_tetC : ∀ p q : Fin 3, #(tetC p q) = 4 := by decide

lemma card_mX : ∀ k p : Fin 3, #(mX k p) = 3 := by decide

lemma card_nX : ∀ x q : Fin 3, #(nX x q) = 3 := by decide

lemma sigX_sub : sigX ⊆ univ.erase (Fin.natAdd 3 (0 : Fin 3)) := by decide

lemma tauX_sub : tauX ⊆ univ.erase (Fin.castAdd 3 (0 : Fin 3)) := by decide

section Abstract

variable {V : Type*} [DecidableEq V] (e : Fin 6 ↪ V)

/-- The subset of `V` at the positions `X`. -/
def tx (X : Finset (Fin 6)) : Finset V := X.map e

lemma tx_inj {X Y : Finset (Fin 6)} : tx e X = tx e Y ↔ X = Y := Finset.map_inj

lemma mem_tris_tx {X : Finset (Fin 6)} {g : Finset V} :
    g ∈ (tx e X).powersetCard 3 ↔ ∃ Y ∈ X.powersetCard 3, tx e Y = g := by
  unfold tx
  rw [Finset.powersetCard_map]
  simp [Finset.mem_map]

lemma mem_tris_tetS (k : Fin 3) {g : Finset V} :
    g ∈ (tx e (tetS k)).powersetCard 3 ↔ g = tx e sigX ∨ ∃ p, g = tx e (mX k p) := by
  rw [mem_tris_tx, tri_tetS]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rcases mem_insert.mp hY with rfl | hY
    · exact Or.inl rfl
    · obtain ⟨p, -, rfl⟩ := mem_image.mp hY
      exact Or.inr ⟨p, rfl⟩
  · rintro (rfl | ⟨p, rfl⟩)
    · exact ⟨sigX, mem_insert_self _ _, rfl⟩
    · exact ⟨mX k p, mem_insert_of_mem (mem_image_of_mem _ (mem_univ _)), rfl⟩

lemma mem_tris_tetT (x : Fin 3) {g : Finset V} :
    g ∈ (tx e (tetT x)).powersetCard 3 ↔ g = tx e tauX ∨ ∃ q, g = tx e (nX x q) := by
  rw [mem_tris_tx, tri_tetT]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rcases mem_insert.mp hY with rfl | hY
    · exact Or.inl rfl
    · obtain ⟨q, -, rfl⟩ := mem_image.mp hY
      exact Or.inr ⟨q, rfl⟩
  · rintro (rfl | ⟨q, rfl⟩)
    · exact ⟨tauX, mem_insert_self _ _, rfl⟩
    · exact ⟨nX x q, mem_insert_of_mem (mem_image_of_mem _ (mem_univ _)), rfl⟩

lemma mem_tris_tetC (p q : Fin 3) {g : Finset V} :
    g ∈ (tx e (tetC p q)).powersetCard 3 ↔
      (∃ k, k ≠ q ∧ g = tx e (mX k p)) ∨ ∃ i, i ≠ p ∧ g = tx e (nX i q) := by
  rw [mem_tris_tx, tri_tetC]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rcases mem_union.mp hY with hY | hY
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hY
      exact Or.inl ⟨k, (mem_erase.mp hk).1, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hY
      exact Or.inr ⟨i, (mem_erase.mp hi).1, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨_, mem_union_left _ (mem_image_of_mem _ (mem_erase.mpr ⟨hk, mem_univ _⟩)), rfl⟩
    · exact ⟨_, mem_union_right _ (mem_image_of_mem _ (mem_erase.mpr ⟨hi, mem_univ _⟩)), rfl⟩

end Abstract

section Dichotomy

variable {V : Type*} [DecidableEq V]

/-- A set closed under two sets of tetrahedra is closed under their union. -/
lemma closedUnder_union {P Q W : Finset (Finset V)} (hP : ClosedUnder P W) (hQ : ClosedUnder Q W) :
    ClosedUnder (P ∪ Q) W := by
  intro t ht f hf h
  rcases mem_union.mp ht with ht | ht
  · exact hP t ht f hf h
  · exact hQ t ht f hf h

/-- **A cone of tetrahedra without a full row is closed.** The tetrahedra `Q` each have the triangles
`a` and `r i 0, r i 1, r i 2` for one `i`. If `a ∉ A` and no row `r i` lies in `A`, then `A` is
closed under `Q`. -/
lemma cone_closed_of_not_full {Q A : Finset (Finset V)} {a : Finset V} {r : Fin 3 → Fin 3 → Finset V}
    (hQ : ∀ t ∈ Q, ∃ i, ∀ g, g ∈ t.powersetCard 3 ↔ g = a ∨ ∃ j, g = r i j)
    (hne : ∀ i j, r i j ≠ a) (ha : a ∉ A) (hrow : ¬ ∃ i, ∀ j, r i j ∈ A) : ClosedUnder Q A := by
  intro t ht f hf hothers
  obtain ⟨i, hi⟩ := hQ t ht
  rcases (hi f).mp hf with rfl | ⟨j, rfl⟩
  · exact absurd ⟨i, fun j => hothers _ ((hi _).mpr (Or.inr ⟨j, rfl⟩)) (hne i j)⟩ hrow
  · exact absurd (hothers a ((hi a).mpr (Or.inl rfl)) (hne i j).symm) ha

/-- **A cone of tetrahedra whose rows are never missing exactly one triangle is closed once the
apex is added.** -/
lemma cone_closed_insert {Q A : Finset (Finset V)} {a : Finset V} {r : Fin 3 → Fin 3 → Finset V}
    (hQ : ∀ t ∈ Q, ∃ i, ∀ g, g ∈ t.powersetCard 3 ↔ g = a ∨ ∃ j, g = r i j)
    (hne : ∀ i j, r i j ≠ a) (hinj : ∀ i, Function.Injective (r i))
    (hfill : ∀ i j, (∀ j', j' ≠ j → r i j' ∈ A) → r i j ∈ A) : ClosedUnder Q (insert a A) := by
  intro t ht f hf hothers
  obtain ⟨i, hi⟩ := hQ t ht
  rcases (hi f).mp hf with rfl | ⟨j, rfl⟩
  · exact mem_insert_self _ _
  · refine mem_insert_of_mem (hfill i j fun j' hj' => ?_)
    have := hothers (r i j') ((hi _).mpr (Or.inr ⟨j', rfl⟩)) (fun h => hj' (hinj i h))
    rcases mem_insert.mp this with h | h
    · exact absurd h (hne i j')
    · exact h

/-- The four triangles of a closed tetrahedron: whenever three are in, so is the fourth. -/
lemma closed_four {A : Finset (Finset V)} {t : Finset V} {X1 X2 X3 X4 : Finset V}
    (hcl : ∀ f ∈ t.powersetCard 3, (∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ A) → f ∈ A)
    (htr : ∀ g, g ∈ t.powersetCard 3 ↔ g = X1 ∨ g = X2 ∨ g = X3 ∨ g = X4) :
    (X2 ∈ A → X3 ∈ A → X4 ∈ A → X1 ∈ A) ∧ (X1 ∈ A → X3 ∈ A → X4 ∈ A → X2 ∈ A) ∧
      (X1 ∈ A → X2 ∈ A → X4 ∈ A → X3 ∈ A) ∧ (X1 ∈ A → X2 ∈ A → X3 ∈ A → X4 ∈ A) := by
  refine ⟨fun h2 h3 h4 => hcl _ ((htr _).mpr (Or.inl rfl)) ?_,
    fun h1 h3 h4 => hcl _ ((htr _).mpr (Or.inr (Or.inl rfl))) ?_,
    fun h1 h2 h4 => hcl _ ((htr _).mpr (Or.inr (Or.inr (Or.inl rfl)))) ?_,
    fun h1 h2 h3 => hcl _ ((htr _).mpr (Or.inr (Or.inr (Or.inr rfl)))) ?_⟩ <;>
  intro g hg hne <;> rcases (htr g).mp hg with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | assumption


lemma tris_tetC_four (e : Fin 6 ↪ V) (p q : Fin 3) (g : Finset V) :
    g ∈ (tx e (tetC p q)).powersetCard 3 ↔ g = tx e (mX (a1 q) p) ∨ g = tx e (mX (a2 q) p) ∨
      g = tx e (nX (a1 p) q) ∨ g = tx e (nX (a2 p) q) := by
  rw [mem_tris_tetC]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩)
    · rcases (ne_iff_a q k).mp hk with rfl | rfl <;> simp
    · rcases (ne_iff_a p i).mp hi with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨_, (ne_iff_a q _).mpr (Or.inl rfl), rfl⟩
    · exact Or.inl ⟨_, (ne_iff_a q _).mpr (Or.inr rfl), rfl⟩
    · exact Or.inr ⟨_, (ne_iff_a p _).mpr (Or.inl rfl), rfl⟩
    · exact Or.inr ⟨_, (ne_iff_a p _).mpr (Or.inr rfl), rfl⟩

open Classical in
/-- **The dichotomy of the 3-3 move.** Let `P0` be the tetrahedra common to the complexes before and
after the move, and `C` the common triangles. If `T ⊆ C` does not force `C` using `P0` alone, then
`T` does not force the triangles of both complexes: not before the move (adding `σ` and the three
tetrahedra `σ ∪ {c_k}`), or not after it (adding `τ` and `τ ∪ {s_x}`). -/
theorem forcing_dichotomy (e : Fin 6 ↪ V) (P0 C T : Finset (Finset V))
    (hCt : ∀ t ∈ P0, ∀ g ∈ t.powersetCard 3, g ∈ C)
    (hσC : tx e sigX ∉ C) (hτC : tx e tauX ∉ C)
    (hcom : ∀ p q, tx e (tetC p q) ∈ P0)
    (hT : T ⊆ C) (hnot : ¬ ForcesIn P0 C T) :
    ¬ ForcesIn (P0 ∪ univ.image fun k => tx e (tetS k)) (insert (tx e sigX) C) T ∨
      ¬ ForcesIn (P0 ∪ univ.image fun x => tx e (tetT x)) (insert (tx e tauX) C) T := by
  set A : Finset (Finset V) := C.filter (fun f => ForcesIn P0 {f} T) with hA
  have hAC : A ⊆ C := filter_subset _ _
  have hTA : T ⊆ A := fun f hf => mem_filter.mpr ⟨hT hf, .done (by simpa using hf)⟩
  have hAforced : ForcesIn P0 A T := ForcesIn.of_singles fun g hg => (mem_filter.mp hg).2
  have hAcl : ClosedUnder P0 A := fun t ht f hf hothers =>
    mem_filter.mpr ⟨hCt t ht f hf, ForcesIn.of_forced_others ht hf
      fun g hg hne => (mem_filter.mp (hothers g hg hne)).2⟩
  have hCA : ¬ C ⊆ A := fun h => hnot (hAforced.mono_target (fun x hx => mem_union_left _ (h hx)))
  have hσA : tx e sigX ∉ A := fun h => hσC (hAC h)
  have hτA : tx e tauX ∉ A := fun h => hτC (hAC h)
  have hQσ : ∀ t ∈ (univ.image fun k => tx e (tetS k)), ∃ k : Fin 3,
      ∀ g, g ∈ t.powersetCard 3 ↔ g = tx e sigX ∨ ∃ p, g = tx e (mX k p) := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := mem_image.mp ht
    exact ⟨k, fun g => mem_tris_tetS e k⟩
  have hQτ : ∀ t ∈ (univ.image fun x => tx e (tetT x)), ∃ x : Fin 3,
      ∀ g, g ∈ t.powersetCard 3 ↔ g = tx e tauX ∨ ∃ q, g = tx e (nX x q) := by
    intro t ht
    obtain ⟨x, -, rfl⟩ := mem_image.mp ht
    exact ⟨x, fun g => mem_tris_tetT e x⟩
  have hneM : ∀ k p, tx e (mX k p) ≠ tx e sigX := fun k p h => mX_ne_sigX k p ((tx_inj e).mp h)
  have hneN : ∀ x q, tx e (nX x q) ≠ tx e tauX := fun x q h => nX_ne_tauX x q ((tx_inj e).mp h)
  have hinjM : ∀ k, Function.Injective fun p => tx e (mX k p) := fun k p p' h =>
    mX_inj k p p' ((tx_inj e).mp h)
  have hinjN : ∀ x, Function.Injective fun q => tx e (nX x q) := fun x q q' h =>
    nX_inj x q q' ((tx_inj e).mp h)
  by_cases hrM : ∃ k, ∀ p, tx e (mX k p) ∈ A
  swap
  · left
    intro hK
    have := hK.sound (closedUnder_union hAcl
      (cone_closed_of_not_full (r := fun k p => tx e (mX k p)) hQσ hneM hσA hrM)) hTA
    exact hCA fun f hf => this (mem_insert_of_mem hf)
  by_cases hrN : ∃ x, ∀ q, tx e (nX x q) ∈ A
  swap
  · right
    intro hK
    have := hK.sound (closedUnder_union hAcl
      (cone_closed_of_not_full (r := fun x q => tx e (nX x q)) hQτ hneN hτA hrN)) hTA
    exact hCA fun f hf => this (mem_insert_of_mem hf)
  -- both rows: the local lemma
  set mb : Fin 3 → Fin 3 → Bool := fun k p => decide (tx e (mX k p) ∈ A) with hmb
  set nb : Fin 3 → Fin 3 → Bool := fun x q => decide (tx e (nX x q) ∈ A) with hnb
  have hok : ∀ p q, ok4 (mb (a1 q) p) (mb (a2 q) p) (nb (a1 p) q) (nb (a2 p) q) = true := by
    intro p q
    have h4 := closed_four (hAcl _ (hcom p q)) (tris_tetC_four e p q)
    obtain ⟨c1, c2, c3, c4⟩ := h4
    exact ok4_of_closed _ _ _ _
      (fun hb hc hd => decide_eq_true (c1 (of_decide_eq_true hb) (of_decide_eq_true hc)
        (of_decide_eq_true hd)))
      (fun ha hc hd => decide_eq_true (c2 (of_decide_eq_true ha) (of_decide_eq_true hc)
        (of_decide_eq_true hd)))
      (fun ha hb hd => decide_eq_true (c3 (of_decide_eq_true ha) (of_decide_eq_true hb)
        (of_decide_eq_true hd)))
      (fun ha hb hc => decide_eq_true (c4 (of_decide_eq_true ha) (of_decide_eq_true hb)
        (of_decide_eq_true hc)))
  have hMb : (((mb 0 0 && mb 0 1 && mb 0 2) || (mb 1 0 && mb 1 1 && mb 1 2) ||
      (mb 2 0 && mb 2 1 && mb 2 2))) = true := by
    obtain ⟨k, hk⟩ := hrM
    simp only [hmb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    fin_cases k
    · exact Or.inl (Or.inl ⟨⟨hk 0, hk 1⟩, hk 2⟩)
    · exact Or.inl (Or.inr ⟨⟨hk 0, hk 1⟩, hk 2⟩)
    · exact Or.inr ⟨⟨hk 0, hk 1⟩, hk 2⟩
  have hNb : (((nb 0 0 && nb 0 1 && nb 0 2) || (nb 1 0 && nb 1 1 && nb 1 2) ||
      (nb 2 0 && nb 2 1 && nb 2 2))) = true := by
    obtain ⟨x, hx⟩ := hrN
    simp only [hnb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    fin_cases x
    · exact Or.inl (Or.inl ⟨⟨hx 0, hx 1⟩, hx 2⟩)
    · exact Or.inl (Or.inr ⟨⟨hx 0, hx 1⟩, hx 2⟩)
    · exact Or.inr ⟨⟨hx 0, hx 1⟩, hx 2⟩
  have key := local33_vars (mb 0 0) (mb 0 1) (mb 0 2) (mb 1 0) (mb 1 1) (mb 1 2) (mb 2 0) (mb 2 1) (mb 2 2) (nb 0 0) (nb 0 1) (nb 0 2) (nb 1 0) (nb 1 1) (nb 1 2) (nb 2 0) (nb 2 1) (nb 2 2)
    (hok 0 0) (hok 0 1) (hok 0 2) (hok 1 0) (hok 1 1) (hok 1 2) (hok 2 0) (hok 2 1) (hok 2 2) hMb hNb
  obtain ⟨r0, r1, r2, s0, s1, s2⟩ := key
  have hrows : ∀ k, ne2 (mb k 0) (mb k 1) (mb k 2) = true := by
    intro k; fin_cases k <;> assumption
  have hcols : ∀ x, ne2 (nb x 0) (nb x 1) (nb x 2) = true := by
    intro x; fin_cases x <;> assumption
  have hfM : ∀ k p, (∀ p', p' ≠ p → tx e (mX k p') ∈ A) → tx e (mX k p) ∈ A := by
    intro k p h
    have hr := fill_of_ne2 _ _ _ (hrows k)
    fin_cases p
    · exact of_decide_eq_true (hr.1 (decide_eq_true (h 1 (by decide)))
        (decide_eq_true (h 2 (by decide))))
    · exact of_decide_eq_true (hr.2.1 (decide_eq_true (h 0 (by decide)))
        (decide_eq_true (h 2 (by decide))))
    · exact of_decide_eq_true (hr.2.2 (decide_eq_true (h 0 (by decide)))
        (decide_eq_true (h 1 (by decide))))
  have hfN : ∀ x q, (∀ q', q' ≠ q → tx e (nX x q') ∈ A) → tx e (nX x q) ∈ A := by
    intro x q h
    have hr := fill_of_ne2 _ _ _ (hcols x)
    fin_cases q
    · exact of_decide_eq_true (hr.1 (decide_eq_true (h 1 (by decide)))
        (decide_eq_true (h 2 (by decide))))
    · exact of_decide_eq_true (hr.2.1 (decide_eq_true (h 0 (by decide)))
        (decide_eq_true (h 2 (by decide))))
    · exact of_decide_eq_true (hr.2.2 (decide_eq_true (h 0 (by decide)))
        (decide_eq_true (h 1 (by decide))))
  left
  intro hK
  have hcl : ClosedUnder P0 (insert (tx e sigX) A) := fun t ht f hf hothers => by
    refine mem_insert_of_mem (hAcl t ht f hf fun g hg hne => ?_)
    rcases mem_insert.mp (hothers g hg hne) with h | h
    · exact absurd (h ▸ hCt t ht g hg) hσC
    · exact h
  have := hK.sound (closedUnder_union hcl
    (cone_closed_insert (r := fun k p => tx e (mX k p)) hQσ hneM hinjM hfM))
    (hTA.trans (subset_insert _ _))
  refine hCA fun f hf => ?_
  rcases mem_insert.mp (this (mem_insert_of_mem hf)) with h | h
  · exact absurd (h ▸ hf) hσC
  · exact h


/-- **The easy direction.** If `T` forces the common triangles `C` using the common tetrahedra alone,
then it also forces them together with `σ` once the tetrahedra `σ ∪ {c_k}` are added: one of them
forces `σ` from its three mixed triangles. -/
theorem forces_sigma_of_common (e : Fin 6 ↪ V) (P0 C T : Finset (Finset V))
    (hmixM : ∀ k p, tx e (mX k p) ∈ C) (hS : ForcesIn P0 C T) :
    ForcesIn (P0 ∪ univ.image fun k => tx e (tetS k)) (insert (tx e sigX) C) T := by
  have hP : P0 ⊆ P0 ∪ univ.image fun k => tx e (tetS k) := subset_union_left
  have h1 : ForcesIn (P0 ∪ univ.image fun k => tx e (tetS k)) C T := hS.mono hP subset_rfl
  have ht : tx e (tetS 0) ∈ P0 ∪ univ.image fun k => tx e (tetS k) :=
    mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  have h2 : ForcesIn (P0 ∪ univ.image fun k => tx e (tetS k)) {tx e sigX} T :=
    h1.of_union (ForcesIn.single ht ((mem_tris_tetS e 0).mpr (Or.inl rfl)) fun g hg hne => by
      rcases (mem_tris_tetS e 0).mp hg with rfl | ⟨p, rfl⟩
      · exact absurd rfl hne
      · exact mem_union_right _ (hmixM 0 p))
  exact (h1.union h2).mono_target (fun x hx => by
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_left _ (mem_union_right _ (mem_singleton_self _))
    · exact mem_union_left _ (mem_union_left _ hx))

/-- The same for `τ` and the tetrahedra `τ ∪ {s_x}`. -/
theorem forces_tau_of_common (e : Fin 6 ↪ V) (P0 C T : Finset (Finset V))
    (hmixN : ∀ x q, tx e (nX x q) ∈ C) (hS : ForcesIn P0 C T) :
    ForcesIn (P0 ∪ univ.image fun x => tx e (tetT x)) (insert (tx e tauX) C) T := by
  have hP : P0 ⊆ P0 ∪ univ.image fun x => tx e (tetT x) := subset_union_left
  have h1 : ForcesIn (P0 ∪ univ.image fun x => tx e (tetT x)) C T := hS.mono hP subset_rfl
  have ht : tx e (tetT 0) ∈ P0 ∪ univ.image fun x => tx e (tetT x) :=
    mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  have h2 : ForcesIn (P0 ∪ univ.image fun x => tx e (tetT x)) {tx e tauX} T :=
    h1.of_union (ForcesIn.single ht ((mem_tris_tetT e 0).mpr (Or.inl rfl)) fun g hg hne => by
      rcases (mem_tris_tetT e 0).mp hg with rfl | ⟨q, rfl⟩
      · exact absurd rfl hne
      · exact mem_union_right _ (hmixN 0 q))
  exact (h1.union h2).mono_target (fun x hx => by
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_left _ (mem_union_right _ (mem_singleton_self _))
    · exact mem_union_left _ (mem_union_left _ hx))

end Dichotomy

/-! ## The complexes before and after the move -/

section Complex

open Lightlike.FourD Complex4

variable {V : Type*} [LinearOrder V] {K : Complex4 V} {σ τ : Finset V}

/-- A 3-3 move: the two triangles have three vertices each. -/
lemma card_tau (h : K.IsMove σ τ) (hσ : #σ = 3) : #τ = 3 := by have := h.card; omega

/-- **Six positions for the six vertices.** The vertices of `σ` and `τ` are the images of `{0,1,2}` and
`{3,4,5}` under an embedding `Fin 6 ↪ V`. -/
lemma exists_embedding (h : K.IsMove σ τ) (hσ : #σ = 3) :
    ∃ e : Fin 6 ↪ V, tx e sigX = σ ∧ tx e tauX = τ := by
  have hτ := card_tau h hσ
  let s := σ.orderEmbOfFin hσ
  let c := τ.orderEmbOfFin hτ
  let f : Fin 6 → V := fun i => if hi : i.val < 3 then s ⟨i, hi⟩ else c ⟨i - 3, by omega⟩
  have hs : ∀ i, s i ∈ σ := fun i => σ.orderEmbOfFin_mem hσ i
  have hc : ∀ i, c i ∈ τ := fun i => τ.orderEmbOfFin_mem hτ i
  have hdisj : ∀ x ∈ σ, ∀ y ∈ τ, x ≠ y := fun x hx y hy hxy =>
    disjoint_left.mp h.disj hx (hxy ▸ hy)
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [f] at hij
    by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3 <;> simp only [hi, hj, dite_true, dite_false] at hij
    · have := s.injective hij; exact Fin.ext (by simpa using congrArg Fin.val this)
    · exact absurd hij (hdisj _ (hs _) _ (hc _))
    · exact absurd hij.symm (hdisj _ (hs _) _ (hc _))
    · have := c.injective hij
      have := congrArg Fin.val this
      exact Fin.ext (by simp at this; omega)
  refine ⟨⟨f, hinj⟩, ?_, ?_⟩
  · refine eq_of_subset_of_card_le ?_ (by rw [hσ]; simp only [tx, card_map]; decide)
    intro x hx
    simp only [tx, mem_map, Function.Embedding.coeFn_mk, sigX] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have : i.val < 3 := by fin_cases i <;> simp_all
    simp only [f, this, dite_true]
    exact hs _
  · refine eq_of_subset_of_card_le ?_ (by rw [hτ]; simp only [tx, card_map]; decide)
    intro x hx
    simp only [tx, mem_map, Function.Embedding.coeFn_mk, tauX] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have : ¬ i.val < 3 := by fin_cases i <;> simp_all
    simp only [f, this, dite_false]
    exact hc _

/-- A face of `K` that does not contain `σ` is a face of the complex after the move, and does not
contain `τ`. -/
lemma sub_face (h : K.IsMove σ τ) {k : ℕ} {f : Finset V} (hf : f ∈ K.faces k) (hσf : ¬ σ ⊆ f) :
    f ∈ (K.move h).faces k ∧ ¬ τ ⊆ f := by
  obtain ⟨S, hS, hfS, hc⟩ := mem_faces.mp hf
  by_cases hσS : σ ⊆ S
  · obtain ⟨b, hb, rfl⟩ := h.star S hS hσS
    obtain ⟨a, ha, haf⟩ := Finset.not_subset.mp hσf
    refine ⟨mem_faces.mpr ⟨(σ ∪ τ).erase a, mem_move.mpr (Or.inr ⟨a, ha, rfl⟩),
      subset_erase_of_notMem (hfS.trans (erase_subset _ _)) haf, hc⟩, fun hτf => ?_⟩
    exact (mem_erase.mp (hfS (hτf hb))).1 rfl
  · exact ⟨mem_faces.mpr ⟨S, mem_move.mpr (Or.inl ⟨hS, hσS⟩), hfS, hc⟩,
      fun hτf => h.fresh S hS (hτf.trans hfS)⟩

/-- The converse: a face of the complex after the move that does not contain `τ` is a face of `K`
that does not contain `σ`. -/
lemma sub_face_back (h : K.IsMove σ τ) {k : ℕ} {f : Finset V} (hf : f ∈ (K.move h).faces k)
    (hτf : ¬ τ ⊆ f) : f ∈ K.faces k ∧ ¬ σ ⊆ f := by
  have := sub_face h.symm hf hτf
  rwa [move_move] at this

section Decomposition

variable (e : Fin 6 ↪ V)

lemma tx_univ_erase (i : Fin 6) : (tx e sigX ∪ tx e tauX).erase (e i) = tx e (univ.erase i) := by
  unfold tx
  rw [← map_union, sigX_union_tauX, map_erase]

/-- The 4-simplices of `K` that contain `σ` are the `(σ ∪ τ) \ {c_j}`. -/
lemma star_form (h : K.IsMove (tx e sigX) (tx e tauX)) {S : Finset V} (hS : S ∈ K.simps)
    (hσS : tx e sigX ⊆ S) : ∃ j : Fin 3, S = tx e (univ.erase (Fin.natAdd 3 j)) := by
  obtain ⟨b, hb, rfl⟩ := h.star S hS hσS
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hb
  obtain ⟨j, rfl⟩ := exists_natAdd i hi
  exact ⟨j, tx_univ_erase e _⟩

/-- The tetrahedra of `K` are those that do not contain `σ` and the three `σ ∪ {c_k}`. -/
lemma tets_before (h : K.IsMove (tx e sigX) (tx e tauX)) :
    K.tets = K.tets.filter (fun t => ¬ tx e sigX ⊆ t) ∪ univ.image fun k => tx e (tetS k) := by
  ext t
  simp only [mem_union, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · intro ht
    by_cases hσt : tx e sigX ⊆ t
    · right
      obtain ⟨S, hS, htS, hc⟩ := mem_faces.mp ht
      obtain ⟨j, rfl⟩ := star_form e h hS (hσt.trans htS)
      obtain ⟨u, hu, rfl⟩ := subset_map_iff.mp htS
      have hsu : sigX ⊆ u := (map_subset_map).mp hσt
      have hc' : #u = 4 := by simpa [card_map] using hc
      obtain ⟨k, rfl⟩ := tetS_of j u hu hsu hc'
      exact ⟨k, rfl⟩
    · exact Or.inl ⟨ht, hσt⟩
  · rintro (⟨ht, -⟩ | ⟨k, rfl⟩)
    · exact ht
    · obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ k := by revert k; decide
      refine mem_faces.mpr ⟨tx e (univ.erase (Fin.natAdd 3 j)), ?_, ?_, ?_⟩
      · rw [← tx_univ_erase]
        exact h.mem _ (mem_map_of_mem _ (natAdd_mem_tauX j))
      · exact map_subset_map.mpr (tetS_sub k j hj)
      · simp [tx, card_map, card_tetS]

/-- The tetrahedra after the move are those that do not contain `τ` and the three `τ ∪ {s_x}`. -/
lemma tets_after (h : K.IsMove (tx e sigX) (tx e tauX)) :
    (K.move h).tets = (K.move h).tets.filter (fun t => ¬ tx e tauX ⊆ t) ∪
      univ.image fun x => tx e (tetT x) := by
  ext t
  simp only [mem_union, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · intro ht
    by_cases hτt : tx e tauX ⊆ t
    · right
      obtain ⟨S, hS, htS, hc⟩ := mem_faces.mp ht
      rcases mem_move.mp hS with ⟨hSK, -⟩ | ⟨a, ha, rfl⟩
      · exact absurd (hτt.trans htS) (h.fresh S hSK)
      · obtain ⟨i, hi, rfl⟩ := mem_map.mp ha
        obtain ⟨j, rfl⟩ := exists_castAdd i hi
        rw [tx_univ_erase] at htS
        obtain ⟨u, hu, rfl⟩ := subset_map_iff.mp htS
        have hsu : tauX ⊆ u := (map_subset_map).mp hτt
        have hc' : #u = 4 := by simpa [card_map] using hc
        obtain ⟨x, rfl⟩ := tetT_of j u hu hsu hc'
        exact ⟨x, rfl⟩
    · exact Or.inl ⟨ht, hτt⟩
  · rintro (⟨ht, -⟩ | ⟨x, rfl⟩)
    · exact ht
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ x := by revert x; decide
      refine mem_faces.mpr ⟨tx e (univ.erase (Fin.castAdd 3 i)), ?_, ?_, ?_⟩
      · rw [← tx_univ_erase]
        exact mem_move.mpr (Or.inr ⟨e (Fin.castAdd 3 i), mem_map_of_mem _ (castAdd_mem_sigX i), rfl⟩)
      · exact map_subset_map.mpr (tetT_sub x i hi)
      · simp [tx, card_map, card_tetT]

end Decomposition

/-- Forcing in a complex is forcing by its tetrahedra. -/
theorem forces_iff_forcesIn (K : Complex4 V) (U T : Finset (Finset V)) :
    Forces K U T ↔ ForcesIn K.tets U T := by
  constructor
  · intro h
    induction h with
    | done h => exact .done h
    | step t f ht hf hg _ ih => exact .step t f ht hf hg ih
  · intro h
    induction h with
    | done h => exact .done h
    | step t f ht hf hg _ ih => exact .step t f ht hf hg ih

/-- **Forcing after a 3-3 move.** Let `K → K'` be a 3-3 move that replaces the triangle `σ` by `τ`,
and `T` a set of triangles of `K` not containing `σ`. If `T` forces every triangle of `K`, then `T`
forces every triangle of `K'` if and only if the closure of `T` under the tetrahedra that do not
contain `σ` already reaches every triangle of `K` other than `σ`. -/
theorem forces_move33_iff (h : K.IsMove σ τ) (hσ : #σ = 3) {T : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hσT : σ ∉ T) (hF : Forces K K.tris T) :
    Forces (K.move h) (K.move h).tris T ↔
      ForcesIn (K.tets.filter fun t => ¬ σ ⊆ t) (K.tris.erase σ) T := by
  obtain ⟨e, hσe, hτe⟩ := exists_embedding h hσ
  subst hσe hτe
  have hSj : ∀ j : Fin 3, tx e (univ.erase (Fin.natAdd 3 j)) ∈ K.simps := fun j => by
    rw [← tx_univ_erase]; exact h.mem _ (mem_map_of_mem _ (natAdd_mem_tauX j))
  have hRi : ∀ i : Fin 3, tx e (univ.erase (Fin.castAdd 3 i)) ∈ (K.move h).simps := fun i => by
    rw [← tx_univ_erase]
    exact mem_move.mpr (Or.inr ⟨e (Fin.castAdd 3 i), mem_map_of_mem _ (castAdd_mem_sigX i), rfl⟩)
  have hcσ : #(tx e sigX) = 3 := hσ
  have hcτ : #(tx e tauX) = 3 := card_tau h hσ
  have hσtri : tx e sigX ∈ K.tris :=
    mem_faces.mpr ⟨_, hSj 0, map_subset_map.mpr sigX_sub, hcσ⟩
  have hτtri : tx e tauX ∈ (K.move h).tris :=
    mem_faces.mpr ⟨_, hRi 0, map_subset_map.mpr tauX_sub, hcτ⟩
  set P0 := K.tets.filter fun t => ¬ tx e sigX ⊆ t with hP0
  set C := K.tris.erase (tx e sigX) with hC
  have hKtris : K.tris = insert (tx e sigX) C := (insert_erase hσtri).symm
  have hnσ : ∀ f ∈ K.tris, f ≠ tx e sigX → ¬ tx e sigX ⊆ f := fun f hf hne hs =>
    hne (eq_of_subset_of_card_le hs (by rw [hcσ, (mem_faces.mp hf).choose_spec.2.2])).symm
  have hnτ : ∀ f ∈ (K.move h).tris, f ≠ tx e tauX → ¬ tx e tauX ⊆ f := fun f hf hne hs =>
    hne (eq_of_subset_of_card_le hs (by rw [hcτ, (mem_faces.mp hf).choose_spec.2.2])).symm
  have hK'tris : (K.move h).tris = insert (tx e tauX) C := by
    ext f
    constructor
    · intro hf
      by_cases hτf : tx e tauX ⊆ f
      · exact (not_not.mp fun hne => hnτ f hf hne hτf) ▸ mem_insert_self _ _
      · obtain ⟨hfK, hσf⟩ := sub_face_back h hf hτf
        exact mem_insert_of_mem (mem_erase.mpr ⟨fun hfs => hσf (hfs ▸ subset_rfl), hfK⟩)
    · intro hf
      rcases mem_insert.mp hf with rfl | hf
      · exact hτtri
      · obtain ⟨hne, hfK⟩ := mem_erase.mp hf
        exact (sub_face h hfK (hnσ f hfK hne)).1
  have hP0' : (K.move h).tets.filter (fun t => ¬ tx e tauX ⊆ t) = P0 := by
    ext t
    simp only [mem_filter, hP0]
    constructor
    · rintro ⟨ht, hτt⟩
      obtain ⟨h1, h2⟩ := sub_face_back h ht hτt
      exact ⟨h1, h2⟩
    · rintro ⟨ht, hσt⟩
      obtain ⟨h1, h2⟩ := sub_face h ht hσt
      exact ⟨h1, h2⟩
  have hKt : K.tets = P0 ∪ univ.image fun k => tx e (tetS k) := tets_before e h
  have hK't : (K.move h).tets = P0 ∪ univ.image fun x => tx e (tetT x) := by
    rw [← hP0']; exact tets_after e h
  have hCt : ∀ t ∈ P0, ∀ g ∈ t.powersetCard 3, g ∈ C := by
    intro t ht g hg
    obtain ⟨htK, hσt⟩ := mem_filter.mp ht
    obtain ⟨hgt, hgc⟩ := mem_powersetCard.mp hg
    obtain ⟨S, hS, htS, -⟩ := mem_faces.mp htK
    exact mem_erase.mpr ⟨fun hgs => hσt (hgs ▸ hgt),
      mem_faces.mpr ⟨S, hS, hgt.trans htS, hgc⟩⟩
  have hσC : tx e sigX ∉ C := fun hh => (mem_erase.mp hh).1 rfl
  have hτC : tx e tauX ∉ C := fun hh => by
    obtain ⟨S, hS, hτS, -⟩ := mem_faces.mp (mem_erase.mp hh).2
    exact h.fresh S hS hτS
  have hcom : ∀ p q, tx e (tetC p q) ∈ P0 := fun p q =>
    mem_filter.mpr ⟨mem_faces.mpr ⟨_, hSj q, map_subset_map.mpr (tetC_sub p q),
      by simp [tx, card_map, card_tetC]⟩,
      fun hs => not_sig_tetC p q (map_subset_map.mp hs)⟩
  have hmixM : ∀ k p, tx e (mX k p) ∈ C := fun k p => by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ k := by revert k; decide
    exact mem_erase.mpr ⟨fun hh => mX_ne_sigX k p ((tx_inj e).mp hh),
      mem_faces.mpr ⟨_, hSj j, map_subset_map.mpr (mX_sub k p j hj), by simp [tx, card_map, card_mX]⟩⟩
  have hmixN : ∀ x q, tx e (nX x q) ∈ C := fun x q =>
    mem_erase.mpr ⟨fun hh => nX_ne_sigX x q ((tx_inj e).mp hh), mem_faces.mpr ⟨_, hSj q, map_subset_map.mpr (nX_sub x q),
      by simp [tx, card_map, card_nX]⟩⟩
  have hTC : T ⊆ C := fun f hf => mem_erase.mpr ⟨fun hh => hσT (hh ▸ hf), hT hf⟩
  have hF1 : ForcesIn (P0 ∪ univ.image fun k => tx e (tetS k)) (insert (tx e sigX) C) T := by
    rw [← hKt, ← hKtris]; exact (forces_iff_forcesIn K _ _).mp hF
  have e2 : Forces (K.move h) (K.move h).tris T ↔
      ForcesIn (P0 ∪ univ.image fun x => tx e (tetT x)) (insert (tx e tauX) C) T := by
    rw [forces_iff_forcesIn, hK't, hK'tris]
  rw [e2]
  constructor
  · intro hF2
    by_contra hnot
    rcases forcing_dichotomy e P0 C T hCt hσC hτC hcom hTC hnot with hh | hh
    · exact hh hF1
    · exact hh hF2
  · exact fun hS => forces_tau_of_common e P0 C T hmixN hS

end Complex

end Forcing33

end Lightlike.SpinFoam
