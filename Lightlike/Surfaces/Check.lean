import Lightlike.Surfaces.Basic

/-!
# Checking finite chains of 2D moves inside a larger surface

Many steps of the classification replace a small region of a surface by another one with the same
boundary. The region and the replacement are concrete complexes on natural-number labels, and the
chain of moves between them is found by computer (`scripts/pl/surf_search.py`). This file checks
such a chain once and for all: `checkChain B S X ms` runs the moves `ms` on `X`, checking each one,
and `checkChain_sound` lifts every checked chain into any surrounding complex `A`, through any
embedding `f` of the labels.

The labels in `B` are the **boundary** labels; `f` sends the others to vertices outside `A`. The
pairs in `S` are pairs of boundary labels whose images lie in no triangle of `A`. A move is
accepted only if every edge it flips or creates has a non-boundary endpoint or is a pair of `S`,
and every triangle it creates with three boundary vertices contains such a pair. Then no triangle
of `A` interferes, and the move lifts (`Move2` on `A ∪ f(K)`).
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

/-! ## Moves on concrete complexes -/

/-- A 2D move on a complex with natural-number labels: subdivide the triangle `bcd` by `x`; flip the
edge `bc` (triangles `bcd`, `bce`) to `de`; or remove `x`, whose triangles are `bcx`, `cdx`, `bdx`,
replacing them by `bcd`. -/
inductive Mv
  | sub (b c d x : ℕ)
  | flip (b c d e : ℕ)
  | unsub (b c d x : ℕ)
  deriving DecidableEq

/-- The complex after subdividing `bcd` by `x` (as in `Move2.sub13`). -/
def subRes {V : Type*} [DecidableEq V] (K : Finset (Finset V)) (b c d x : V) :
    Finset (Finset V) :=
  insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (K.erase {b, c, d})))

/-- The complex after flipping `bc` to `de` (as in `Move2.flip22`). -/
def flipRes {V : Type*} [DecidableEq V] (K : Finset (Finset V)) (b c d e : V) :
    Finset (Finset V) :=
  insert {b, d, e} (insert {c, d, e} ((K.erase {b, c, d}).erase {b, c, e}))

/-- The complex before subdividing `bcd` by `x`: remove the three triangles at `x`, add `bcd`. -/
def unsubRes (K : Finset (Finset ℕ)) (b c d x : ℕ) : Finset (Finset ℕ) :=
  insert {b, c, d} (((K.erase {b, c, x}).erase {c, d, x}).erase {b, d, x})

/-- A pair of labels is **safe**: a non-boundary label, or a listed pair. -/
def Safe (B : Finset ℕ) (S : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  u ∉ B ∨ v ∉ B ∨ (u, v) ∈ S ∨ (v, u) ∈ S

instance (B : Finset ℕ) (S : List (ℕ × ℕ)) (u v : ℕ) : Decidable (Safe B S u v) := by
  unfold Safe; infer_instance

/-- The conditions under which a subdivision is accepted. -/
def OkSub (B : Finset ℕ) (K : Finset (Finset ℕ)) (b c d x : ℕ) : Prop :=
  b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ {b, c, d} ∈ K ∧ x ∉ verts2 K ∧ x ∉ B

/-- The conditions under which a flip is accepted. -/
def OkFlip (B : Finset ℕ) (S : List (ℕ × ℕ)) (K : Finset (Finset ℕ)) (b c d e : ℕ) : Prop :=
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ {b, c, d} ∈ K ∧ {b, c, e} ∈ K ∧
    (∀ τ ∈ K, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e}) ∧ (∀ τ ∈ K, ¬ {d, e} ⊆ τ) ∧
    Safe B S b c ∧ Safe B S d e

/-- The conditions under which a removal is accepted. -/
def OkUnsub (B : Finset ℕ) (S : List (ℕ × ℕ)) (K : Finset (Finset ℕ)) (b c d x : ℕ) : Prop :=
  b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ x ∉ verts2 (unsubRes K b c d x) ∧
    ({b, c, d} : Finset ℕ) ∉ ((K.erase {b, c, x}).erase {c, d, x}).erase {b, d, x} ∧
    subRes (unsubRes K b c d x) b c d x = K ∧ x ∉ B ∧
    (Safe B S b c ∨ Safe B S c d ∨ Safe B S b d)

instance (B : Finset ℕ) (K : Finset (Finset ℕ)) (b c d x : ℕ) : Decidable (OkSub B K b c d x) := by
  unfold OkSub; infer_instance

instance (B : Finset ℕ) (S : List (ℕ × ℕ)) (K : Finset (Finset ℕ)) (b c d e : ℕ) :
    Decidable (OkFlip B S K b c d e) := by
  unfold OkFlip; infer_instance

instance (B : Finset ℕ) (S : List (ℕ × ℕ)) (K : Finset (Finset ℕ)) (b c d x : ℕ) :
    Decidable (OkUnsub B S K b c d x) := by
  unfold OkUnsub; infer_instance

/-- One checked move: the resulting complex, or `none` if the move is not accepted. -/
def stepMv (B : Finset ℕ) (S : List (ℕ × ℕ)) (K : Finset (Finset ℕ)) :
    Mv → Option (Finset (Finset ℕ))
  | .sub b c d x => if OkSub B K b c d x then some (subRes K b c d x) else none
  | .flip b c d e => if OkFlip B S K b c d e then some (flipRes K b c d e) else none
  | .unsub b c d x => if OkUnsub B S K b c d x then some (unsubRes K b c d x) else none

/-- A checked chain of moves: the final complex, or `none` if some move is not accepted. -/
def checkChain (B : Finset ℕ) (S : List (ℕ × ℕ)) : Finset (Finset ℕ) → List Mv →
    Option (Finset (Finset ℕ))
  | K, [] => some K
  | K, m :: ms => (stepMv B S K m).bind fun K' => checkChain B S K' ms

/-! ## Lifting checked moves -/

variable {V : Type*} [DecidableEq V]

/-- A concrete complex placed in `V` by an embedding of the labels. -/
def liftK (f : ℕ ↪ V) (K : Finset (Finset ℕ)) : Finset (Finset V) := K.image (Finset.map f)

/-- The **context conditions**: non-boundary labels go outside the surrounding complex `A`, and the
listed pairs lie in no triangle of `A`. -/
structure Ctx (A : Finset (Finset V)) (f : ℕ ↪ V) (B : Finset ℕ) (S : List (ℕ × ℕ)) : Prop where
  fresh : ∀ n, n ∉ B → f n ∉ verts2 A
  safe : ∀ p ∈ S, ∀ t ∈ A, ¬ ({f p.1, f p.2} : Finset V) ⊆ t

section lift

variable {A : Finset (Finset V)} {f : ℕ ↪ V} {B : Finset ℕ} {S : List (ℕ × ℕ)}

lemma Ctx.not_subset (hC : Ctx A f B S) {u v : ℕ} (h : Safe B S u v) :
    ∀ t ∈ A, ¬ ({f u, f v} : Finset V) ⊆ t := by
  intro t ht hs
  rcases h with h | h | h | h
  · exact hC.fresh u h (mem_verts2.mpr ⟨t, ht, hs (by simp)⟩)
  · exact hC.fresh v h (mem_verts2.mpr ⟨t, ht, hs (by simp)⟩)
  · exact hC.safe _ h t ht hs
  · exact hC.safe _ h t ht (by rw [pair_comm]; exact hs)

lemma map_tri (a b c : ℕ) : ({a, b, c} : Finset ℕ).map f = {f a, f b, f c} := by simp

lemma map_pair (a b : ℕ) : ({a, b} : Finset ℕ).map f = {f a, f b} := by simp

set_option linter.unusedSimpArgs false in
lemma Ctx.tri_notMem (hC : Ctx A f B S) {a b c : ℕ}
    (h : Safe B S a b ∨ Safe B S b c ∨ Safe B S a c) : ({f a, f b, f c} : Finset V) ∉ A := by
  intro hm
  rcases h with h | h | h
  · exact hC.not_subset h _ hm (by simp [insert_subset_iff])
  · exact hC.not_subset h _ hm (by simp [insert_subset_iff])
  · exact hC.not_subset h _ hm (by simp [insert_subset_iff])

lemma liftK_insert (K : Finset (Finset ℕ)) (t : Finset ℕ) :
    liftK f (insert t K) = insert (t.map f) (liftK f K) := image_insert _ _ _

lemma liftK_erase (K : Finset (Finset ℕ)) (t : Finset ℕ) :
    liftK f (K.erase t) = (liftK f K).erase (t.map f) :=
  image_erase (map_injective f) _ _

lemma mem_liftK {K : Finset (Finset ℕ)} {s : Finset V} :
    s ∈ liftK f K ↔ ∃ t ∈ K, t.map f = s := by simp [liftK]

lemma map_mem_liftK {K : Finset (Finset ℕ)} {t : Finset ℕ} : t.map f ∈ liftK f K ↔ t ∈ K := by
  rw [mem_liftK]
  exact ⟨fun ⟨u, hu, e⟩ => map_injective f e ▸ hu, fun h => ⟨t, h, rfl⟩⟩

lemma liftK_subRes (K : Finset (Finset ℕ)) (b c d x : ℕ) :
    liftK f (subRes K b c d x) = subRes (liftK f K) (f b) (f c) (f d) (f x) := by
  simp only [subRes, liftK_insert, liftK_erase, map_tri]

lemma liftK_flipRes (K : Finset (Finset ℕ)) (b c d e : ℕ) :
    liftK f (flipRes K b c d e) = flipRes (liftK f K) (f b) (f c) (f d) (f e) := by
  simp only [flipRes, liftK_insert, liftK_erase, map_tri]

lemma union_erase_of_notMem {M : Finset (Finset V)} {t : Finset V} (ht : t ∉ A) :
    (A ∪ M).erase t = A ∪ M.erase t := by
  ext s
  simp only [mem_erase, mem_union]
  constructor
  · rintro ⟨hs, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hs, h⟩
  · rintro (h | ⟨hs, h⟩)
    · exact ⟨fun e => ht (e ▸ h), Or.inl h⟩
    · exact ⟨hs, Or.inr h⟩

lemma subRes_union {M : Finset (Finset V)} {b c d x : V} (h : ({b, c, d} : Finset V) ∉ A) :
    subRes (A ∪ M) b c d x = A ∪ subRes M b c d x := by
  simp only [subRes, union_erase_of_notMem h, union_insert]

lemma flipRes_union {M : Finset (Finset V)} {b c d e : V} (h₁ : ({b, c, d} : Finset V) ∉ A)
    (h₂ : ({b, c, e} : Finset V) ∉ A) :
    flipRes (A ∪ M) b c d e = A ∪ flipRes M b c d e := by
  simp only [flipRes, union_erase_of_notMem h₁, union_erase_of_notMem h₂, union_insert]

lemma verts2_union (M N : Finset (Finset V)) : verts2 (M ∪ N) = verts2 M ∪ verts2 N := by
  simp only [verts2, union_biUnion]

lemma notMem_verts2_liftK {K : Finset (Finset ℕ)} {x : ℕ} (hx : x ∉ verts2 K) :
    f x ∉ verts2 (liftK f K) := by
  rw [mem_verts2]
  rintro ⟨s, hs, hxs⟩
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hs
  rw [mem_map'] at hxs
  exact hx (mem_verts2.mpr ⟨t, ht, hxs⟩)

/-- The invariant: no triangle of the region lies in `A`. -/
def Disj (A : Finset (Finset V)) (f : ℕ ↪ V) (K : Finset (Finset ℕ)) : Prop :=
  ∀ t ∈ K, t.map f ∉ A

lemma Ctx.map_notMem_of_fresh (hC : Ctx A f B S) {t : Finset ℕ} {x : ℕ} (hx : x ∈ t)
    (hxB : x ∉ B) : t.map f ∉ A := fun h =>
  hC.fresh x hxB (mem_verts2.mpr ⟨_, h, mem_map_of_mem f hx⟩)

/-- **A checked subdivision lifts.** -/
lemma lift_sub (hC : Ctx A f B S) {K : Finset (Finset ℕ)} (hD : Disj A f K) {b c d x : ℕ}
    (h : OkSub B K b c d x) :
    Move2 (A ∪ liftK f K) (A ∪ liftK f (subRes K b c d x)) ∧ Disj A f (subRes K b c d x) := by
  obtain ⟨hbc, hbd, hcd, hτ, hx, hxB⟩ := h
  have hbcd : ({f b, f c, f d} : Finset V) ∉ A := by rw [← map_tri]; exact hD _ hτ
  refine ⟨?_, ?_⟩
  · have hm := Move2.sub13 (f.injective.ne hbc) (f.injective.ne hbd) (f.injective.ne hcd)
      (mem_union_right A (by rw [← map_tri]; exact map_mem_liftK.mpr hτ))
      (x := f x) (by
        rw [verts2_union, mem_union, not_or]
        exact ⟨hC.fresh x hxB, notMem_verts2_liftK hx⟩)
    have e := subRes_union (M := liftK f K) (x := f x) hbcd
    rw [liftK_subRes, ← e]
    exact hm
  · intro t ht
    simp only [subRes, mem_insert, mem_erase] at ht
    rcases ht with rfl | rfl | rfl | ⟨-, ht⟩
    · exact hC.map_notMem_of_fresh (by simp) hxB
    · exact hC.map_notMem_of_fresh (by simp) hxB
    · exact hC.map_notMem_of_fresh (by simp) hxB
    · exact hD t ht

set_option linter.unusedSimpArgs false in
/-- **A checked flip lifts.** -/
lemma lift_flip (hC : Ctx A f B S) {K : Finset (Finset ℕ)} (hD : Disj A f K) {b c d e : ℕ}
    (h : OkFlip B S K b c d e) :
    Move2 (A ∪ liftK f K) (A ∪ liftK f (flipRes K b c d e)) ∧ Disj A f (flipRes K b c d e) := by
  obtain ⟨hbc, hbd, hbe, hcd, hce, hde, h₁, h₂, hstar, hfresh, hsbc, hsde⟩ := h
  have n1 : ({f b, f c, f d} : Finset V) ∉ A := by rw [← map_tri]; exact hD _ h₁
  have n2 : ({f b, f c, f e} : Finset V) ∉ A := by rw [← map_tri]; exact hD _ h₂
  have hstar' : ∀ τ ∈ A ∪ liftK f K, ({f b, f c} : Finset V) ⊆ τ →
      τ = {f b, f c, f d} ∨ τ = {f b, f c, f e} := by
    intro τ hτ hsub
    rcases mem_union.mp hτ with hτ | hτ
    · exact absurd hsub (hC.not_subset hsbc τ hτ)
    · obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hτ
      have : ({b, c} : Finset ℕ) ⊆ t := by rw [← map_subset_map (f := f), map_pair]; exact hsub
      rcases hstar t ht this with rfl | rfl
      · exact Or.inl (map_tri _ _ _)
      · exact Or.inr (map_tri _ _ _)
  have hfresh' : ∀ τ ∈ A ∪ liftK f K, ¬ ({f d, f e} : Finset V) ⊆ τ := by
    intro τ hτ hsub
    rcases mem_union.mp hτ with hτ | hτ
    · exact hC.not_subset hsde τ hτ hsub
    · obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hτ
      exact hfresh t ht (by rw [← map_subset_map (f := f), map_pair]; exact hsub)
  refine ⟨?_, ?_⟩
  · have hm := Move2.flip22 (f.injective.ne hbc) (f.injective.ne hbd) (f.injective.ne hbe)
      (f.injective.ne hcd) (f.injective.ne hce) (f.injective.ne hde)
      (mem_union_right A (by rw [← map_tri]; exact map_mem_liftK.mpr h₁))
      (mem_union_right A (by rw [← map_tri]; exact map_mem_liftK.mpr h₂)) hstar' hfresh'
    rw [liftK_flipRes, ← flipRes_union n1 n2]
    exact hm
  · intro t ht
    simp only [flipRes, mem_insert, mem_erase] at ht
    rcases ht with rfl | rfl | ⟨-, -, ht⟩
    · rw [map_tri]
      intro hm
      exact hC.not_subset hsde _ hm (by simp [insert_subset_iff])
    · rw [map_tri]
      intro hm
      exact hC.not_subset hsde _ hm (by simp [insert_subset_iff])
    · exact hD t ht

/-- **A checked removal lifts** (as the subdivision it undoes). -/
lemma lift_unsub (hC : Ctx A f B S) {K : Finset (Finset ℕ)} (hD : Disj A f K) {b c d x : ℕ}
    (h : OkUnsub B S K b c d x) :
    Move2 (A ∪ liftK f (unsubRes K b c d x)) (A ∪ liftK f K) ∧
      Disj A f (unsubRes K b c d x) := by
  obtain ⟨hbc, hbd, hcd, hx, -, heq, hxB, hsafe⟩ := h
  have hbcd : ({f b, f c, f d} : Finset V) ∉ A := hC.tri_notMem hsafe
  refine ⟨?_, ?_⟩
  · have hm := Move2.sub13 (f.injective.ne hbc) (f.injective.ne hbd) (f.injective.ne hcd)
      (mem_union_right A (show ({f b, f c, f d} : Finset V) ∈ liftK f (unsubRes K b c d x) by
        rw [← map_tri]; exact map_mem_liftK.mpr (by rw [unsubRes]; exact mem_insert_self _ _)))
      (x := f x) (by
        rw [verts2_union, mem_union, not_or]
        exact ⟨hC.fresh x hxB, notMem_verts2_liftK hx⟩)
    have e := subRes_union (M := liftK f (unsubRes K b c d x)) (x := f x) hbcd
    conv_rhs => rw [← heq]
    rw [liftK_subRes, ← e]
    exact hm
  · intro t ht
    rw [unsubRes, mem_insert] at ht
    rcases ht with rfl | ht
    · rw [map_tri]; exact hbcd
    · exact hD t (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase ht)))

/-- **Soundness of the checker**: a chain of moves accepted by `checkChain` from `X` to `Y` is a
chain of 2D bistellar moves from `A ∪ f(X)` to `A ∪ f(Y)`, for every surrounding complex `A` and
embedding `f` satisfying the context conditions, provided no triangle of `f(X)` lies in `A`. -/
theorem checkChain_sound (hC : Ctx A f B S) : ∀ (ms : List Mv) {X Y : Finset (Finset ℕ)},
    Disj A f X → checkChain B S X ms = some Y →
      Relation.EqvGen Move2 (A ∪ liftK f X) (A ∪ liftK f Y)
  | [], X, Y, _, h => by
    simp only [checkChain, Option.some.injEq] at h
    subst h
    exact .refl _
  | m :: ms, X, Y, hD, h => by
    simp only [checkChain, Option.bind_eq_some_iff] at h
    obtain ⟨K', hK', hrest⟩ := h
    cases m with
    | sub b c d x =>
      simp only [stepMv] at hK'
      split_ifs at hK' with hok
      cases hK'
      obtain ⟨hm, hD'⟩ := lift_sub hC hD hok
      exact (Relation.EqvGen.rel _ _ hm).trans _ _ _ (checkChain_sound hC ms hD' hrest)
    | flip b c d e =>
      simp only [stepMv] at hK'
      split_ifs at hK' with hok
      cases hK'
      obtain ⟨hm, hD'⟩ := lift_flip hC hD hok
      exact (Relation.EqvGen.rel _ _ hm).trans _ _ _ (checkChain_sound hC ms hD' hrest)
    | unsub b c d x =>
      simp only [stepMv] at hK'
      split_ifs at hK' with hok
      cases hK'
      obtain ⟨hm, hD'⟩ := lift_unsub hC hD hok
      exact (Relation.EqvGen.rel _ _ hm).symm.trans _ _ _ (checkChain_sound hC ms hD' hrest)

end lift

end Lightlike.Surfaces
