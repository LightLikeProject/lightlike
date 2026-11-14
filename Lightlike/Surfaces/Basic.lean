import Lightlike.PonzanoRegge.SphereRecognition

/-!
# Closed combinatorial surfaces and their orientations

A **closed combinatorial surface** (`IsSurface`) is a nonempty finite set of triangles in which every
edge lies in exactly two triangles, every vertex link is connected (with closedness, a cycle), and
the 1-skeleton is connected. These are the intrinsic conditions of `IsSurfaceSphere`
(`Lightlike/PonzanoRegge/SphereConverse.lean`) without the Euler characteristic.

An **orientation** (`IsOrientation`) is a fundamental class: an alternating function `o` of ordered
triples of vertices, equal to `±1` on the orderings of each triangle and `0` elsewhere, whose
boundary vanishes, `∑_w o u v w = 0` for all `u, v`. On a closed surface this says exactly that the
two triangles at each edge induce opposite directions on it.

* `Move2.isSurface_iff`: 2D bistellar moves preserve closed surfaces, in both directions.
* `Move2.isOrientable_iff`: they preserve orientability, in both directions. The new orientation
  is the old one plus a multiple of a chain with zero boundary (`edir` sums cancel by
  antisymmetry), so the proof is algebra.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Closed surfaces -/

/-- A **closed combinatorial surface**: a nonempty set of triangles, every edge in exactly two of
them, every vertex link connected, and the 1-skeleton connected. -/
structure IsSurface (L : Finset (Finset V)) : Prop where
  nonempty : L.Nonempty
  card : IsTri2 L
  closed : IsClosed2 L
  link : IsLinkConn L
  connected : IsConnected2 L

/-- The two complexes of a 2D move are nonempty. -/
lemma Move2.nonempty_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    L.Nonempty ↔ L'.Nonempty := by
  cases h with
  | sub13 _ _ _ hτ _ => exact ⟨fun _ => ⟨_, mem_insert_self _ _⟩, fun _ => ⟨_, hτ⟩⟩
  | flip22 _ _ _ _ _ _ h₁ _ _ _ => exact ⟨fun _ => ⟨_, mem_insert_self _ _⟩, fun _ => ⟨_, h₁⟩⟩

/-- **A 2D bistellar move keeps closed surfaces, in both directions.** -/
theorem Move2.isSurface_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    IsSurface L ↔ IsSurface L' := by
  constructor
  · intro hS
    exact ⟨(Move2.nonempty_iff h).mp hS.nonempty, h.tri_iff.mp hS.card, h.closed_iff.mp hS.closed,
      h.linkConn_iff.mp hS.link, h.connected_iff.mp hS.connected⟩
  · intro hS
    exact ⟨(Move2.nonempty_iff h).mpr hS.nonempty, h.tri_iff.mpr hS.card, h.closed_iff.mpr hS.closed,
      h.linkConn_iff.mpr hS.link, h.connected_iff.mpr hS.connected⟩

/-- Complexes related by 2D bistellar moves are surfaces together. -/
theorem isSurface_iff_of_eqvGen {L L' : Finset (Finset V)} (h : Relation.EqvGen Move2 L L') :
    IsSurface L ↔ IsSurface L' := by
  induction h with
  | rel _ _ h => exact Move2.isSurface_iff h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An intrinsic triangulated 2-sphere is a closed surface. -/
theorem IsSurfaceSphere.isSurface {L : Finset (Finset V)} (hS : IsSurfaceSphere L) :
    IsSurface L where
  nonempty := by
    rcases L.eq_empty_or_nonempty with h | h
    · have := hS.euler
      simp [h, euler2, verts2, edges2] at this
    · exact h
  card := hS.card
  closed := hS.closed
  link := hS.link
  connected := hS.connected

/-- **The closed surfaces with Euler characteristic `2` are the intrinsic 2-spheres.** -/
theorem isSurfaceSphere_iff {L : Finset (Finset V)} :
    IsSurfaceSphere L ↔ IsSurface L ∧ euler2 L = 2 :=
  ⟨fun h => ⟨IsSurfaceSphere.isSurface h, h.euler⟩, fun ⟨h, he⟩ => ⟨h.card, h.closed, h.link, h.connected, he⟩⟩

/-! ## Oriented triangles -/

/-- The indicator of the ordered triple `(p, q, r)`. -/
def ind (p q r x y z : V) : ℤ := if x = p ∧ y = q ∧ z = r then 1 else 0

/-- The **oriented triangle** `(a, b, c)` as an alternating function of ordered triples: `1` on the
rotations of `(a, b, c)`, `-1` on those of `(b, a, c)`. -/
def otri (a b c x y z : V) : ℤ :=
  ind a b c x y z + ind b c a x y z + ind c a b x y z - ind b a c x y z - ind c b a x y z -
    ind a c b x y z

/-- The **directed edge** `(p, q)` as an antisymmetric function of ordered pairs. -/
def edir (p q u v : V) : ℤ := (if u = p ∧ v = q then 1 else 0) - (if u = q ∧ v = p then 1 else 0)

lemma ind_rot (p q r x y z : V) : ind p q r y z x = ind r p q x y z := by
  simp only [ind]
  congr 1
  exact propext ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₁, h₂⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₃, h₁⟩⟩

lemma ind_swap (p q r x y z : V) : ind p q r y x z = ind q p r x y z := by
  simp only [ind]
  congr 1
  exact propext ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩⟩

lemma otri_rot (a b c x y z : V) : otri a b c y z x = otri a b c x y z := by
  simp only [otri]
  rw [ind_rot a b c x y z, ind_rot b c a x y z, ind_rot c a b x y z, ind_rot b a c x y z,
    ind_rot c b a x y z, ind_rot a c b x y z]
  ring

lemma otri_swap (a b c x y z : V) : otri a b c y x z = - otri a b c x y z := by
  simp only [otri]
  rw [ind_swap a b c x y z, ind_swap b c a x y z, ind_swap c a b x y z, ind_swap b a c x y z,
    ind_swap c b a x y z, ind_swap a c b x y z]
  ring

lemma edir_swap (p q u v : V) : edir q p u v = - edir p q u v := by
  simp only [edir]
  ring

lemma sum_ind {S : Finset V} (p q r u v : V) :
    ∑ w ∈ S, ind p q r u v w = if u = p ∧ v = q ∧ r ∈ S then 1 else 0 := by
  have : ∀ w, ind p q r u v w = if r = w then (if u = p ∧ v = q then 1 else 0) else 0 := by
    intro w
    simp only [ind]
    by_cases h : r = w
    · subst h; simp
    · simp only [h, ite_false]
      rw [ite_eq_right_iff]
      intro h'
      exact absurd h'.2.2.symm h
  simp only [this, sum_ite_eq]
  by_cases hr : r ∈ S <;> by_cases huv : u = p ∧ v = q <;> simp [hr, huv]

/-- The boundary of an oriented triangle: its three directed edges. -/
lemma sum_otri {S : Finset V} {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (u v : V) :
    ∑ w ∈ S, otri a b c u v w = edir a b u v + edir b c u v + edir c a u v := by
  simp only [otri, sum_add_distrib, sum_sub_distrib, sum_ind, ha, hb, hc, and_true, edir]
  ring

/-- An oriented triangle vanishes off its own vertex set. -/
lemma otri_eq_zero {a b c x y z : V} (h : ({x, y, z} : Finset V) ≠ {a, b, c}) :
    otri a b c x y z = 0 := by
  have key : ∀ p q r : V, ({p, q, r} : Finset V) = {a, b, c} → ind p q r x y z = 0 := by
    intro p q r hpqr
    simp only [ind, ite_eq_right_iff, one_ne_zero, imp_false]
    rintro ⟨rfl, rfl, rfl⟩
    exact h hpqr
  have e1 : ({b, c, a} : Finset V) = {a, b, c} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e2 : ({c, a, b} : Finset V) = {a, b, c} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e3 : ({b, a, c} : Finset V) = {a, b, c} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e4 : ({c, b, a} : Finset V) = {a, b, c} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e5 : ({a, c, b} : Finset V) = {a, b, c} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  simp only [otri, key a b c rfl, key b c a e1, key c a b e2, key b a c e3, key c b a e4,
    key a c b e5]
  ring

set_option linter.unusedSimpArgs false in
/-- An alternating function on the orderings of a triangle is determined by one value. -/
lemma eq_otri_mul {o : V → V → V → ℤ} (hrot : ∀ x y z, o y z x = o x y z)
    (hswap : ∀ x y z, o y x z = - o x y z) {a b c x y z : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h : ({x, y, z} : Finset V) = {a, b, c}) :
    o x y z = otri a b c x y z * o a b c := by
  have h3 : #({x, y, z} : Finset V) = 3 := by
    rw [h, card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  obtain ⟨hxy, hxz, hyz⟩ := tri_ne h3
  have hx : x ∈ ({a, b, c} : Finset V) := h ▸ by simp
  have hy : y ∈ ({a, b, c} : Finset V) := h ▸ by simp
  have hz : z ∈ ({a, b, c} : Finset V) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at hx hy hz
  have r1 := hrot a b c
  have r2 := hrot b c a
  have s1 := hswap a b c
  have s2 := hswap b c a
  have s3 := hswap c a b
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | exact absurd rfl hxz
    | exact absurd rfl hyz
    | (simp only [otri, ind, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, and_self, and_true,
        true_and, and_false, false_and, ite_true, ite_false]
       linarith)

/-! ## Orientations -/

/-- An **orientation** of `L`: an alternating function of ordered triples, `±1` on the orderings of
every triangle of `L` and `0` off `L`, with zero boundary. -/
structure IsOrientation (L : Finset (Finset V)) (o : V → V → V → ℤ) : Prop where
  rot : ∀ x y z, o y z x = o x y z
  swap : ∀ x y z, o y x z = - o x y z
  supp : ∀ x y z, o x y z ≠ 0 → ({x, y, z} : Finset V) ∈ L
  unit : ∀ x y z, ({x, y, z} : Finset V) ∈ L → o x y z = 1 ∨ o x y z = -1
  cycle : ∀ u v, ∑ w ∈ verts2 L, o u v w = 0

/-- `L` is **orientable**: it has an orientation. -/
def IsOrientable (L : Finset (Finset V)) : Prop := ∃ o, IsOrientation L o

namespace IsOrientation

variable {L : Finset (Finset V)} {o : V → V → V → ℤ}

lemma eq_zero_of_notMem (ho : IsOrientation L o) {x y z : V}
    (h : ({x, y, z} : Finset V) ∉ L) : o x y z = 0 := by
  by_contra h'
  exact h (ho.supp x y z h')

lemma eq_zero_of_notMem_verts (ho : IsOrientation L o) {x y z : V} (hz : z ∉ verts2 L) :
    o x y z = 0 :=
  ho.eq_zero_of_notMem fun h => hz (mem_verts2.mpr ⟨_, h, by simp⟩)

lemma perm (ho : IsOrientation L o) {a b c x y z : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ({x, y, z} : Finset V) = {a, b, c}) : o x y z = otri a b c x y z * o a b c :=
  eq_otri_mul ho.rot ho.swap hab hac hbc h

lemma swap23 (ho : IsOrientation L o) (x y z : V) : o x z y = - o x y z := by
  rw [ho.rot y x z, ho.swap x y z]

/-- At an edge `uv` whose only triangles are `uvp` and `uvq`, the two values cancel. -/
lemma pair (ho : IsOrientation L o) {u v p q : V} (hpq : p ≠ q) (hp : p ∈ verts2 L)
    (hq : q ∈ verts2 L) (h : ∀ w, ({u, v, w} : Finset V) ∈ L → w = p ∨ w = q) :
    o u v p + o u v q = 0 := by
  have hc := ho.cycle u v
  rwa [← sum_subset (s₁ := {p, q}) (by simp [insert_subset_iff, hp, hq])
    (fun w _ hw => ho.eq_zero_of_notMem fun h' => by
      simp only [mem_insert, mem_singleton, not_or] at hw
      rcases h w h' with rfl | rfl
      · exact hw.1 rfl
      · exact hw.2 rfl), sum_pair hpq] at hc

end IsOrientation

/-- Values on orderings of a triangle: `±1` times `±1`. -/
lemma otri_mul_unit {a b c x y z : V} {s : ℤ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ({x, y, z} : Finset V) = {a, b, c}) (hs : s = 1 ∨ s = -1) :
    s * otri a b c x y z = 1 ∨ s * otri a b c x y z = -1 := by
  have h3 : #({x, y, z} : Finset V) = 3 := by
    rw [h, card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  obtain ⟨hxy, hxz, hyz⟩ := tri_ne h3
  have hx : x ∈ ({a, b, c} : Finset V) := h ▸ by simp
  have hy : y ∈ ({a, b, c} : Finset V) := h ▸ by simp
  have hz : z ∈ ({a, b, c} : Finset V) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at hx hy hz
  rcases hs with rfl | rfl <;>
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | exact absurd rfl hxz
    | exact absurd rfl hyz
    | simp [otri, ind, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

/-- Two triangles with a vertex that only one of them contains are different. -/
lemma ne_tri {p q r a b c : V} (y : V) (hy : y = a ∨ y = b ∨ y = c)
    (hy' : y ≠ p ∧ y ≠ q ∧ y ≠ r) : ({p, q, r} : Finset V) ≠ {a, b, c} := by
  intro h
  have : y ∈ ({p, q, r} : Finset V) := h ▸ by simp [hy]
  simp only [mem_insert, mem_singleton] at this
  rcases this with h' | h' | h' <;> simp_all

/-- A triangle of `L` does not contain a vertex outside `L`. -/
lemma notMem_of_notMem_verts {L : Finset (Finset V)} {t : Finset V} {x : V} (ht : t ∈ L)
    (hx : x ∉ verts2 L) : x ∉ t :=
  fun h => hx (mem_verts2.mpr ⟨t, ht, h⟩)

lemma mem_verts2_of_mem {L : Finset (Finset V)} {a b c : V} (h : ({a, b, c} : Finset V) ∈ L) :
    a ∈ verts2 L ∧ b ∈ verts2 L ∧ c ∈ verts2 L :=
  ⟨mem_verts2.mpr ⟨_, h, by simp⟩, mem_verts2.mpr ⟨_, h, by simp⟩, mem_verts2.mpr ⟨_, h, by simp⟩⟩

/-- Summing over a set with one more point where the function vanishes. -/
lemma sum_verts_insert {S : Finset V} {f : V → ℤ} {x : V} (hx : x ∉ S) (hfx : f x = 0) :
    ∑ w ∈ insert x S, f w = ∑ w ∈ S, f w := by
  rw [sum_insert hx, hfx, zero_add]

/-! ## Subdividing a triangle -/

section sub13

variable {L : Finset (Finset V)} {b c d x : V} {o : V → V → V → ℤ}

/-- An orientation after subdividing `bcd` by `x`: the old one plus `o(b,c,d)` times the
boundary-free chain `bcx + cdx + dbx − bcd`. -/
lemma isOrientation_sub13 (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hτ : {b, c, d} ∈ L)
    (hx : x ∉ verts2 L) (ho : IsOrientation L o) :
    IsOrientation (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d}))))
      (fun p q r => o p q r + o b c d * (otri b c x p q r + otri c d x p q r + otri d b x p q r -
        otri b c d p q r)) := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have edb : ({d, b, x} : Finset V) = {b, d, x} := insert_comm _ _ _
  have hs := ho.unit b c d hτ
  have hnew : ∀ {t : Finset V}, x ∈ t → t ∉ L := fun hxt ht => notMem_of_notMem_verts ht hx hxt
  refine ⟨fun p q r => ?_, fun p q r => ?_, fun p q r h => ?_, fun p q r h => ?_, fun u v => ?_⟩
  · rw [ho.rot, otri_rot b c x p q r, otri_rot c d x p q r, otri_rot d b x p q r,
      otri_rot b c d p q r]
  · rw [ho.swap, otri_swap b c x p q r, otri_swap c d x p q r, otri_swap d b x p q r,
      otri_swap b c d p q r]
    ring
  · simp only [mem_insert, mem_erase]
    by_cases h1 : ({p, q, r} : Finset V) = {b, c, x}
    · exact Or.inl h1
    by_cases h2 : ({p, q, r} : Finset V) = {c, d, x}
    · exact Or.inr (Or.inl h2)
    by_cases h3 : ({p, q, r} : Finset V) = {b, d, x}
    · exact Or.inr (Or.inr (Or.inl h3))
    rw [otri_eq_zero h1, otri_eq_zero h2, otri_eq_zero (edb ▸ h3)] at h
    by_cases h4 : ({p, q, r} : Finset V) = {b, c, d}
    · rw [ho.perm hbc hbd hcd h4] at h
      exact absurd (by ring) h
    · rw [otri_eq_zero h4] at h
      exact Or.inr (Or.inr (Or.inr ⟨h4, ho.supp p q r (by simpa using h)⟩))
  · simp only [mem_insert, mem_erase] at h
    rcases h with h | h | h | ⟨h4, hL⟩
    · rw [ho.eq_zero_of_notMem (h ▸ hnew (by simp)),
        otri_eq_zero (a := c) (b := d) (c := x)
          (by rw [h]; exact ne_tri d (by simp) ⟨hbd.symm, hcd.symm, hxd.symm⟩),
        otri_eq_zero (a := d) (b := b) (c := x)
          (by rw [h]; exact ne_tri d (by simp) ⟨hbd.symm, hcd.symm, hxd.symm⟩),
        otri_eq_zero (a := b) (b := c) (c := d)
          (by rw [h]; exact ne_tri d (by simp) ⟨hbd.symm, hcd.symm, hxd.symm⟩)]
      simpa using otri_mul_unit hbc hxb.symm hxc.symm h hs
    · rw [ho.eq_zero_of_notMem (h ▸ hnew (by simp)),
        otri_eq_zero (a := b) (b := c) (c := x)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hxb.symm⟩),
        otri_eq_zero (a := d) (b := b) (c := x)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hxb.symm⟩),
        otri_eq_zero (a := b) (b := c) (c := d)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hxb.symm⟩)]
      simpa using otri_mul_unit hcd hxc.symm hxd.symm h hs
    · rw [← edb] at h
      rw [ho.eq_zero_of_notMem (h ▸ hnew (by simp)),
        otri_eq_zero (a := b) (b := c) (c := x)
          (by rw [h]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hxc.symm⟩),
        otri_eq_zero (a := c) (b := d) (c := x)
          (by rw [h]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hxc.symm⟩),
        otri_eq_zero (a := b) (b := c) (c := d)
          (by rw [h]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hxc.symm⟩)]
      simpa using otri_mul_unit hbd.symm hxd.symm hxb.symm h hs
    · have hxt : x ∉ ({p, q, r} : Finset V) := notMem_of_notMem_verts hL hx
      simp only [mem_insert, mem_singleton, not_or] at hxt
      rw [otri_eq_zero (a := b) (b := c) (c := x) (ne_tri x (by simp) hxt),
        otri_eq_zero (a := c) (b := d) (c := x) (ne_tri x (by simp) hxt),
        otri_eq_zero (a := d) (b := b) (c := x) (ne_tri x (by simp) hxt), otri_eq_zero h4]
      simpa using ho.unit p q r hL
  · obtain ⟨hb, hc, hd⟩ := mem_verts2_of_mem hτ
    rw [verts2_sub13 hτ, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_add_distrib,
      sum_add_distrib, sum_insert hx, ho.eq_zero_of_notMem_verts hx, zero_add, ho.cycle,
      sum_otri (mem_insert_of_mem hb) (mem_insert_of_mem hc) (mem_insert_self _ _),
      sum_otri (mem_insert_of_mem hc) (mem_insert_of_mem hd) (mem_insert_self _ _),
      sum_otri (mem_insert_of_mem hd) (mem_insert_of_mem hb) (mem_insert_self _ _),
      sum_otri (mem_insert_of_mem hb) (mem_insert_of_mem hc) (mem_insert_of_mem hd),
      edir_swap b x, edir_swap c x, edir_swap d x]
    ring

/-- An orientation before subdividing `bcd` by `x`: the reverse of `isOrientation_sub13`. -/
lemma isOrientation_of_sub13 (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hτ : {b, c, d} ∈ L)
    (hx : x ∉ verts2 L)
    (ho : IsOrientation (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d}))))
      o) :
    IsOrientation L (fun p q r => o p q r + o b c x * (otri b c d p q r - otri b c x p q r -
      otri c d x p q r - otri d b x p q r)) := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have edb : ({d, b, x} : Finset V) = {b, d, x} := insert_comm _ _ _
  have hnew : ∀ {t : Finset V}, x ∈ t → t ∉ L := fun hxt ht => notMem_of_notMem_verts ht hx hxt
  set L' := insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d}))) with hL'
  have mbcx : ({b, c, x} : Finset V) ∈ L' := mem_insert_self _ _
  have mcdx : ({c, d, x} : Finset V) ∈ L' := mem_insert_of_mem (mem_insert_self _ _)
  have mbdx : ({b, d, x} : Finset V) ∈ L' :=
    mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
  -- the triangles of `L'` through `x`
  have hx3 : ∀ {t : Finset V}, t ∈ L' → x ∈ t → t = {b, c, x} ∨ t = {c, d, x} ∨ t = {b, d, x} := by
    intro t ht hxt
    simp only [hL', mem_insert, mem_erase] at ht
    rcases ht with h | h | h | ⟨-, ht⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd ht (hnew hxt)
  have hs := ho.unit b c x mbcx
  -- the values on the three new triangles agree
  have hcx : o c x b + o c x d = 0 := by
    refine ho.pair hbd (mem_verts2_of_mem mbcx).1 (mem_verts2_of_mem mcdx).2.1
      fun w hw => ?_
    rcases hx3 hw (by simp) with h | h | h
    · have : b ∈ ({c, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hbc
      · exact absurd h'.symm hxb
      · exact Or.inl h'.symm
    · have : d ∈ ({c, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h'.symm hcd
      · exact absurd h'.symm hxd
      · exact Or.inr h'.symm
    · have h1 : b ∈ ({c, x, w} : Finset V) := h ▸ by simp
      have h2 : d ∈ ({c, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 hbc
      · exact absurd h1.symm hxb
      rcases h2 with h2 | h2 | h2
      · exact absurd h2.symm hcd
      · exact absurd h2.symm hxd
      · exact absurd (h1.trans h2.symm) hbd
  have hdx : o d x c + o d x b = 0 := by
    refine ho.pair hbc.symm (mem_verts2_of_mem mcdx).1 (mem_verts2_of_mem mbdx).1
      fun w hw => ?_
    rcases hx3 hw (by simp) with h | h | h
    · have h1 : b ∈ ({d, x, w} : Finset V) := h ▸ by simp
      have h2 : c ∈ ({d, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 hbd
      · exact absurd h1.symm hxb
      rcases h2 with h2 | h2 | h2
      · exact absurd h2 hcd
      · exact absurd h2.symm hxc
      · exact absurd (h1.trans h2.symm) hbc
    · have : c ∈ ({d, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hcd
      · exact absurd h'.symm hxc
      · exact Or.inl h'.symm
    · have : b ∈ ({d, x, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hbd
      · exact absurd h'.symm hxb
      · exact Or.inr h'.symm
  have ecdx : o c d x = o b c x := by linarith [ho.rot b c x, ho.swap23 c x d]
  have edbx : o d b x = o b c x := by linarith [ho.rot c d x, ho.swap23 d x b]
  -- support
  have hsupp : ∀ p q r, o p q r + o b c x * (otri b c d p q r - otri b c x p q r -
      otri c d x p q r - otri d b x p q r) ≠ 0 → ({p, q, r} : Finset V) ∈ L := by
    intro p q r h
    by_cases h4 : ({p, q, r} : Finset V) = {b, c, d}
    · exact h4 ▸ hτ
    rw [otri_eq_zero h4] at h
    by_cases h1 : ({p, q, r} : Finset V) = {b, c, x}
    · rw [ho.perm hbc hxb.symm hxc.symm h1,
        otri_eq_zero (a := c) (b := d) (c := x)
          (by rw [h1]; exact ne_tri d (by simp) ⟨hbd.symm, hcd.symm, hxd.symm⟩),
        otri_eq_zero (a := d) (b := b) (c := x)
          (by rw [h1]; exact ne_tri d (by simp) ⟨hbd.symm, hcd.symm, hxd.symm⟩)] at h
      exact absurd (by ring) h
    by_cases h2 : ({p, q, r} : Finset V) = {c, d, x}
    · rw [ho.perm hcd hxc.symm hxd.symm h2, ecdx,
        otri_eq_zero (a := b) (b := c) (c := x)
          (by rw [h2]; exact ne_tri b (by simp) ⟨hbc, hbd, hxb.symm⟩),
        otri_eq_zero (a := d) (b := b) (c := x)
          (by rw [h2]; exact ne_tri b (by simp) ⟨hbc, hbd, hxb.symm⟩)] at h
      exact absurd (by ring) h
    by_cases h3 : ({p, q, r} : Finset V) = {d, b, x}
    · rw [ho.perm hbd.symm hxd.symm hxb.symm h3, edbx,
        otri_eq_zero (a := b) (b := c) (c := x)
          (by rw [h3]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hxc.symm⟩),
        otri_eq_zero (a := c) (b := d) (c := x)
          (by rw [h3]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hxc.symm⟩)] at h
      exact absurd (by ring) h
    rw [otri_eq_zero h1, otri_eq_zero h2, otri_eq_zero h3] at h
    have hm := ho.supp p q r (by simpa using h)
    simp only [hL', mem_insert, mem_erase] at hm
    rcases hm with hm | hm | hm | ⟨-, hm⟩
    · exact absurd hm h1
    · exact absurd hm h2
    · exact absurd (hm.trans edb.symm) h3
    · exact hm
  refine ⟨fun p q r => ?_, fun p q r => ?_, hsupp, fun p q r h => ?_, fun u v => ?_⟩
  · rw [ho.rot, otri_rot b c d p q r, otri_rot b c x p q r, otri_rot c d x p q r,
      otri_rot d b x p q r]
  · rw [ho.swap, otri_swap b c d p q r, otri_swap b c x p q r, otri_swap c d x p q r,
      otri_swap d b x p q r]
    ring
  · have hxt : x ∉ ({p, q, r} : Finset V) := notMem_of_notMem_verts h hx
    simp only [mem_insert, mem_singleton, not_or] at hxt
    rw [otri_eq_zero (a := b) (b := c) (c := x) (ne_tri x (by simp) hxt),
      otri_eq_zero (a := c) (b := d) (c := x) (ne_tri x (by simp) hxt),
      otri_eq_zero (a := d) (b := b) (c := x) (ne_tri x (by simp) hxt)]
    by_cases h4 : ({p, q, r} : Finset V) = {b, c, d}
    · have hbcd : ({b, c, d} : Finset V) ∉ L' := by
        intro hm
        simp only [hL', mem_insert, mem_erase] at hm
        rcases hm with hm | hm | hm | ⟨hm, -⟩
        · have : x ∈ ({b, c, d} : Finset V) := hm ▸ by simp
          simp [hxb, hxc, hxd] at this
        · have : x ∈ ({b, c, d} : Finset V) := hm ▸ by simp
          simp [hxb, hxc, hxd] at this
        · have : x ∈ ({b, c, d} : Finset V) := hm ▸ by simp
          simp [hxb, hxc, hxd] at this
        · exact hm rfl
      rw [ho.eq_zero_of_notMem (h4 ▸ hbcd)]
      simpa using otri_mul_unit hbc hbd hcd h4 hs
    · have hm : ({p, q, r} : Finset V) ∈ L' :=
        mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨h4, h⟩)))
      rw [otri_eq_zero h4]
      simpa using ho.unit p q r hm
  · obtain ⟨hb', hc', hx'⟩ := mem_verts2_of_mem mbcx
    obtain ⟨-, hd', -⟩ := mem_verts2_of_mem mcdx
    have hx0 : o u v x + o b c x * (otri b c d u v x - otri b c x u v x - otri c d x u v x -
        otri d b x u v x) = 0 := by
      by_contra h'
      exact hx (mem_verts2.mpr ⟨_, hsupp u v x h', by simp⟩)
    rw [← sum_verts_insert hx hx0, ← verts2_sub13 hτ, ← hL', sum_add_distrib, ← mul_sum,
      sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ho.cycle, sum_otri hb' hc' hd',
      sum_otri hb' hc' hx', sum_otri hc' hd' hx', sum_otri hd' hb' hx', edir_swap b x,
      edir_swap c x, edir_swap d x]
    ring

end sub13

/-! ## Flipping an edge -/

section flip22

variable {L : Finset (Finset V)} {b c d e : V} {o : V → V → V → ℤ}

/-- An orientation after flipping `bc` to `de`: the old one plus `o(b,c,d)` times the boundary-free
chain `dbe + cde − bcd − cbe`. -/
lemma isOrientation_flip22 (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L)
    (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e})
    (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ) (ho : IsOrientation L o) :
    IsOrientation (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e})))
      (fun p q r => o p q r + o b c d * (otri d b e p q r + otri c d e p q r - otri b c d p q r -
        otri c b e p q r)) := by
  have ecb : ({c, b, e} : Finset V) = {b, c, e} := insert_comm _ _ _
  have edb : ({d, b, e} : Finset V) = {b, d, e} := insert_comm _ _ _
  obtain ⟨hb, hc, hd⟩ := mem_verts2_of_mem h₁
  obtain ⟨-, -, he⟩ := mem_verts2_of_mem h₂
  have hs := ho.unit b c d h₁
  have hbde : ({b, d, e} : Finset V) ∉ L := fun h => hfresh _ h (by simp)
  have hcde : ({c, d, e} : Finset V) ∉ L := fun h => hfresh _ h (by simp)
  have hpair : o b c d + o b c e = 0 := by
    refine ho.pair hde hd he fun w hw => ?_
    rcases hstar _ hw (by simp [insert_subset_iff]) with h | h
    · have : d ∈ ({b, c, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h'.symm hbd
      · exact absurd h'.symm hcd
      · exact Or.inl h'.symm
    · have : e ∈ ({b, c, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h'.symm hbe
      · exact absurd h'.symm hce
      · exact Or.inr h'.symm
  have hcbe : o c b e = o b c d := by linarith [ho.swap b c e]
  refine ⟨fun p q r => ?_, fun p q r => ?_, fun p q r h => ?_, fun p q r h => ?_, fun u v => ?_⟩
  · rw [ho.rot, otri_rot d b e p q r, otri_rot c d e p q r, otri_rot b c d p q r,
      otri_rot c b e p q r]
  · rw [ho.swap, otri_swap d b e p q r, otri_swap c d e p q r, otri_swap b c d p q r,
      otri_swap c b e p q r]
    ring
  · simp only [mem_insert, mem_erase]
    by_cases h1 : ({p, q, r} : Finset V) = {b, d, e}
    · exact Or.inl h1
    by_cases h2 : ({p, q, r} : Finset V) = {c, d, e}
    · exact Or.inr (Or.inl h2)
    rw [otri_eq_zero (edb ▸ h1), otri_eq_zero h2] at h
    by_cases h3 : ({p, q, r} : Finset V) = {b, c, d}
    · rw [ho.perm hbc hbd hcd h3, otri_eq_zero (a := c) (b := b) (c := e)
        (by rw [h3]; exact ne_tri e (by simp) ⟨hbe.symm, hce.symm, hde.symm⟩)] at h
      exact absurd (by ring) h
    by_cases h4 : ({p, q, r} : Finset V) = {c, b, e}
    · rw [ho.perm hbc.symm hce hbe h4, hcbe, otri_eq_zero (a := b) (b := c) (c := d)
        (by rw [h4]; exact ne_tri d (by simp) ⟨hcd.symm, hbd.symm, hde⟩)] at h
      exact absurd (by ring) h
    rw [otri_eq_zero h3, otri_eq_zero h4] at h
    exact Or.inr (Or.inr ⟨fun h' => h4 (h'.trans ecb.symm), h3, ho.supp p q r (by simpa using h)⟩)
  · simp only [mem_insert, mem_erase] at h
    rcases h with h | h | ⟨h4, h3, hL⟩
    · rw [ho.eq_zero_of_notMem (h ▸ hbde),
        otri_eq_zero (a := c) (b := d) (c := e)
          (by rw [h]; exact ne_tri c (by simp) ⟨hbc.symm, hcd, hce⟩),
        otri_eq_zero (a := b) (b := c) (c := d)
          (by rw [h]; exact ne_tri c (by simp) ⟨hbc.symm, hcd, hce⟩),
        otri_eq_zero (a := c) (b := b) (c := e)
          (by rw [h]; exact ne_tri c (by simp) ⟨hbc.symm, hcd, hce⟩)]
      simpa using otri_mul_unit hbd.symm hde hbe (h.trans edb.symm) hs
    · rw [ho.eq_zero_of_notMem (h ▸ hcde),
        otri_eq_zero (a := d) (b := b) (c := e)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hbe⟩),
        otri_eq_zero (a := b) (b := c) (c := d)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hbe⟩),
        otri_eq_zero (a := c) (b := b) (c := e)
          (by rw [h]; exact ne_tri b (by simp) ⟨hbc, hbd, hbe⟩)]
      simpa using otri_mul_unit hcd hce hde h hs
    · rw [otri_eq_zero (a := d) (b := b) (c := e) (fun h' => hbde (edb ▸ h' ▸ hL)),
        otri_eq_zero (a := c) (b := d) (c := e) (fun h' => hcde (h' ▸ hL)), otri_eq_zero h3,
        otri_eq_zero (fun h' => h4 (h'.trans ecb))]
      simpa using ho.unit p q r hL
  · rw [verts2_flip22 h₁ h₂, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib,
      sum_add_distrib, ho.cycle, sum_otri hd hb he, sum_otri hc hd he, sum_otri hb hc hd,
      sum_otri hc hb he, edir_swap d e, edir_swap b c]
    ring

/-- An orientation before flipping `bc` to `de`: the reverse of `isOrientation_flip22`. -/
lemma isOrientation_of_flip22 (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L)
    (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ)
    (ho : IsOrientation (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e})))
      o) :
    IsOrientation L (fun p q r => o p q r - o d b e * (otri d b e p q r + otri c d e p q r -
      otri b c d p q r - otri c b e p q r)) := by
  have ecb : ({c, b, e} : Finset V) = {b, c, e} := insert_comm _ _ _
  have edb : ({d, b, e} : Finset V) = {b, d, e} := insert_comm _ _ _
  set L' := insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e})) with hL'
  have mbde : ({b, d, e} : Finset V) ∈ L' := mem_insert_self _ _
  have mcde : ({c, d, e} : Finset V) ∈ L' := mem_insert_of_mem (mem_insert_self _ _)
  have hbde : ({b, d, e} : Finset V) ∉ L := fun h => hfresh _ h (by simp)
  have hcde : ({c, d, e} : Finset V) ∉ L := fun h => hfresh _ h (by simp)
  have hs := ho.unit d b e (edb ▸ mbde)
  have hpair : o d e b + o d e c = 0 := by
    refine ho.pair hbc (mem_verts2_of_mem mbde).1 (mem_verts2_of_mem mcde).1 fun w hw => ?_
    simp only [hL', mem_insert, mem_erase] at hw
    rcases hw with h | h | ⟨-, -, hw⟩
    · have : b ∈ ({d, e, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hbd
      · exact absurd h' hbe
      · exact Or.inl h'.symm
    · have : c ∈ ({d, e, w} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hcd
      · exact absurd h' hce
      · exact Or.inr h'.symm
    · exact absurd (by simp [insert_subset_iff]) (hfresh _ hw)
  have hcde' : o c d e = o d b e := by
    linarith [ho.rot b d e, ho.swap b d e, ho.rot c d e]
  have hsupp : ∀ p q r, o p q r - o d b e * (otri d b e p q r + otri c d e p q r -
      otri b c d p q r - otri c b e p q r) ≠ 0 → ({p, q, r} : Finset V) ∈ L := by
    intro p q r h
    by_cases h3 : ({p, q, r} : Finset V) = {b, c, d}
    · exact h3 ▸ h₁
    by_cases h4 : ({p, q, r} : Finset V) = {c, b, e}
    · exact h4.trans ecb ▸ h₂
    rw [otri_eq_zero h3, otri_eq_zero h4] at h
    by_cases h1 : ({p, q, r} : Finset V) = {d, b, e}
    · rw [ho.perm hbd.symm hde hbe h1, otri_eq_zero (a := c) (b := d) (c := e)
        (by rw [h1]; exact ne_tri c (by simp) ⟨hcd, hbc.symm, hce⟩)] at h
      exact absurd (by ring) h
    by_cases h2 : ({p, q, r} : Finset V) = {c, d, e}
    · rw [ho.perm hcd hce hde h2, hcde', otri_eq_zero (a := d) (b := b) (c := e)
        (by rw [h2]; exact ne_tri b (by simp) ⟨hbc, hbd, hbe⟩)] at h
      exact absurd (by ring) h
    rw [otri_eq_zero h1, otri_eq_zero h2] at h
    have hm := ho.supp p q r (by simpa using h)
    simp only [hL', mem_insert, mem_erase] at hm
    rcases hm with hm | hm | ⟨-, -, hm⟩
    · exact absurd (hm.trans edb.symm) h1
    · exact absurd hm h2
    · exact hm
  refine ⟨fun p q r => ?_, fun p q r => ?_, hsupp, fun p q r h => ?_, fun u v => ?_⟩
  · rw [ho.rot, otri_rot d b e p q r, otri_rot c d e p q r, otri_rot b c d p q r,
      otri_rot c b e p q r]
  · rw [ho.swap, otri_swap d b e p q r, otri_swap c d e p q r, otri_swap b c d p q r,
      otri_swap c b e p q r]
    ring
  · have hne1 : ({p, q, r} : Finset V) ≠ {d, b, e} := fun h' => hbde (edb ▸ h' ▸ h)
    have hne2 : ({p, q, r} : Finset V) ≠ {c, d, e} := fun h' => hcde (h' ▸ h)
    rw [otri_eq_zero hne1, otri_eq_zero hne2]
    by_cases h3 : ({p, q, r} : Finset V) = {b, c, d}
    · have hn : ({b, c, d} : Finset V) ∉ L' := by
        intro hm
        simp only [hL', mem_insert, mem_erase] at hm
        rcases hm with hm | hm | ⟨-, hm, -⟩
        · have : c ∈ ({b, d, e} : Finset V) := hm ▸ by simp
          simp [hbc.symm, hcd, hce] at this
        · have : b ∈ ({c, d, e} : Finset V) := hm ▸ by simp
          simp [hbc, hbd, hbe] at this
        · exact hm rfl
      rw [ho.eq_zero_of_notMem (h3 ▸ hn), otri_eq_zero (a := c) (b := b) (c := e)
        (by rw [h3]; exact ne_tri e (by simp) ⟨hbe.symm, hce.symm, hde.symm⟩)]
      simpa using otri_mul_unit hbc hbd hcd h3 hs
    by_cases h4 : ({p, q, r} : Finset V) = {c, b, e}
    · have hn : ({b, c, e} : Finset V) ∉ L' := by
        intro hm
        simp only [hL', mem_insert, mem_erase] at hm
        rcases hm with hm | hm | ⟨hm, -, -⟩
        · have : c ∈ ({b, d, e} : Finset V) := hm ▸ by simp
          simp [hbc.symm, hcd, hce] at this
        · have : b ∈ ({c, d, e} : Finset V) := hm ▸ by simp
          simp [hbc, hbd, hbe] at this
        · exact hm rfl
      rw [ho.eq_zero_of_notMem (h4.trans ecb ▸ hn), otri_eq_zero h3]
      simpa using otri_mul_unit hbc.symm hce hbe h4 hs
    · have hm : ({p, q, r} : Finset V) ∈ L' := mem_insert_of_mem (mem_insert_of_mem
        (mem_erase.mpr ⟨fun h' => h4 (h'.trans ecb.symm), mem_erase.mpr ⟨h3, h⟩⟩))
      rw [otri_eq_zero h3, otri_eq_zero h4]
      simpa using ho.unit p q r hm
  · obtain ⟨hb, hc, hd⟩ := mem_verts2_of_mem h₁
    obtain ⟨-, -, he⟩ := mem_verts2_of_mem h₂
    have hv : verts2 L = verts2 L' := (verts2_flip22 h₁ h₂).symm
    rw [hv] at hb hc hd he
    rw [hv, sum_sub_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
      ho.cycle, sum_otri hd hb he, sum_otri hc hd he, sum_otri hb hc hd, sum_otri hc hb he,
      edir_swap d e, edir_swap b c]
    ring

end flip22

/-- **A 2D bistellar move keeps orientability, in both directions.** -/
theorem Move2.isOrientable_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    IsOrientable L ↔ IsOrientable L' := by
  cases h with
  | sub13 hbc hbd hcd hτ hx =>
    exact ⟨fun ⟨_, ho⟩ => ⟨_, isOrientation_sub13 hbc hbd hcd hτ hx ho⟩,
      fun ⟨_, ho⟩ => ⟨_, isOrientation_of_sub13 hbc hbd hcd hτ hx ho⟩⟩
  | flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    exact ⟨fun ⟨_, ho⟩ => ⟨_, isOrientation_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh ho⟩,
      fun ⟨_, ho⟩ => ⟨_, isOrientation_of_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hfresh ho⟩⟩

/-- The Euler characteristic is an invariant of chains of 2D bistellar moves. -/
theorem euler2_eq_of_eqvGen {L L' : Finset (Finset V)} (h : Relation.EqvGen Move2 L L') :
    euler2 L = euler2 L' := by
  induction h with
  | rel _ _ h => exact Move2.euler2_eq h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Complexes related by 2D bistellar moves are orientable together. -/
theorem isOrientable_iff_of_eqvGen {L L' : Finset (Finset V)} (h : Relation.EqvGen Move2 L L') :
    IsOrientable L ↔ IsOrientable L' := by
  induction h with
  | rel _ _ h => exact Move2.isOrientable_iff h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Lightlike.Surfaces
