import Lightlike.SpinFoam.EPRLStateSum.Sphere6Sign
import Lightlike.SpinFoam.EPRLStateSum.TrustSphere
import Lightlike.SpinFoam.EPRLStateSum.IntrinsicVertex

/-!
# The EPRL state sum at `γ = 1` on the boundary of the 5-simplex at low spins

Trust check of `amplitudeI` (t1): with the bone cutoff `col0` (doubled spin `≤ 1` on the four triangles through the
edge `{0, 1}`, `0` on the others) only two triangle colourings contribute, the zero colouring and the bone
colouring `col0`, and for each of them the virtual spins are forced, so that the signed Ooguri sum of
`amplitudeI_one_eq_signed_ooguri` has two terms.
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The triangles of `sphere6` are the `3`-element subsets of `Fin 6`. -/
lemma mem_tris_sphere6 {f : Finset (Fin 6)} : f ∈ sphere6.tris ↔ #f = 3 := by
  revert f; decide +kernel

/-- The tetrahedra of `sphere6` are the `4`-element subsets of `Fin 6`. -/
lemma mem_tets_sphere6 {f : Finset (Fin 6)} : f ∈ sphere6.tets ↔ #f = 4 := by
  revert f; decide +kernel

/-- A tetrahedron `univ \ {p, p'}` meeting `{0, 1}` has no leg containing `{0, 1}`. -/
lemma legs_not_bone : ∀ (p p' : Fin 6) (a : Fin 5) (i : Fin 4), p ≠ p' → p.succAbove a = p' →
    (p = 0 ∨ p = 1 ∨ p' = 0 ∨ p' = 1) →
      ¬ ({0, 1} : Finset (Fin 6)) ⊆ univ \ {p, p', p.succAbove (a.succAbove i)} := by
  decide +kernel

/-- For the tetrahedron `univ \ {p, p'} ∋ 0, 1`, the legs `0, 1` omit `0, 1`. -/
lemma legs_01_not_bone : ∀ (p p' : Fin 6) (a : Fin 5) (i : Fin 4), i.val < 2 → p ≠ p' → p.succAbove a = p' →
    ¬ (p = 0 ∨ p = 1 ∨ p' = 0 ∨ p' = 1) →
      ¬ ({0, 1} : Finset (Fin 6)) ⊆ univ \ {p, p', p.succAbove (a.succAbove i)} := by
  decide +kernel

/-- For the tetrahedron `univ \ {p, p'} ∋ 0, 1`, the legs `2, 3` are the bone triangles `{0, 1, x}`, `{0, 1, y}`
with `{x, y}` the other two vertices. -/
lemma legs_23_bone : ∀ (p p' : Fin 6) (a : Fin 5) (x y : Fin 6), p ≠ p' → p.succAbove a = p' →
    ¬ (p = 0 ∨ p = 1 ∨ p' = 0 ∨ p' = 1) → x ≠ y → x ≠ p → x ≠ p' → y ≠ p → y ≠ p' → x ≠ 0 → x ≠ 1 →
      y ≠ 0 → y ≠ 1 →
        ((univ \ {p, p', p.succAbove (a.succAbove 2)} = {0, 1, x} ∧
            univ \ {p, p', p.succAbove (a.succAbove 3)} = {0, 1, y}) ∨
          (univ \ {p, p', p.succAbove (a.succAbove 2)} = {0, 1, y} ∧
            univ \ {p, p', p.succAbove (a.succAbove 3)} = {0, 1, x})) := by
  decide +kernel


/-- **The legs of a tetrahedron of `sphere6`**: for an incidence bijection `e`, the tetrahedron `t` is `univ \ {p, p'}`
and the sorted legs of its first incidence are the colours of the triangles `univ \ {p, p', q_i}`. -/
lemma sphere6_legs (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (t : sphere6.tets) (g : Finset (Fin 6) → ℕ) :
    ∃ p p' : Fin 6, p ≠ p' ∧ p.succAbove (e (t, false)).2 = p' ∧ t.1 = univ \ {p, p'} ∧
      ∀ i : Fin 4, complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove i) =
        g (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove i)} ) := by
  obtain ⟨p, p', h1, -, hne, hs, -⟩ := sphere6_positions e he t
  refine ⟨p, p', hne, hs, ?_, fun i => ?_⟩
  · have h := congrArg Subtype.val (he t false)
    have h' : incSet sphere6 (e (t, false)) = t.1 := h
    rw [incSet_sphere6 _ p h1] at h'
    rw [← h', hs]
    ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  · unfold complexJ simplexJ
    have key : ∀ (s : Finset (Fin 6)) (hs' : s = univ.erase p) (h : #s = 5) (a b : Fin 5),
        g ((s.erase (s.orderEmbOfFin h a)).erase (s.orderEmbOfFin h b)) =
          g (univ \ {p, p.succAbove a, p.succAbove b}) := by
      rintro s rfl h a b
      rw [orderEmbOfFin_erase, orderEmbOfFin_erase]
      congr 1
      ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
    rw [key _ h1 _ _ _, hs]


/-- **The legs of the bone colouring**: for the tetrahedron `univ \ {p, p'}` with its sorted legs `univ \ {p, p', q_i}`,
the legs `0, 1` have colour `0` and the legs `2, 3` have the colour of the tetrahedron (`1` if it contains `{0, 1}`). -/
lemma col0_legs : ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    col0 (univ \ {p, p', p.succAbove (a.succAbove 0)}) = 0 ∧
    col0 (univ \ {p, p', p.succAbove (a.succAbove 1)}) = 0 ∧
    col0 (univ \ {p, p', p.succAbove (a.succAbove 2)}) = col0 (univ \ {p, p'}) ∧
    col0 (univ \ {p, p', p.succAbove (a.succAbove 3)}) = col0 (univ \ {p, p'}) := by
  unfold col0; decide +kernel

/-- The triangle part of the sign of a simplex of `sphere6` at the bone colouring is even. -/
lemma col0_triPart_even : ∀ p : Fin 6,
    Even (col0 (univ \ {p, p.succAbove 1, p.succAbove 2}) + col0 (univ \ {p, p.succAbove 1, p.succAbove 4}) +
      col0 (univ \ {p, p.succAbove 3, p.succAbove 4}) + col0 (univ \ {p, p.succAbove 0, p.succAbove 2}) +
      col0 (univ \ {p, p.succAbove 0, p.succAbove 4}) + col0 (univ \ {p, p.succAbove 2, p.succAbove 4})) := by
  unfold col0; decide +kernel

/-- A set not containing `{0, 1}` has bone colour `0`. -/
lemma col0_eq_zero_of_not_sub {f : Finset (Fin 6)} (h : ¬ ({0, 1} : Finset (Fin 6)) ⊆ f) : col0 f = 0 := by
  unfold col0; rw [if_neg (fun h' => h h'.1)]

/-- A triangle containing `{0, 1}` is `{0, 1, x}` with `2 ≤ x`. -/
lemma tri_bone_eq : ∀ f : Finset (Fin 6), #f = 3 → ({0, 1} : Finset (Fin 6)) ⊆ f →
    ∃ x : Fin 6, 2 ≤ x ∧ f = {0, 1, x} := by
  decide +kernel

/-- The tetrahedron `{0, 1, x, y}` of `sphere6`. -/
lemma card_bone_tet : ∀ x y : Fin 6, 2 ≤ x → 2 ≤ y → x ≠ y → #({0, 1, x, y} : Finset (Fin 6)) = 4 := by
  decide +kernel

/-- The colouring `extS S c` of a colouring `c ≤ cut` of the faces in `S` is `≤ cut`. -/
lemma extS_le {V : Type*} [LinearOrder V] {S : Finset (Finset V)} {cut : Finset V → ℕ} (c : ∀ f ∈ S, ℕ)
    (hc : c ∈ S.pi (fun f => range (cut f + 1))) (f : Finset V) :
    Lightlike.PR.extS S c f ≤ cut f := by
  unfold Lightlike.PR.extS
  split_ifs with h
  · rw [Finset.mem_pi] at hc
    have := hc f h
    rw [mem_range] at this; omega
  · exact Nat.zero_le _

lemma extS_of_mem {V : Type*} [LinearOrder V] {S : Finset (Finset V)} (c : ∀ f ∈ S, ℕ) {f : Finset V}
    (hf : f ∈ S) : Lightlike.PR.extS S c f = c f hf := by
  unfold Lightlike.PR.extS; rw [dif_pos hf]

/-- The sorted legs of the first incidence of the tetrahedron `t`. -/
noncomputable def legJ (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (t : sphere6.tets) (i : Fin 4) : ℕ :=
  complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove i)

/-- The triangle constraints at the tetrahedron `t` for the virtual spin `L t`. -/
def IndP (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (L : sphere6.tets → ℕ) (t : sphere6.tets) : Prop :=
  Lightlike.Pentagon.Tri (legJ e g t 0) (legJ e g t 2) (L t) ∧
    Lightlike.Pentagon.Tri (L t) (legJ e g t 1) (legJ e g t 3)

/-- **The bone colouring is constant on the bone triangles** whenever the triangle constraints hold. -/
lemma bone_const (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ) (hle : ∀ f, g f ≤ col0 f)
    (L : sphere6.tets → ℕ) (hI : ∀ t, IndP e g L t) (x y : Fin 6) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxy : x ≠ y) : g {0, 1, x} = g {0, 1, y} := by
  let t : sphere6.tets := ⟨{0, 1, x, y}, mem_tets_sphere6.2 (card_bone_tet x y hx hy hxy)⟩
  obtain ⟨p, p', hne, hs, ht, hl⟩ := sphere6_legs e he t g
  have hmem : ∀ z : Fin 6, z ∈ ({0, 1, x, y} : Finset (Fin 6)) → z ≠ p ∧ z ≠ p' := by
    intro z hz
    have : z ∈ t.1 := hz
    rw [ht] at this
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at this
    exact this
  have h01 : ¬ (p = 0 ∨ p = 1 ∨ p' = 0 ∨ p' = 1) := by
    intro h
    have h0 := hmem 0 (by simp)
    have h1 := hmem 1 (by simp)
    rcases h with h | h | h | h <;> simp_all
  have hxp := hmem x (by simp)
  have hyp := hmem y (by simp)
  have hx0 : x ≠ 0 := by intro h; subst h; omega
  have hx1 : x ≠ 1 := by intro h; subst h; omega
  have hy0 : y ≠ 0 := by intro h; subst h; omega
  have hy1 : y ≠ 1 := by intro h; subst h; omega
  have hI' := hI t
  unfold IndP legJ at hI'
  rw [hl 0, hl 1, hl 2, hl 3] at hI'
  set a := (e (t, false)).2 with ha
  have z0 : g (univ \ {p, p', p.succAbove (a.succAbove 0)}) = 0 := by
    have := hle (univ \ {p, p', p.succAbove (a.succAbove 0)})
    rw [col0_eq_zero_of_not_sub (legs_01_not_bone p p' a 0 (by decide) hne hs h01)] at this; omega
  have z1 : g (univ \ {p, p', p.succAbove (a.succAbove 1)}) = 0 := by
    have := hle (univ \ {p, p', p.succAbove (a.succAbove 1)})
    rw [col0_eq_zero_of_not_sub (legs_01_not_bone p p' a 1 (by decide) hne hs h01)] at this; omega
  rw [z0, z1] at hI'
  obtain ⟨hT1, hT2⟩ := hI'
  unfold Lightlike.Pentagon.Tri at hT1 hT2
  rcases legs_23_bone p p' a x y hne hs h01 hxy hxp.1 hxp.2 hyp.1 hyp.2 hx0 hx1 hy0 hy1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · rw [h2] at hT1; rw [h3] at hT2; omega
  · rw [h2] at hT1; rw [h3] at hT2; omega


/-- The legs of a tetrahedron are triangles. -/
lemma legs_card : ∀ (p p' : Fin 6) (a : Fin 5) (i : Fin 4), p ≠ p' → p.succAbove a = p' →
    #(univ \ {p, p', p.succAbove (a.succAbove i)}) = 3 := by
  decide +kernel

/-- **The legs at the bone colouring**: `(0, 0, v, v)` with `v` the bone colour of the tetrahedron. -/
lemma legJ_col0 (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, #f = 3 → g f = col0 f) (t : sphere6.tets) :
    legJ e g t 0 = 0 ∧ legJ e g t 1 = 0 ∧ legJ e g t 2 = col0 t.1 ∧ legJ e g t 3 = col0 t.1 := by
  obtain ⟨p, p', hne, hs, ht, hl⟩ := sphere6_legs e he t g
  obtain ⟨h0, h1, h2, h3⟩ := col0_legs p p' (e (t, false)).2 hne hs
  unfold legJ
  rw [hl 0, hl 1, hl 2, hl 3, hg _ (legs_card p p' _ 0 hne hs), hg _ (legs_card p p' _ 1 hne hs),
    hg _ (legs_card p p' _ 2 hne hs), hg _ (legs_card p p' _ 3 hne hs), h0, h1, h2, h3, ht]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- At the zero colouring all the legs are `0`. -/
lemma legJ_zero (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, g f = 0) (t : sphere6.tets) (i : Fin 4) : legJ e g t i = 0 := by
  unfold legJ complexJ simplexJ; exact hg _

/-- **The virtual spin is forced at the bone colouring**: the constraints at `t` give `L t = col0 t`. -/
lemma L_eq_col0 (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, #f = 3 → g f = col0 f) (L : sphere6.tets → ℕ) (t : sphere6.tets) (hI : IndP e g L t) :
    L t = col0 t.1 := by
  obtain ⟨h0, h1, h2, h3⟩ := legJ_col0 e he g hg t
  obtain ⟨hT1, hT2⟩ := hI
  rw [h0, h2] at hT1; rw [h1, h3] at hT2
  unfold Lightlike.Pentagon.Tri at hT1 hT2
  omega

/-- The virtual spin is `0` at the zero colouring. -/
lemma L_eq_zero (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, g f = 0) (L : sphere6.tets → ℕ) (t : sphere6.tets) (hI : IndP e g L t) : L t = 0 := by
  obtain ⟨hT1, hT2⟩ := hI
  rw [legJ_zero e g hg t 0, legJ_zero e g hg t 2] at hT1
  unfold Lightlike.Pentagon.Tri at hT1
  omega


/-- The triangle spins of the simplex `univ.erase p` of `sphere6`. -/
lemma complexJ_sphere6 (g : Finset (Fin 6) → ℕ) (s : sphere6.simps) (p : Fin 6) (hp : s.1 = univ.erase p)
    (x y : Fin 5) : complexJ sphere6 g s x y = g (univ \ {p, p.succAbove x, p.succAbove y}) := by
  unfold complexJ simplexJ
  have key : ∀ (s' : Finset (Fin 6)) (hs' : s' = univ.erase p) (h : #s' = 5) (a b : Fin 5),
      g ((s'.erase (s'.orderEmbOfFin h a)).erase (s'.orderEmbOfFin h b)) =
        g (univ \ {p, p.succAbove a, p.succAbove b}) := by
    rintro s' rfl h a b
    rw [orderEmbOfFin_erase, orderEmbOfFin_erase]
    congr 1
    ext z; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  exact key _ hp _ x y

lemma card_tri_sphere6 : ∀ (p : Fin 6) (x y : Fin 5), x ≠ y → #(univ \ {p, p.succAbove x, p.succAbove y}) = 3 := by
  decide +kernel

/-- The triangle part of the global sign is even at the bone colouring. -/
lemma triPart_even_col0 (g : Finset (Fin 6) → ℕ) (hg : ∀ f, #f = 3 → g f = col0 f) (s : sphere6.simps) :
    Even (triPart (complexJ sphere6 g s)) := by
  obtain ⟨p, hp⟩ := sphere6_simp_eq s
  have h := col0_triPart_even p
  unfold triPart
  rw [complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp,
    complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp,
    hg _ (card_tri_sphere6 p 1 2 (by decide)), hg _ (card_tri_sphere6 p 1 4 (by decide)),
    hg _ (card_tri_sphere6 p 3 4 (by decide)), hg _ (card_tri_sphere6 p 0 2 (by decide)),
    hg _ (card_tri_sphere6 p 0 4 (by decide)), hg _ (card_tri_sphere6 p 2 4 (by decide))]
  exact h

lemma triPart_even_zero (g : Finset (Fin 6) → ℕ) (hg : ∀ f, g f = 0) (s : sphere6.simps) :
    Even (triPart (complexJ sphere6 g s)) := by
  unfold triPart complexJ simplexJ
  simp only [hg]
  exact ⟨0, rfl⟩


/-- **The sign of the link orientations is `1`** when the triangle part of every simplex is even. -/
lemma linkSign_eq_one (g : Finset (Fin 6) → ℕ)
    (htri : ∀ s : sphere6.simps, Even (triPart (complexJ sphere6 g s))) :
    linkSign sphere6 g = 1 := by
  unfold linkSign
  exact Even.neg_one_pow (Finset.even_sum _ fun s _ => htri s)


/-- `simpBox` only reads the entries off the diagonal. -/
lemma simpBox_congr {J J' : Fin 5 → Fin 5 → ℕ} (h : ∀ x y, x ≠ y → J x y = J' x y) :
    simpBox J = simpBox J' := by
  have h01 := h 0 1 (by decide)
  have h03 := h 0 3 (by decide)
  have h12 := h 1 2 (by decide)
  have h14 := h 1 4 (by decide)
  have h23 := h 2 3 (by decide)
  have h02 := h 0 2 (by decide)
  have h34 := h 3 4 (by decide)
  have h13 := h 1 3 (by decide)
  have h04 := h 0 4 (by decide)
  have h24 := h 2 4 (by decide)
  unfold simpBox
  simp only [h01, h03, h12, h14, h23, h02, h34, h13, h04, h24]

/-- The bone colour of a tetrahedron is in the box of its positions. -/
lemma col0_mem_box : ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    col0 (univ \ {p, p'}) ∈
      simpBox (fun x y => col0 (univ \ {p, p.succAbove x, p.succAbove y})) a := by
  unfold simpBox col0; decide +kernel

/-- The bone colour of a tetrahedron is in the box of each of its two incidences. -/
lemma mem_box_col0 (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ) (hg : ∀ f, #f = 3 → g f = col0 f)
    (t : sphere6.tets) (b : Bool) :
    col0 t.1 ∈ simpBox (complexJ sphere6 g (e (t, b)).1) (e (t, b)).2 := by
  obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
  have ht : t.1 = univ \ {p, p'} := by
    have h := congrArg Subtype.val (he t false)
    have h' : incSet sphere6 (e (t, false)) = t.1 := h
    rw [incSet_sphere6 _ p h1] at h'
    rw [← h', hs]
    ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  have hJ : ∀ (q : Fin 6) (s : sphere6.simps), s.1 = univ.erase q → ∀ x y : Fin 5, x ≠ y →
      complexJ sphere6 g s x y = col0 (univ \ {q, q.succAbove x, q.succAbove y}) := fun q s hq x y hxy => by
    rw [complexJ_sphere6 g s q hq, hg _ (card_tri_sphere6 q x y hxy)]
  cases b
  · rw [simpBox_congr (hJ p _ h1), ht]
    exact col0_mem_box p p' _ hne hs
  · rw [simpBox_congr (hJ p' _ h2), ht, Finset.pair_comm p p']
    exact col0_mem_box p' p _ hne.symm hs'


lemma zero_mem_box (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) : 0 ∈ simpBox J a := by
  fin_cases a <;> simp [simpBox]

/-- A colouring `g ≤ col0` for which the triangle constraints hold is `0` or the bone colouring on triangles. -/
lemma g_of_const (g : Finset (Fin 6) → ℕ) (hle : ∀ f, g f ≤ col0 f)
    (hconst : ∀ x y : Fin 6, 2 ≤ x → 2 ≤ y → x ≠ y → g {0, 1, x} = g {0, 1, y}) :
    (∀ f, #f = 3 → g f = 0) ∨ (∀ f, #f = 3 → g f = col0 f) := by
  have hb : ∀ f : Finset (Fin 6), #f = 3 → ({0, 1} : Finset (Fin 6)) ⊆ f → g f = g {0, 1, 2} := by
    intro f hf hsub
    obtain ⟨x, hx, rfl⟩ := tri_bone_eq f hf hsub
    by_cases h2 : x = 2
    · rw [h2]
    · exact hconst x 2 hx (by decide) h2
  have hnb : ∀ f : Finset (Fin 6), ¬ ({0, 1} : Finset (Fin 6)) ⊆ f → g f = 0 := by
    intro f hf
    have := hle f
    rw [col0_eq_zero_of_not_sub hf] at this; omega
  have c012 : col0 {0, 1, 2} = 1 := by unfold col0; decide
  have h12 : g {0, 1, 2} ≤ 1 := by have := hle {0, 1, 2}; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h12 with h | h
  · left
    intro f hf
    by_cases hs : ({0, 1} : Finset (Fin 6)) ⊆ f
    · rw [hb f hf hs, h]
    · exact hnb f hs
  · right
    intro f hf
    by_cases hs : ({0, 1} : Finset (Fin 6)) ⊆ f
    · rw [hb f hf hs, h]
      unfold col0; rw [if_pos ⟨hs, by omega, by omega⟩]
    · rw [hnb f hs, col0_eq_zero_of_not_sub hs]

/-- **The Ooguri sum with the link signs** of `amplitudeI_one_eq_signed_ooguri`, for a weight `W` of the coloured complex. -/
noncomputable def signedSum {V : Type*} [LinearOrder V] (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (W : (Finset V → ℕ) → ℝ) : ℝ :=
  ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
    ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
        simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1) (e (t, false)).2 ∩
          simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, true)).1) (e (t, true)).2),
      (∏ t : K.tets, if
          Lightlike.Pentagon.Tri
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 0))
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 2))
            (L t) ∧
          Lightlike.Pentagon.Tri (L t)
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 1))
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 3))
        then (1 : ℝ) else 0) *
        (linkSign K (Lightlike.PR.extS K.tris c) * W (extL K (Lightlike.PR.extS K.tris c) L))

/-- **`amplitudeI` at `γ = 1` is the signed Ooguri sum with the Ooguri weight.** -/
theorem amplitudeI_one_eq_signedSum {V : Type*} [LinearOrder V] (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    amplitudeI 1 K cut = ((signedSum K cut e (Lightlike.SpinFoam.weight K) : ℝ) : ℂ) :=
  amplitudeI_one_eq_signed_ooguri K cut e he


/-- A colouring of the faces `S` bounded by `cut` lies in `S.pi (range (cut + 1))`. -/
lemma mem_pi_of_le {V : Type*} [LinearOrder V] {S : Finset (Finset V)} {cut : Finset V → ℕ}
    (c : ∀ f ∈ S, ℕ) (h : ∀ f hf, c f hf ≤ cut f) : c ∈ S.pi (fun f => range (cut f + 1)) :=
  Finset.mem_pi.2 fun f hf => mem_range.2 (Nat.lt_succ_of_le (h f hf))

/-- The product of the indicators is `1` if all the triangle constraints hold. -/
lemma prod_ind_eq_one (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (L : sphere6.tets → ℕ) (h : ∀ t, IndP e g L t) :
    (∏ t : sphere6.tets, if
        Lightlike.Pentagon.Tri
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2)) (L t) ∧
        Lightlike.Pentagon.Tri (L t)
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)) then (1 : ℝ)
      else 0) = 1 :=
  Finset.prod_eq_one fun t _ => if_pos (h t)

/-- The product of the indicators is `0` if a triangle constraint fails. -/
lemma prod_ind_eq_zero (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5) (g : Finset (Fin 6) → ℕ)
    (L : sphere6.tets → ℕ) (h : ¬ ∀ t, IndP e g L t) :
    (∏ t : sphere6.tets, if
        Lightlike.Pentagon.Tri
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2)) (L t) ∧
        Lightlike.Pentagon.Tri (L t)
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
          (complexJ sphere6 g (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)) then (1 : ℝ)
      else 0) = 0 := by
  push_neg at h
  obtain ⟨t, ht⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

/-- **The signed sum on `sphere6` with the bone cutoff has two terms**: the zero colouring and the bone colouring,
each with the sign `+1`: `signedSum col0 = W 0 + W col0`. -/
theorem signedSum_col0 (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (W : (Finset (Fin 6) → ℕ) → ℝ)
    (hW : ∀ col col' : Finset (Fin 6) → ℕ, (∀ f ∈ colFaces sphere6, col f = col' f) → W col = W col') :
    signedSum sphere6 col0 e W = W (fun _ => 0) + W col0 := by
  classical
  have hTm : ∀ f, f ∈ sphere6.tris ↔ #f = 3 := fun f => mem_tris_sphere6
  have hcolF : ∀ f, f ∈ colFaces sphere6 → f ∈ sphere6.tris ∨ f ∈ sphere6.tets := fun f hf => by
    unfold colFaces at hf; exact mem_union.1 hf
  unfold signedSum
  generalize sphere6.tris = T at hTm hcolF ⊢
  set c0 : ∀ f ∈ T, ℕ := fun _ _ => 0 with hc0
  set c1 : ∀ f ∈ T, ℕ := fun f _ => col0 f with hc1
  have hm0 := mem_pi_of_le (S := T) (cut := col0) c0 (fun f hf => Nat.zero_le _)
  have hm1 := mem_pi_of_le (S := T) (cut := col0) c1 (fun f hf => le_refl _)
  have h012 : ({0, 1, 2} : Finset (Fin 6)) ∈ T := (hTm _).2 (by decide)
  have c012 : col0 {0, 1, 2} = 1 := by unfold col0; decide
  have hne : c0 ≠ c1 := by
    intro h
    have := congrFun (congrFun h {0, 1, 2}) h012
    simp only [c0, c1, c012] at this
    omega
  have g0 : ∀ f, Lightlike.PR.extS T c0 f = 0 := fun f => by
    unfold Lightlike.PR.extS; split_ifs <;> rfl
  have g1 : ∀ f, #f = 3 → Lightlike.PR.extS T c1 f = col0 f := fun f hf => by
    rw [extS_of_mem c1 ((hTm f).2 hf)]
  -- `W` at the colourings of the two terms
  have hW0 : ∀ L : sphere6.tets → ℕ, (∀ t, L t = 0) →
      W (extL sphere6 (Lightlike.PR.extS T c0) L) = W (fun _ => 0) := fun L hL =>
    hW _ _ fun f hf => by
      rcases hcolF f hf with h | h
      · unfold extL; rw [dif_neg]; · exact g0 f
        intro ht
        have := (hTm f).1 h
        have := mem_tets_sphere6.1 ht
        omega
      · unfold extL; rw [dif_pos h]; exact hL _
  have hW1 : ∀ L : sphere6.tets → ℕ, (∀ t, L t = col0 t.1) →
      W (extL sphere6 (Lightlike.PR.extS T c1) L) = W col0 := fun L hL =>
    hW _ _ fun f hf => by
      rcases hcolF f hf with h | h
      · unfold extL; rw [dif_neg]; · exact g1 f ((hTm f).1 h)
        intro ht
        have := (hTm f).1 h
        have := mem_tets_sphere6.1 ht
        omega
      · unfold extL; rw [dif_pos h]; exact hL ⟨f, h⟩
  -- the constraints force the colouring
  have hbone : ∀ c ∈ T.pi (fun f => range (col0 f + 1)), c ≠ c0 → c ≠ c1 →
      ∀ L : sphere6.tets → ℕ, ¬ ∀ t, IndP e (Lightlike.PR.extS T c) L t := by
    intro c hc h0 h1 L hI
    have hle : ∀ f, Lightlike.PR.extS T c f ≤ col0 f := extS_le (S := T) (cut := col0) c hc
    have hconst := fun x y hx hy hxy => bone_const e he (Lightlike.PR.extS T c) hle L hI x y hx hy hxy
    rcases g_of_const _ hle hconst with hz | hb
    · apply h0; funext f hf
      rw [← extS_of_mem c hf]; exact hz f ((hTm f).1 hf)
    · apply h1; funext f hf
      rw [← extS_of_mem c hf]; exact hb f ((hTm f).1 hf)
  have hI0 : ∀ t, IndP e (Lightlike.PR.extS T c0) (fun _ => 0) t := fun t => by
    unfold IndP Lightlike.Pentagon.Tri
    rw [legJ_zero e _ g0 t 0, legJ_zero e _ g0 t 1, legJ_zero e _ g0 t 2, legJ_zero e _ g0 t 3]
    dsimp only
    omega
  have hI1 : ∀ t, IndP e (Lightlike.PR.extS T c1) (fun t => col0 t.1) t := fun t => by
    obtain ⟨h0, h1, h2, h3⟩ := legJ_col0 e he _ g1 t
    unfold IndP Lightlike.Pentagon.Tri
    rw [h0, h1, h2, h3]
    dsimp only
    omega
  refine (Finset.sum_eq_add c0 c1 hne ?_ ?_ ?_).trans ?_
  · -- every other colouring contributes `0`
    intro c hc ⟨hc0', hc1'⟩
    refine Finset.sum_eq_zero fun L _ => ?_
    rw [prod_ind_eq_zero e _ L (hbone c hc hc0' hc1' L), zero_mul]
  · intro h; exact absurd hm0 h
  · intro h; exact absurd hm1 h
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the zero colouring
    refine (Finset.sum_eq_single (fun _ => (0 : ℕ)) ?_ ?_).trans ?_
    · intro L _ hL
      rw [prod_ind_eq_zero e _ L (fun h => hL (funext fun t => L_eq_zero e _ g0 L t (h t))), zero_mul]
    · intro hmem
      exact absurd (Fintype.mem_piFinset.2 fun t => mem_inter.2 ⟨zero_mem_box _ _, zero_mem_box _ _⟩) hmem
    · rw [prod_ind_eq_one e _ _ hI0,
        linkSign_eq_one _ (triPart_even_zero _ g0), one_mul, one_mul]
      exact hW0 _ fun t => rfl
  · -- the bone colouring
    refine (Finset.sum_eq_single (fun t => col0 t.1) ?_ ?_).trans ?_
    · intro L _ hL
      rw [prod_ind_eq_zero e _ L (fun h => hL (funext fun t => L_eq_col0 e he _ g1 L t (h t))), zero_mul]
    · intro hmem
      exact absurd (Fintype.mem_piFinset.2 fun t => mem_inter.2
        ⟨mem_box_col0 e he _ g1 t false, mem_box_col0 e he _ g1 t true⟩) hmem
    · rw [prod_ind_eq_one e _ _ hI1,
        linkSign_eq_one _ (triPart_even_col0 _ g1), one_mul, one_mul]
      exact hW1 _ fun t => rfl

/-- **The EPRL state sum at `γ = 1` on the boundary of the 5-simplex with the bone cutoff is the signed Ooguri sum
`1 · weight(0) + 1 · weight(col0)`**: only the zero colouring and the bone colouring survive the triangle
constraints, and both carry the sign `+1` (`signedSum_col0`). -/
theorem amplitudeI_sphere6_eq_weights :
    amplitudeI 1 sphere6 col0 =
      ((Lightlike.SpinFoam.weight sphere6 (fun _ => 0) + Lightlike.SpinFoam.weight sphere6 col0 : ℝ) : ℂ) := by
  obtain ⟨e, he⟩ := exists_complex_incidence sphere6 sphere6_checks.2.2
  rw [amplitudeI_one_eq_signedSum sphere6 col0 e he,
    signedSum_col0 e he (Lightlike.SpinFoam.weight sphere6) (fun col col' h => weight_congr sphere6 h)]

/-- **t1: the EPRL state sum at `γ = 1` on the boundary of the 5-simplex with the bone cutoff is `5`.** The two
contributing colourings are the zero colouring (weight `1`, `weight_zero`) and the bone colouring (weight `4`,
`weight_col0`), both with the sign `+1`: `1 + 4`. -/
theorem amplitudeI_sphere6_low_spin : amplitudeI 1 sphere6 col0 = 5 := by
  rw [amplitudeI_sphere6_eq_weights, weight_zero, weight_col0]
  norm_num

/-- The wrong-face weight `(J + 1)²` depends only on the colours of the faces. -/
lemma weightWrong_congr (K : Complex4 (Fin 6)) {col col' : Finset (Fin 6) → ℕ}
    (h : ∀ f ∈ colFaces K, col f = col' f) : weightWrong K col = weightWrong K col' := by
  unfold weightWrong
  congr 1
  · refine prod_congr rfl fun f hf => ?_
    rw [h f (mem_union_left _ hf)]
  · refine prod_congr rfl fun s hs => simpW_congr fun f hfs hf => h f ?_
    rcases hf with hf | hf
    · exact mem_union_left _ (Complex4.mem_faces.mpr ⟨s, hs, hfs, hf⟩)
    · exact mem_union_right _ (Complex4.mem_faces.mpr ⟨s, hs, hfs, hf⟩)

/-- The zero colouring has weight `1` also with the wrong face amplitude. -/
lemma weightWrong_zero : weightWrong sphere6 (fun _ => 0) = 1 := by
  have h := weight_zero sphere6
  unfold weight at h
  unfold weightWrong
  simpa using h

/-- **t2: a wrong face amplitude is detected.** With the face amplitude `(J + 1)²` instead of `J + 1` in the signed
Ooguri sum the bone cutoff gives `1 + 64 = 65`, not the `5` of `amplitudeI_sphere6_low_spin`. -/
theorem amplitudeI_wrong_face :
    ∃ e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5,
      ((signedSum sphere6 col0 e (weightWrong sphere6) : ℝ) : ℂ) = 65 ∧
        ((signedSum sphere6 col0 e (weightWrong sphere6) : ℝ) : ℂ) ≠ amplitudeI 1 sphere6 col0 := by
  obtain ⟨e, he⟩ := exists_complex_incidence sphere6 sphere6_checks.2.2
  refine ⟨e, ?_, ?_⟩
  · rw [signedSum_col0 e he (weightWrong sphere6) (fun col col' h => weightWrong_congr sphere6 h), weightWrong_zero,
      weightWrong_col0]
    norm_num
  · rw [signedSum_col0 e he (weightWrong sphere6) (fun col col' h => weightWrong_congr sphere6 h), weightWrong_zero,
      weightWrong_col0, amplitudeI_sphere6_low_spin]
    norm_num

end Lightlike.SpinFoam.EPRLStateSum.Trust
