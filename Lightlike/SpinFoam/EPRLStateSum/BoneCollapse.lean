import Lightlike.SpinFoam.EPRLStateSum.BoneColouring

/-!
# The signed Ooguri sum of a bone cutoff has two terms

For the bone cutoff `boneB u w` of an edge `{u, w}` (`u < w`) of `∂Δ⁵` only the zero colouring and the bone colouring
survive the triangle constraints: the tetrahedra through the edge force the colours of their two bone triangles to be
equal (their sum with the two other legs, which are `0`, is even), and the virtual spin is forced to be `boneLf`.
The sign of the bone term is `1` (`linkSign_bone`). This generalises `signedSum_col0`
(the edge `{0, 1}`) to every edge.
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The `i`-th leg of the tetrahedron `univ \ {p, p'}` (with `p' = p.succAbove a`): the triangle omitting its `i`-th vertex. -/
def legT (p p' : Fin 6) (a : Fin 5) (i : Fin 4) : Finset (Fin 6) := univ \ {p, p', p.succAbove (a.succAbove i)}

/-- A triangle containing the edge `{u, w}` is `{u, w, x}`. -/
lemma tri_bone_eq_gen : ∀ u w : Fin 6, u ≠ w → ∀ f : Finset (Fin 6), #f = 3 → ({u, w} : Finset (Fin 6)) ⊆ f →
    ∃ x : Fin 6, x ≠ u ∧ x ≠ w ∧ f = {u, w, x} := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The tetrahedron `{u, w, x, y}` has two legs `{u, w, x}` and `{u, w, y}` through the edge and no other. -/
lemma legs_bone_pair : ∀ u w : Fin 6, u ≠ w → ∀ (p p' : Fin 6) (a : Fin 5) (x y : Fin 6), p ≠ p' →
    p.succAbove a = p' → univ \ {p, p'} = ({u, w, x, y} : Finset (Fin 6)) → x ≠ y → x ≠ u → x ≠ w → y ≠ u →
    y ≠ w → ∃ i j : Fin 4, i ≠ j ∧ legT p p' a i = {u, w, x} ∧ legT p p' a j = {u, w, y} ∧
      ∀ k : Fin 4, k ≠ i → k ≠ j → ¬ ({u, w} : Finset (Fin 6)) ⊆ legT p p' a k := by
  unfold legT; decide +kernel


set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The virtual spin is forced**: the triangle constraints at the legs of the bone colouring leave only `boneLf`. -/
lemma bone_forced : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    ∀ L : Fin 3, Lightlike.Pentagon.Tri (boneB u w (legT p p' a 0)) (boneB u w (legT p p' a 2)) L.val →
      Lightlike.Pentagon.Tri L.val (boneB u w (legT p p' a 1)) (boneB u w (legT p p' a 3)) →
        L.val = boneLf u w (univ \ {p, p'}) := by
  unfold Lightlike.Pentagon.Tri boneB boneLf legT; decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The virtual spin `boneLf` of a tetrahedron is in the box of its positions. -/
lemma boneLf_mem_box : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    boneLf u w (univ \ {p, p'}) ∈
      simpBox (fun x y => boneB u w (univ \ {p, p.succAbove x, p.succAbove y})) a := by
  unfold simpBox boneB boneLf; decide +kernel

lemma boneB_zero_of_not_sub {u w : Fin 6} {f : Finset (Fin 6)} (h : ¬ ({u, w} : Finset (Fin 6)) ⊆ f) :
    boneB u w f = 0 := by
  unfold boneB; rw [if_neg]; exact fun h' => h h'.1

lemma boneB_le_one (u w : Fin 6) (f : Finset (Fin 6)) : boneB u w f ≤ 1 := by
  unfold boneB; split_ifs <;> simp

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
lemma card_four : ∀ u w x y : Fin 6, u ≠ w → x ≠ u → x ≠ w → y ≠ u → y ≠ w → x ≠ y →
    #({u, w, x, y} : Finset (Fin 6)) = 4 := by
  decide +kernel

/-- **The colours of the bone triangles agree** whenever the triangle constraints hold: for the tetrahedron `{u, w, x, y}`
the two legs through the edge are the only ones that can be nonzero, and the sum of the four legs is even. -/
lemma bone_const_gen (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ) (hle : ∀ f, g f ≤ boneB u w f)
    (L : sphere6.tets → ℕ) (hI : ∀ t, IndP e g L t) (x y : Fin 6) (hx : x ≠ u) (hxw : x ≠ w) (hy : y ≠ u)
    (hyw : y ≠ w) (hxy : x ≠ y) : g {u, w, x} = g {u, w, y} := by
  have huw' : u ≠ w := ne_of_lt huw
  let t : sphere6.tets := ⟨{u, w, x, y}, mem_tets_sphere6.2 (card_four u w x y huw' hx hxw hy hyw hxy)⟩
  obtain ⟨p, p', hne, hs, ht, hl⟩ := sphere6_legs e he t g
  obtain ⟨i, j, hij, hi, hj, hk⟩ := legs_bone_pair u w huw' p p' (e (t, false)).2 x y hne hs ht.symm hxy hx hxw hy hyw
  have hleg : ∀ k : Fin 4, legJ e g t k = g (legT p p' (e (t, false)).2 k) := fun k => hl k
  have hz : ∀ k : Fin 4, k ≠ i → k ≠ j → legJ e g t k = 0 := fun k hki hkj => by
    rw [hleg]
    have := hle (legT p p' (e (t, false)).2 k)
    rw [boneB_zero_of_not_sub (hk k hki hkj)] at this
    omega
  have hsum : ∑ k : Fin 4, legJ e g t k = legJ e g t i + legJ e g t j :=
    Finset.sum_eq_add i j hij (fun k _ h => hz k h.1 h.2) (fun h => absurd (mem_univ i) h)
      (fun h => absurd (mem_univ j) h)
  rw [Fin.sum_univ_four] at hsum
  obtain ⟨h1, h2⟩ := hI t
  unfold Lightlike.Pentagon.Tri at h1 h2
  have hgi : legJ e g t i = g {u, w, x} := by rw [hleg, hi]
  have hgj : legJ e g t j = g {u, w, y} := by rw [hleg, hj]
  have bx := (hle {u, w, x}).trans (boneB_le_one u w _)
  have by' := (hle {u, w, y}).trans (boneB_le_one u w _)
  rw [hgi, hgj] at hsum
  omega


lemma ex_third : ∀ u w : Fin 6, u ≠ w → ∃ x : Fin 6, x ≠ u ∧ x ≠ w := by decide

lemma ex_bone_tri : ∀ u w : Fin 6, u ≠ w → ∃ f : Finset (Fin 6), #f = 3 ∧ ({u, w} : Finset (Fin 6)) ⊆ f := by
  decide +kernel

/-- **The colours of the bone triangles are all `0` or all `1`** if they are pairwise equal. -/
lemma g_of_const_gen (u w : Fin 6) (huw : u ≠ w) (g : Finset (Fin 6) → ℕ) (hle : ∀ f, g f ≤ boneB u w f)
    (hconst : ∀ x y : Fin 6, x ≠ u → x ≠ w → y ≠ u → y ≠ w → x ≠ y → g {u, w, x} = g {u, w, y}) :
    (∀ f, #f = 3 → g f = 0) ∨ (∀ f, #f = 3 → g f = boneB u w f) := by
  obtain ⟨x0, hx0u, hx0w⟩ := ex_third u w huw
  have hb : ∀ f : Finset (Fin 6), #f = 3 → ({u, w} : Finset (Fin 6)) ⊆ f → g f = g {u, w, x0} := by
    intro f hf hsub
    obtain ⟨x, hx, hxw, rfl⟩ := tri_bone_eq_gen u w huw f hf hsub
    by_cases h : x = x0
    · rw [h]
    · exact hconst x x0 hx hxw hx0u hx0w h
  have hnb : ∀ f : Finset (Fin 6), ¬ ({u, w} : Finset (Fin 6)) ⊆ f → g f = 0 := by
    intro f hf
    have := hle f
    rw [boneB_zero_of_not_sub hf] at this; omega
  have hv : g {u, w, x0} ≤ 1 := (hle _).trans (boneB_le_one u w _)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hv with h | h
  · left
    intro f hf
    by_cases hs : ({u, w} : Finset (Fin 6)) ⊆ f
    · rw [hb f hf hs, h]
    · exact hnb f hs
  · right
    intro f hf
    by_cases hs : ({u, w} : Finset (Fin 6)) ⊆ f
    · rw [hb f hf hs, h]
      unfold boneB; rw [if_pos ⟨hs, by omega, by omega⟩]
    · rw [hnb f hs, boneB_zero_of_not_sub hs]

/-- **The virtual spin is forced at the bone colouring**: `L t = boneLf` at every tetrahedron. -/
lemma L_eq_bone (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ) (hg : ∀ f, #f = 3 → g f = boneB u w f)
    (L : sphere6.tets → ℕ) (t : sphere6.tets) (hI : IndP e g L t) : L t = boneLf u w t.1 := by
  obtain ⟨p, p', hne, hs, ht, hl⟩ := sphere6_legs e he t g
  have hleg : ∀ k : Fin 4, legJ e g t k = boneB u w (legT p p' (e (t, false)).2 k) := fun k => by
    have h := hl k
    unfold legJ
    rw [h]
    exact hg _ (legs_card p p' (e (t, false)).2 k hne hs)
  obtain ⟨h1, h2⟩ := hI
  rw [hleg 0, hleg 2] at h1
  rw [hleg 1, hleg 3] at h2
  have b0 := boneB_le_one u w (legT p p' (e (t, false)).2 0)
  have b2 := boneB_le_one u w (legT p p' (e (t, false)).2 2)
  have hlt : L t < 3 := by
    unfold Lightlike.Pentagon.Tri at h1
    omega
  have := bone_forced u w huw p p' (e (t, false)).2 hne hs ⟨L t, hlt⟩ h1 h2
  rw [ht]
  exact this

/-- The virtual spin `boneLf` of a tetrahedron is in the box of each of its two incidences. -/
lemma mem_box_bone (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ) (hg : ∀ f, #f = 3 → g f = boneB u w f)
    (t : sphere6.tets) (b : Bool) :
    boneLf u w t.1 ∈ simpBox (complexJ sphere6 g (e (t, b)).1) (e (t, b)).2 := by
  obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
  have ht : t.1 = univ \ {p, p'} := by
    have h := congrArg Subtype.val (he t false)
    have h' : incSet sphere6 (e (t, false)) = t.1 := h
    rw [incSet_sphere6 _ p h1] at h'
    rw [← h', hs]
    ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  have hJ : ∀ (q : Fin 6) (s : sphere6.simps), s.1 = univ.erase q → ∀ x y : Fin 5, x ≠ y →
      complexJ sphere6 g s x y = boneB u w (univ \ {q, q.succAbove x, q.succAbove y}) := fun q s hq x y hxy => by
    rw [complexJ_sphere6 g s q hq, hg _ (card_tri_sphere6 q x y hxy)]
  cases b
  · rw [simpBox_congr (hJ p _ h1), ht]
    exact boneLf_mem_box u w huw p p' _ hne hs
  · rw [simpBox_congr (hJ p' _ h2), ht, Finset.pair_comm p p']
    exact boneLf_mem_box u w huw p' p _ hne.symm hs'


/-- The colouring of the faces of the bone colouring of the edge `{u, w}`: `boneB` on the triangles, the forced virtual
spin `boneLf` on the tetrahedra. -/
def boneFull (u w : Fin 6) (f : Finset (Fin 6)) : ℕ :=
  if #f = 3 then boneB u w f else if #f = 4 then boneLf u w f else 0

/-- The total triangle part of the signs of the six simplices of `sphere6` at the bone colouring of any edge is even
(the part of one simplex is odd for some edges). -/
lemma boneB_triPart_sum_even : ∀ u w : Fin 6, u < w →
    Even (∑ p : Fin 6, (boneB u w (univ \ {p, p.succAbove 1, p.succAbove 2}) +
      boneB u w (univ \ {p, p.succAbove 1, p.succAbove 4}) + boneB u w (univ \ {p, p.succAbove 3, p.succAbove 4}) +
      boneB u w (univ \ {p, p.succAbove 0, p.succAbove 2}) + boneB u w (univ \ {p, p.succAbove 0, p.succAbove 4}) +
      boneB u w (univ \ {p, p.succAbove 2, p.succAbove 4}))) := by
  unfold boneB; decide +kernel

lemma erase_univ_inj : ∀ p q : Fin 6, (univ.erase p : Finset (Fin 6)) = univ.erase q → p = q := by decide +kernel

lemma erase_mem_simps : ∀ p : Fin 6, (univ.erase p : Finset (Fin 6)) ∈ sphere6.simps := by decide +kernel

/-- The simplices of `sphere6` are indexed by the omitted vertex. -/
noncomputable def simpEquiv6 : sphere6.simps ≃ Fin 6 where
  toFun s := (sphere6_simp_eq s).choose
  invFun p := ⟨univ.erase p, erase_mem_simps p⟩
  left_inv s := Subtype.ext (sphere6_simp_eq s).choose_spec.symm
  right_inv p := (erase_univ_inj _ _ (sphere6_simp_eq ⟨univ.erase p, erase_mem_simps p⟩).choose_spec).symm

/-- **The sign of the link orientations of the bone colouring of any edge is `1`.** -/
theorem linkSign_bone (u w : Fin 6) (huw : u < w) (g : Finset (Fin 6) → ℕ) (hg : ∀ f, #f = 3 → g f = boneB u w f) :
    linkSign sphere6 g = 1 := by
  unfold linkSign
  have h : ∑ s : sphere6.simps, triPart (complexJ sphere6 g s) =
      ∑ p : Fin 6, (boneB u w (univ \ {p, p.succAbove 1, p.succAbove 2}) +
        boneB u w (univ \ {p, p.succAbove 1, p.succAbove 4}) + boneB u w (univ \ {p, p.succAbove 3, p.succAbove 4}) +
        boneB u w (univ \ {p, p.succAbove 0, p.succAbove 2}) + boneB u w (univ \ {p, p.succAbove 0, p.succAbove 4}) +
        boneB u w (univ \ {p, p.succAbove 2, p.succAbove 4})) := by
    rw [← Equiv.sum_comp simpEquiv6.symm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : (simpEquiv6.symm p).1 = univ.erase p := rfl
    unfold triPart
    rw [complexJ_sphere6 g _ p hp, complexJ_sphere6 g _ p hp, complexJ_sphere6 g _ p hp,
      complexJ_sphere6 g _ p hp, complexJ_sphere6 g _ p hp, complexJ_sphere6 g _ p hp,
      hg _ (card_tri_sphere6 p 1 2 (by decide)), hg _ (card_tri_sphere6 p 1 4 (by decide)),
      hg _ (card_tri_sphere6 p 3 4 (by decide)), hg _ (card_tri_sphere6 p 0 2 (by decide)),
      hg _ (card_tri_sphere6 p 0 4 (by decide)), hg _ (card_tri_sphere6 p 2 4 (by decide))]
  rw [h]
  exact Even.neg_one_pow (boneB_triPart_sum_even u w huw)

/-- **The Ooguri sum of the bone cutoff of the edge `{u, w}` has two terms**: the zero colouring and the bone colouring,
both with the sign `1` of the link orientations (`linkSign_bone`). For `{0, 1}` this is `signedSum_col0`. -/
theorem signedSum_bone (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (W : (Finset (Fin 6) → ℕ) → ℝ)
    (hW : ∀ col col' : Finset (Fin 6) → ℕ, (∀ f ∈ colFaces sphere6, col f = col' f) → W col = W col') :
    signedSum sphere6 (boneB u w) e W =
      W (fun _ => 0) + W (boneFull u w) := by
  classical
  have huw' : u ≠ w := ne_of_lt huw
  have hTm : ∀ f, f ∈ sphere6.tris ↔ #f = 3 := fun f => mem_tris_sphere6
  have hcolF : ∀ f, f ∈ colFaces sphere6 → f ∈ sphere6.tris ∨ f ∈ sphere6.tets := fun f hf => by
    unfold colFaces at hf; exact mem_union.1 hf
  unfold signedSum
  generalize sphere6.tris = T at hTm hcolF ⊢
  set c0 : ∀ f ∈ T, ℕ := fun _ _ => 0 with hc0
  set c1 : ∀ f ∈ T, ℕ := fun f _ => boneB u w f with hc1
  have hm0 := mem_pi_of_le (S := T) (cut := boneB u w) c0 (fun f hf => Nat.zero_le _)
  have hm1 := mem_pi_of_le (S := T) (cut := boneB u w) c1 (fun f hf => le_refl _)
  obtain ⟨f0, hf0, hf0s⟩ := ex_bone_tri u w huw'
  have hf0T : f0 ∈ T := (hTm f0).2 hf0
  have hb0 : boneB u w f0 = 1 := by
    unfold boneB; rw [if_pos ⟨hf0s, by omega, by omega⟩]
  have hne : c0 ≠ c1 := by
    intro h
    have := congrFun (congrFun h f0) hf0T
    simp only [c0, c1, hb0] at this
    omega
  have g0 : ∀ f, Lightlike.PR.extS T c0 f = 0 := fun f => by
    unfold Lightlike.PR.extS; split_ifs <;> rfl
  have g1 : ∀ f, #f = 3 → Lightlike.PR.extS T c1 f = boneB u w f := fun f hf => by
    rw [extS_of_mem c1 ((hTm f).2 hf)]
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
  have hW1 : ∀ L : sphere6.tets → ℕ, (∀ t, L t = boneLf u w t.1) →
      W (extL sphere6 (Lightlike.PR.extS T c1) L) = W (boneFull u w) := fun L hL =>
    hW _ _ fun f hf => by
      rcases hcolF f hf with h | h
      · unfold extL; rw [dif_neg]
        · rw [g1 f ((hTm f).1 h)]
          unfold boneFull; rw [if_pos ((hTm f).1 h)]
        intro ht
        have := (hTm f).1 h
        have := mem_tets_sphere6.1 ht
        omega
      · unfold extL; rw [dif_pos h, hL ⟨f, h⟩]
        have h4 := mem_tets_sphere6.1 h
        unfold boneFull; rw [if_neg (by omega), if_pos h4]
  have hbone : ∀ c ∈ T.pi (fun f => range (boneB u w f + 1)), c ≠ c0 → c ≠ c1 →
      ∀ L : sphere6.tets → ℕ, ¬ ∀ t, IndP e (Lightlike.PR.extS T c) L t := by
    intro c hc h0 h1 L hI
    have hle : ∀ f, Lightlike.PR.extS T c f ≤ boneB u w f := extS_le (S := T) (cut := boneB u w) c hc
    have hconst := fun x y hx hxw hy hyw hxy =>
      bone_const_gen u w huw e he (Lightlike.PR.extS T c) hle L hI x y hx hxw hy hyw hxy
    rcases g_of_const_gen u w huw' _ hle hconst with hz | hb
    · apply h0; funext f hf
      rw [← extS_of_mem c hf]; exact hz f ((hTm f).1 hf)
    · apply h1; funext f hf
      rw [← extS_of_mem c hf]; exact hb f ((hTm f).1 hf)
  have hI0 : ∀ t, IndP e (Lightlike.PR.extS T c0) (fun _ => 0) t := fun t => by
    unfold IndP Lightlike.Pentagon.Tri
    rw [legJ_zero e _ g0 t 0, legJ_zero e _ g0 t 1, legJ_zero e _ g0 t 2, legJ_zero e _ g0 t 3]
    dsimp only
    omega
  have hI1 : ∀ t, IndP e (Lightlike.PR.extS T c1) (fun t => boneLf u w t.1) t :=
    fun t => bone_admitted u w huw e he _ g1 t
  refine (Finset.sum_eq_add c0 c1 hne ?_ ?_ ?_).trans ?_
  · intro c hc ⟨hc0', hc1'⟩
    refine Finset.sum_eq_zero fun L _ => ?_
    rw [prod_ind_eq_zero e _ L (hbone c hc hc0' hc1' L), zero_mul]
  · intro h; exact absurd hm0 h
  · intro h; exact absurd hm1 h
  refine congrArg₂ (· + ·) ?_ ?_
  · refine (Finset.sum_eq_single (fun _ => (0 : ℕ)) ?_ ?_).trans ?_
    · intro L _ hL
      rw [prod_ind_eq_zero e _ L (fun h => hL (funext fun t => L_eq_zero e _ g0 L t (h t))), zero_mul]
    · intro hmem
      exact absurd (Fintype.mem_piFinset.2 fun t => mem_inter.2 ⟨zero_mem_box _ _, zero_mem_box _ _⟩) hmem
    · rw [prod_ind_eq_one e _ _ hI0, linkSign_eq_one _ (triPart_even_zero _ g0), one_mul, one_mul]
      exact hW0 _ fun t => rfl
  · refine (Finset.sum_eq_single (fun t => boneLf u w t.1) ?_ ?_).trans ?_
    · intro L _ hL
      rw [prod_ind_eq_zero e _ L (fun h => hL (funext fun t => L_eq_bone u w huw e he _ g1 L t (h t))), zero_mul]
    · intro hmem
      exact absurd (Fintype.mem_piFinset.2 fun t => mem_inter.2
        ⟨mem_box_bone u w huw e he _ g1 t false, mem_box_bone u w huw e he _ g1 t true⟩) hmem
    · rw [prod_ind_eq_one e _ _ hI1, linkSign_bone u w huw _ g1, one_mul, one_mul]
      exact hW1 _ fun t => rfl

end Lightlike.SpinFoam.EPRLStateSum.Trust
