import Lightlike.SpinFoam.EPRLStateSum.BoneAmplitude

/-!
# The dependence of the EPRL state sum on the vertex order: the swap phase of the bone colourings

At `γ = 1` the intrinsic EPRL amplitude is the signed Ooguri sum of `amplitudeI_one_eq_signed_ooguri`: the sum over the
triangle colourings and the virtual spins of the triangle constraints times the explicit sign `eprlGlobalSign` times the
Ooguri weight.  The sign depends on the order of the vertices (through the positions of the omitted vertices of the two
simplices of every tetrahedron).  On `sphere6` the *bone colouring of the edge `{u, w}`* (doubled spin `1` on the
triangles through the edge, virtual spin `boneLf` on the tetrahedra) is admitted by the triangle constraints
(`bone_admitted`) and its sign is

`eprlGlobalSign = (-1)^(w - u - 1)`, the parity of the number of vertices strictly between `u` and `w`
(`eprlGlobalSign_bone`): `+1` for `{u, u+1}` and `{0, 1}`, `-1` for `{0, 2}`.  For `{0, 1}` this is the `+1` used in
`amplitudeI_sphere6_low_spin`.

This is the *stated* dependence of the state sum on the order of the vertices; it is not an independence claim.  What
this file does not prove: the value of the Ooguri weight of the bone colourings of the other edges (it is `4` for
`{0, 1}`, `weight_col0`; the numerical model `scripts/spinfoam/eprl_order_check.py` gives the pure Ooguri amplitude
`5 = 1 + 4` for all fifteen edges, hence the EPRL amplitudes `5` for `w - u` odd and `-3` for `w - u` even) and the invariance of `amplitudeI` under order isomorphisms.
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The bone colouring of the edge `{u, w}`: doubled spin `1` on the triangles and tetrahedra containing it. -/
def boneB (u w : Fin 6) (f : Finset (Fin 6)) : ℕ := if {u, w} ⊆ f ∧ 3 ≤ #f ∧ #f ≤ 4 then 1 else 0

/-- The virtual spin of the bone colouring on a tetrahedron `f`: `1` if `f` contains the edge and the number of
vertices of `f` strictly between `u` and `w` is not `1` (the two bone legs are then in the channels `(0,1)`, `(0,3)`,
`(1,2)` or `(2,3)` of the sorted legs), and `0` otherwise. -/
def boneLf (u w : Fin 6) (f : Finset (Fin 6)) : ℕ :=
  if {u, w} ⊆ f ∧ #(f.filter fun x => u < x ∧ x < w) ≠ 1 then 1 else 0

/-- The bone colouring of `{0, 1}` is `col0`. -/
lemma boneB_zero_one : boneB 0 1 = col0 := rfl

/-- The exponent of the sign of the tetrahedron `univ \ {p, p'}` (first incidence at the position `a`). -/
def tetExp (u w p p' : Fin 6) (a : Fin 5) : ℕ :=
  pairTypeU p p' * tetSignExp 1 (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 0)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 1)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 2)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 3)})) (boneLf u w (univ \ {p, p'})) +
    pairTypeV p p' * tetSignExp 3 (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 0)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 1)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 2)}))
      (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 3)})) (boneLf u w (univ \ {p, p'}))

/-- The exponent of the sign of a tetrahedron as a function of the tetrahedron. -/
def tetExpSym (u w : Fin 6) (f : Finset (Fin 6)) : ℕ :=
  ∑ p : Fin 6, ∑ p' : Fin 6, ∑ a : Fin 5,
    if p < p' ∧ p.succAbove a = p' ∧ univ \ {p, p'} = f then tetExp u w p p' a else 0

/-- The exponent depends on the tetrahedron only: for `p < p'` it is `tetExpSym`. -/
lemma tetExp_lt : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a : Fin 5), p < p' → p.succAbove a = p' →
    tetExp u w p p' a = tetExpSym u w (univ \ {p, p'}) := by
  unfold tetExp tetExpSym pairTypeU pairTypeV tU tV boneB boneLf tetSignExp; decide +kernel

/-- The exponent is symmetric under the exchange of the two simplices of the tetrahedron. -/
lemma tetExp_symm : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a a' : Fin 5), p ≠ p' → p.succAbove a = p' →
    p'.succAbove a' = p → tetExp u w p p' a = tetExp u w p' p a' := by
  unfold tetExp pairTypeU pairTypeV tU tV boneB boneLf tetSignExp; decide +kernel


/-- The triangle part of the sign of the simplex `univ.erase p` at the bone colouring. -/
def triSumP (u w : Fin 6) (p : Fin 6) : ℕ :=
  boneB u w (univ \ {p, p.succAbove 1, p.succAbove 2}) + boneB u w (univ \ {p, p.succAbove 1, p.succAbove 4}) +
    boneB u w (univ \ {p, p.succAbove 3, p.succAbove 4}) + boneB u w (univ \ {p, p.succAbove 0, p.succAbove 2}) +
    boneB u w (univ \ {p, p.succAbove 0, p.succAbove 4}) + boneB u w (univ \ {p, p.succAbove 2, p.succAbove 4})

/-- **The parity of the whole exponent** of the global sign of the bone colouring of `{u, w}` is the parity of the number
`w - u - 1` of vertices strictly between `u` and `w`. -/
lemma total_parity : ∀ u w : Fin 6, u < w →
    (∑ p : Fin 6, triSumP u w p + ∑ f ∈ (univ : Finset (Fin 6)).powersetCard 4, tetExpSym u w f) % 2 =
      (w.val - u.val - 1) % 2 := by
  unfold triSumP tetExpSym tetExp pairTypeU pairTypeV tU tV boneB boneLf tetSignExp; decide +kernel

/-- The legs and the tetrahedron of the first incidence, for given omitted vertices. -/
lemma legs_of_pos (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (t : sphere6.tets) (g : Finset (Fin 6) → ℕ) (p p' : Fin 6) (hs : p.succAbove (e (t, false)).2 = p')
    (h1 : (e (t, false)).1.1 = univ.erase p) (ht' : incSet sphere6 (e (t, false)) = t.1) :
    t.1 = univ \ {p, p'} ∧ ∀ i : Fin 4, complexJ sphere6 g (e (t, false)).1 (e (t, false)).2
        ((e (t, false)).2.succAbove i) = g (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove i)}) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [incSet_sphere6 _ p h1] at ht'
    rw [← ht', hs]
    ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  · rw [complexJ_sphere6 g _ p h1, hs]

/-- The tetrahedra of `sphere6` are the `4`-element subsets. -/
lemma tets_sphere6_eq : sphere6.tets = (univ : Finset (Fin 6)).powersetCard 4 := by
  ext f; rw [mem_tets_sphere6, mem_powersetCard]; simp

/-- The equivalence between the simplices of `sphere6` and the omitted vertices. -/
def simpEquiv : sphere6.simps ≃ Fin 6 where
  toFun s := omitted s.1
  invFun p := ⟨univ.erase p, by
    have h : univ.erase p ∈ (univ : Finset (Fin 6)).powersetCard 5 := by
      rw [mem_powersetCard]; simp
    exact h⟩
  left_inv s := by
    obtain ⟨p, hp⟩ := sphere6_simp_eq s
    apply Subtype.ext
    simp only [hp, omitted_erase]
  right_inv p := omitted_erase p

/-- **The swap phase of the bone colouring.** On the boundary of the 5-simplex, for the bone colouring of the edge
`{u, w}` (`u < w`; doubled spin `1` on the triangles through it) with the virtual spins `boneLf`, the global sign of the
signed Ooguri sum is `(-1)^(w - u - 1)`: the parity of the number of vertices strictly between `u` and `w`. It is `+1`
for `{u, u+1}` (and `{0, 1}`, as used in `amplitudeI_sphere6_low_spin`) and `-1` for `{0, 2}`. -/
theorem eprlGlobalSign_bone (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, #f = 3 → g f = boneB u w f) :
    eprlGlobalSign sphere6 g (fun t => boneLf u w t.1) e = (-1 : ℝ) ^ (w.val - u.val - 1) := by
  unfold eprlGlobalSign
  -- the triangle part
  have hA : ∑ s : sphere6.simps, triPart (complexJ sphere6 g s) = ∑ p : Fin 6, triSumP u w p := by
    have h1 : ∀ s : sphere6.simps, triPart (complexJ sphere6 g s) = triSumP u w (simpEquiv s) := by
      intro s
      obtain ⟨p, hp⟩ := sphere6_simp_eq s
      have hpe : simpEquiv s = p := by simp only [simpEquiv, Equiv.coe_fn_mk, hp, omitted_erase]
      rw [hpe]
      unfold triPart triSumP
      rw [complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp,
        complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp, complexJ_sphere6 g s p hp,
        hg _ (card_tri_sphere6 p 1 2 (by decide)), hg _ (card_tri_sphere6 p 1 4 (by decide)),
        hg _ (card_tri_sphere6 p 3 4 (by decide)), hg _ (card_tri_sphere6 p 0 2 (by decide)),
        hg _ (card_tri_sphere6 p 0 4 (by decide)), hg _ (card_tri_sphere6 p 2 4 (by decide))]
    rw [Finset.sum_congr rfl fun s _ => h1 s]
    exact Equiv.sum_comp simpEquiv (triSumP u w)
  -- the tetrahedron factors
  have hB : ∀ t : sphere6.tets,
      (-1 : ℝ) ^ ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) *
          tetE1 sphere6 g (fun t => boneLf u w t.1) e t +
        (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 sphere6 g (fun t => boneLf u w t.1) e t) =
        (-1 : ℝ) ^ tetExpSym u w t.1 := by
    intro t
    obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
    have ht' : incSet sphere6 (e (t, false)) = t.1 := congrArg Subtype.val (he t false)
    obtain ⟨ht, hl⟩ := legs_of_pos e t g p p' hs h1 ht'
    obtain ⟨hU, hV⟩ := sphere6_types p p' _ _ hne hs hs'
    have hcard := fun i => legs_card p p' (e (t, false)).2 i hne hs
    have e1 : tetE1 sphere6 g (fun t => boneLf u w t.1) e t =
        tetSignExp 1 (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 0)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 1)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 2)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 3)}))
          (boneLf u w (univ \ {p, p'})) := by
      unfold tetE1
      change tetSignExp 1 (legJ e g t 0) (legJ e g t 1) (legJ e g t 2) (legJ e g t 3) (boneLf u w t.1) = _
      unfold legJ
      rw [hl 0, hl 1, hl 2, hl 3, hg _ (hcard 0), hg _ (hcard 1), hg _ (hcard 2), hg _ (hcard 3), ht]
    have e3 : tetE3 sphere6 g (fun t => boneLf u w t.1) e t =
        tetSignExp 3 (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 0)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 1)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 2)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 3)}))
          (boneLf u w (univ \ {p, p'})) := by
      unfold tetE3
      change tetSignExp 3 (legJ e g t 0) (legJ e g t 1) (legJ e g t 2) (legJ e g t 3) (boneLf u w t.1) = _
      unfold legJ
      rw [hl 0, hl 1, hl 2, hl 3, hg _ (hcard 0), hg _ (hcard 1), hg _ (hcard 2), hg _ (hcard 3), ht]
    rw [e1, e3, hU, hV]
    have hexp : pairTypeU p p' * tetSignExp 1 (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 0)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 1)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 2)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 3)}))
          (boneLf u w (univ \ {p, p'})) +
        pairTypeV p p' * tetSignExp 3 (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 0)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 1)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 2)}))
          (boneB u w (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove 3)}))
          (boneLf u w (univ \ {p, p'})) = tetExpSym u w t.1 := by
      change tetExp u w p p' (e (t, false)).2 = _
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [tetExp_lt u w huw p p' _ hlt hs, ht]
      · rw [tetExp_symm u w huw p p' _ _ hne hs hs', tetExp_lt u w huw p' p _ hgt hs', ht,
          Finset.pair_comm]
    rw [hexp]
  rw [Finset.prod_congr rfl fun t _ => hB t, Finset.prod_pow_eq_pow_sum, hA, ← pow_add]
  have hsum : ∑ t : sphere6.tets, tetExpSym u w t.1 =
      ∑ f ∈ (univ : Finset (Fin 6)).powersetCard 4, tetExpSym u w f := by
    rw [Finset.sum_coe_sort sphere6.tets (tetExpSym u w), tets_sphere6_eq]
  rw [hsum, neg_one_pow_eq_pow_mod_two, total_parity u w huw, ← neg_one_pow_eq_pow_mod_two]


/-- The virtual spins `boneLf` satisfy the triangle constraints at the sorted legs of the bone colouring. -/
lemma bone_tri_ok : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    Lightlike.Pentagon.Tri (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 0)}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 2)})) (boneLf u w (univ \ {p, p'})) ∧
      Lightlike.Pentagon.Tri (boneLf u w (univ \ {p, p'}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 1)}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 3)})) := by
  unfold Lightlike.Pentagon.Tri boneB boneLf; decide +kernel

/-- **The bone colouring of any edge is admitted by the triangle constraints**, so its term, with the sign
`eprlGlobalSign_bone`, occurs in the signed Ooguri sum. -/
theorem bone_admitted (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, #f = 3 → g f = boneB u w f) (t : sphere6.tets) :
    IndP e g (fun t => boneLf u w t.1) t := by
  obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
  have ht' : incSet sphere6 (e (t, false)) = t.1 := congrArg Subtype.val (he t false)
  obtain ⟨ht, hl⟩ := legs_of_pos e t g p p' hs h1 ht'
  have hcard := fun i => legs_card p p' (e (t, false)).2 i hne hs
  unfold IndP legJ
  rw [hl 0, hl 1, hl 2, hl 3, hg _ (hcard 0), hg _ (hcard 1), hg _ (hcard 2), hg _ (hcard 3)]
  show _ ∧ _
  have := bone_tri_ok u w huw p p' (e (t, false)).2 hne hs
  rw [← ht] at this
  exact this

end Lightlike.SpinFoam.EPRLStateSum.Trust
