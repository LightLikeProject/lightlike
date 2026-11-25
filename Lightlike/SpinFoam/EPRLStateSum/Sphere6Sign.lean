import Lightlike.SpinFoam.EPRLStateSum.ComplexIntrinsicAmp
import Lightlike.FourD.Tests

/-!
# The global sign of the EPRL (γ = 1) amplitude on the boundary of the 5-simplex

On the smallest closed 4-complex `sphere6` (the boundary of the 5-simplex on `Fin 6`) the global sign
`eprlGlobalSign` of `eprlIntrinsicAmp_eq_signed_ooguri` is made explicit.  The simplices are `univ.erase p`,
the tetrahedra are `univ \ {p, p'}` (`p ≠ p'`), and the two incidences of such a tetrahedron are the
simplices `univ.erase p` and `univ.erase p'` with the positions `a = rank of p'` in `univ.erase p` and
`a' = rank of p` in `univ.erase p'` (`sphere6_positions`: `p.succAbove a = p'`, `p'.succAbove a' = p`).
With `u < w` the two vertices of the complement, the positions are `{u, w - 1}`, so the sign type of the
tetrahedron is the explicit `pairTypeU, pairTypeV` of `{u, w}`; the tetrahedron factor is `1` for the six
pairs `{u, u+1}` and `{0, 5}`, and for the nine others it is `(-1)^(cU e₁ + cV e₃)` with the table
`sphere6_type_table`.  The triangle part `(-1)^(Σ_s triPart)` is as in `eprlGlobalSign`.

So `Z_EPRL = Σ_{col, L} [triangle constraints] · sign · Z_Ooguri(col, L)` with an explicit sign
(`eprlIntrinsicAmp_sphere6`).  The sign is not `1`: it is a product of face parities and, for nine of the fifteen
tetrahedra, tetrahedron parities (Choice A of the owner decision on G2-024 keeps the sign in the statement).
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

/-- Every 4-simplex of `sphere6` is `univ.erase p`. -/
lemma sphere6_simp_eq (s : sphere6.simps) : ∃ p : Fin 6, s.1 = univ.erase p := by
  have hc : #s.1 = 5 := sphere6.card_eq _ s.2
  have h1 : #(s.1ᶜ) = 1 := by
    rw [Finset.card_compl, hc]; rfl
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  refine ⟨p, ?_⟩
  ext y
  have := congrArg (y ∈ ·) hp
  simp only [Finset.mem_compl, Finset.mem_singleton, eq_iff_iff] at this
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- The sorted embedding of `univ.erase p` is `p.succAbove`. -/
lemma orderEmbOfFin_erase (p : Fin 6) (h : #(univ.erase p) = 5) (a : Fin 5) :
    (univ.erase p).orderEmbOfFin h a = p.succAbove a :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := p.succAbove)
    (fun x => by simp) (Fin.strictMono_succAbove p)) a).symm

/-- The tetrahedron of the incidence `(univ.erase p, a)` is `(univ.erase p).erase (p.succAbove a)`. -/
lemma incSet_sphere6 (x : sphere6.simps × Fin 5) (p : Fin 6) (hp : x.1.1 = univ.erase p) :
    incSet sphere6 x = (univ.erase p).erase (p.succAbove x.2) := by
  unfold incSet
  have h5 : #(univ.erase p) = 5 := by simp
  have : x.1.1.orderEmbOfFin (sphere6.card_eq _ x.1.2) x.2 = p.succAbove x.2 := by
    have key : ∀ (s : Finset (Fin 6)) (hs : s = univ.erase p) (h : #s = 5),
        s.orderEmbOfFin h x.2 = p.succAbove x.2 := by
      rintro s rfl h
      exact orderEmbOfFin_erase p h x.2
    exact key _ hp _
  rw [this, hp]

/-- Brute-force: two incidences with the same tetrahedron have distinct simplices, and each simplex omits the
vertex that the other one lacks. -/
lemma sphere6_pair_decide : ∀ (p p' : Fin 6) (a a' : Fin 5),
    (univ.erase p).erase (p.succAbove a) = (univ.erase p').erase (p'.succAbove a') →
      (p = p' → a = a') ∧ (p ≠ p' → p.succAbove a = p' ∧ p'.succAbove a' = p) := by
  decide +kernel

/-- **Positions of a tetrahedron of `sphere6`.** For any incidence bijection `e`, the two incidences of a
tetrahedron lie in the simplices `univ.erase p`, `univ.erase p'` with `p ≠ p'`, and their positions satisfy
`p.succAbove a = p'`, `p'.succAbove a' = p`. -/
theorem sphere6_positions (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (t : sphere6.tets) :
    ∃ p p' : Fin 6, (e (t, false)).1.1 = univ.erase p ∧ (e (t, true)).1.1 = univ.erase p' ∧ p ≠ p' ∧
      p.succAbove (e (t, false)).2 = p' ∧ p'.succAbove (e (t, true)).2 = p := by
  obtain ⟨p, hp⟩ := sphere6_simp_eq (e (t, false)).1
  obtain ⟨p', hp'⟩ := sphere6_simp_eq (e (t, true)).1
  have h1 := congrArg Subtype.val (he t false)
  have h2 := congrArg Subtype.val (he t true)
  have h12 : incSet sphere6 (e (t, false)) = incSet sphere6 (e (t, true)) := h1.trans h2.symm
  rw [incSet_sphere6 _ p hp, incSet_sphere6 _ p' hp'] at h12
  have hd := sphere6_pair_decide p p' _ _ h12
  have hne : p ≠ p' := by
    intro hpp
    have ha := hd.1 hpp
    have : e (t, false) = e (t, true) := by
      refine Prod.ext (Subtype.ext ?_) ha
      rw [hp, hp', hpp]
    have := e.injective this
    simp at this
  exact ⟨p, p', hp, hp', hne, (hd.2 hne).1, (hd.2 hne).2⟩

/-- First coordinate of the sign type of the pair of positions of the tetrahedron `univ \ {p, p'}`
(natural-number version of `sgnU`). -/
def tU (r : ℕ) : ℕ := if r = 1 ∨ r = 2 then 1 else 0

/-- Second coordinate (natural-number version of `sgnV`). -/
def tV (r : ℕ) : ℕ := if r = 3 ∨ r = 2 then 1 else 0

/-- The sum `εU` of the first sign types of the two positions of the tetrahedron `univ \ {p, p'}`: the positions
are `{min, max - 1}`. -/
def pairTypeU (p p' : Fin 6) : ℕ :=
  if p < p' then tU p.val + tU (p'.val - 1) else tU p'.val + tU (p.val - 1)

/-- The sum `εV` of the second sign types of the two positions. -/
def pairTypeV (p p' : Fin 6) : ℕ :=
  if p < p' then tV p.val + tV (p'.val - 1) else tV p'.val + tV (p.val - 1)

/-- The explicit sign types of the positions. -/
lemma sphere6_types : ∀ (p p' : Fin 6) (a a' : Fin 5), p ≠ p' → p.succAbove a = p' →
    p'.succAbove a' = p →
      sgnU a + sgnU a' = pairTypeU p p' ∧ sgnV a + sgnV a' = pairTypeV p p' := by
  unfold sgnU sgnV pairTypeU pairTypeV tU tV
  decide +kernel

/-- The tetrahedron factor is `1` when the complement pair is `{u, u+1}` or `{0, 5}`: the two positions have
the same sign type. -/
lemma sphere6_trivial_types : ∀ (p p' : Fin 6) (a a' : Fin 5), p ≠ p' → p.succAbove a = p' →
    p'.succAbove a' = p → (p.val + 1 = p'.val ∨ p'.val + 1 = p.val ∨ (p.val = 0 ∧ p'.val = 5) ∨
      (p'.val = 0 ∧ p.val = 5)) → sgnU a = sgnU a' ∧ sgnV a = sgnV a' := by
  unfold sgnU sgnV
  decide +kernel

/-- **The table of the nine nontrivial tetrahedron types** (`u < w` the complement vertices): the pair
`(εU, εV) mod 2` of `pairType` for `{u, w}`. -/
lemma sphere6_type_table : ∀ (u w : Fin 6), u < w →
    (((pairTypeU u w % 2, pairTypeV u w % 2) = (1, 0)) ↔
        ((u.val, w.val) = (0, 2) ∨ (u.val, w.val) = (1, 5) ∨ (u.val, w.val) = (2, 4))) ∧
    (((pairTypeU u w % 2, pairTypeV u w % 2) = (1, 1)) ↔
        ((u.val, w.val) = (0, 3) ∨ (u.val, w.val) = (1, 4) ∨ (u.val, w.val) = (2, 5))) ∧
    (((pairTypeU u w % 2, pairTypeV u w % 2) = (0, 1)) ↔
        ((u.val, w.val) = (0, 4) ∨ (u.val, w.val) = (1, 3) ∨ (u.val, w.val) = (3, 5))) ∧
    (((pairTypeU u w % 2, pairTypeV u w % 2) = (0, 0)) ↔
        (u.val + 1 = w.val ∨ (u.val = 0 ∧ w.val = 5))) := by
  unfold pairTypeU pairTypeV tU tV
  decide +kernel

/-- **The tetrahedron factor of the global sign on `sphere6` is explicit**: with `p, p'` the omitted vertices of
the two incidences of `t`, it is `(-1)^(εU e₁ + εV e₃)` with `εU = pairTypeU p p'`, `εV = pairTypeV p p'`
(modulo `2` the table `sphere6_type_table`), and it is `1` when `{p, p'}` is `{u, u+1}` or `{0, 5}`. -/
theorem sphere6_tetFactor (col : Finset (Fin 6) → ℕ) (L : sphere6.tets → ℕ)
    (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (t : sphere6.tets) :
    ∃ p p' : Fin 6, p ≠ p' ∧ (e (t, false)).1.1 = univ.erase p ∧ (e (t, true)).1.1 = univ.erase p' ∧
      (-1 : ℝ) ^ ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) * tetE1 sphere6 col L e t +
          (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 sphere6 col L e t) =
        (-1 : ℝ) ^ (pairTypeU p p' * tetE1 sphere6 col L e t + pairTypeV p p' * tetE3 sphere6 col L e t) ∧
      ((p.val + 1 = p'.val ∨ p'.val + 1 = p.val ∨ (p.val = 0 ∧ p'.val = 5) ∨
        (p'.val = 0 ∧ p.val = 5)) →
        (-1 : ℝ) ^ (pairTypeU p p' * tetE1 sphere6 col L e t +
          pairTypeV p p' * tetE3 sphere6 col L e t) = 1) := by
  obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
  obtain ⟨hU, hV⟩ := sphere6_types p p' _ _ hne hs hs'
  refine ⟨p, p', hne, h1, h2, by rw [hU, hV], fun hadj => ?_⟩
  obtain ⟨hU', hV'⟩ := sphere6_trivial_types p p' _ _ hne hs hs' hadj
  have := tetPairSign_of_type sphere6 col L e t hU' hV'
  rwa [hU, hV] at this

/-- The omitted vertex of a 5-element subset of `Fin 6` (the largest vertex not in it). -/
def omitted (s : Finset (Fin 6)) : Fin 6 := ((univ.filter (· ∉ s)).max).unbotD 0

lemma omitted_erase : ∀ p : Fin 6, omitted (univ.erase p) = p := by
  unfold omitted
  decide +kernel

/-- **The explicit global sign on `sphere6`**: the face part times, over the tetrahedra, `(-1)^(εU e₁ + εV e₃)`
with `εU, εV = pairTypeU, pairTypeV` of the omitted vertices of the two incidences of the tetrahedron
(`sphere6_tetFactor`: trivial for the pairs `{u, u+1}` and `{0, 5}`). -/
theorem eprlGlobalSign_sphere6 (col : Finset (Fin 6) → ℕ) (L : sphere6.tets → ℕ)
    (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) :
    eprlGlobalSign sphere6 col L e =
      (-1 : ℝ) ^ (∑ s : sphere6.simps, triPart (complexJ sphere6 col s)) *
        ∏ t : sphere6.tets, (-1 : ℝ) ^
          (pairTypeU (omitted (e (t, false)).1.1) (omitted (e (t, true)).1.1) *
              tetE1 sphere6 col L e t +
            pairTypeV (omitted (e (t, false)).1.1) (omitted (e (t, true)).1.1) *
              tetE3 sphere6 col L e t) := by
  unfold eprlGlobalSign
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  obtain ⟨p, p', -, h1, h2, h, -⟩ := sphere6_tetFactor col L e he t
  rw [h, h1, h2, omitted_erase, omitted_erase]

/-- **Z_EPRL = signed Z_Ooguri on the boundary of the 5-simplex.** For an incidence bijection `e` (it exists), the
intrinsic EPRL (γ = 1) amplitude is the sum over triangle colourings and virtual spins of the triangle constraints
times the sign `eprlGlobalSign` (explicit by `eprlGlobalSign_sphere6`) times the Ooguri weight of the coloured
complex. -/
theorem eprlIntrinsicAmp_sphere6 (cut : Finset (Fin 6) → ℕ) :
    ∃ e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5, (∀ t b, incTet sphere6 (e (t, b)) = t) ∧
      eprlIntrinsicAmp sphere6 cut e =
        ∑ c ∈ sphere6.tris.pi (fun f => range (cut f + 1)),
          ∑ L ∈ Fintype.piFinset (fun t : sphere6.tets =>
              simpBox (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1)
                  (e (t, false)).2 ∩
                simpBox (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, true)).1)
                  (e (t, true)).2),
            (∏ t : sphere6.tets, if
                Lightlike.Pentagon.Tri
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 0))
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 2))
                  (L t) ∧
                Lightlike.Pentagon.Tri (L t)
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 1))
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 3))
              then (1 : ℝ) else 0) *
              (eprlGlobalSign sphere6 (Lightlike.PR.extS sphere6.tris c) L e *
                Lightlike.SpinFoam.weight sphere6
                  (extL sphere6 (Lightlike.PR.extS sphere6.tris c) L)) := by
  obtain ⟨e, he⟩ := exists_complex_incidence sphere6 sphere6_checks.2.2
  exact ⟨e, he, eprlIntrinsicAmp_eq_signed_ooguri sphere6 cut e he⟩

/-! ### Non-vacuity: the sign types are not all trivial -/

example : (pairTypeU 0 2 % 2, pairTypeV 0 2 % 2) = (1, 0) := by decide
example : (pairTypeU 1 4 % 2, pairTypeV 1 4 % 2) = (1, 1) := by decide
example : (pairTypeU 3 5 % 2, pairTypeV 3 5 % 2) = (0, 1) := by decide
example : (pairTypeU 0 5 % 2, pairTypeV 0 5 % 2) = (0, 0) := by decide
example : (pairTypeU 2 3 % 2, pairTypeV 2 3 % 2) = (0, 0) := by decide

end Lightlike.SpinFoam.EPRLStateSum

