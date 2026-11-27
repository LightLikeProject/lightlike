import Lightlike.FourD.Boundary

/-!
# The link of an edge of a closed complex carries an even colour sum

For a closed 4-complex `K` and a colouring `col` of its triangles whose four colours around every tetrahedron have an even sum (`TetPar`), the
sum of `col (s ∖ {x, y})` over the 4-simplices `s ∋ x, y` is even, for every two vertices `x ≠ y`: the triangles `f = s ∖ {x, y}` form the link of the
edge `{x, y}`; the sum over the tetrahedra `s ∖ {y}` of the sum of their four colours is even, and counts every triangle of the link once and every
other triangle `(s ∖ {y}) ∖ {v}` twice (each tetrahedron of a closed complex lies in two 4-simplices).
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [DecidableEq V]

/-- The four colours around every tetrahedron have an even sum. -/
def TetPar (K : Complex4 V) (col : Finset V → ℕ) : Prop :=
  ∀ g ∈ K.tets, Even (∑ v ∈ g, col (g.erase v))

lemma erase_mem_tets (K : Complex4 V) {s : Finset V} (hs : s ∈ K.simps) {y : V} (hy : y ∈ s) : s.erase y ∈ K.tets := by
  rw [Complex4.mem_faces]
  refine ⟨s, hs, Finset.erase_subset _ _, ?_⟩
  rw [Finset.card_erase_of_mem hy, K.card_eq s hs]

/-- **The link of an edge**: the sum of the colours of the triangles `s ∖ {x, y}` over the 4-simplices `s ∋ x, y` is even. -/
theorem link_sum_even (K : Complex4 V) (hK : K.IsClosed4) (col : Finset V → ℕ) (hp : TetPar K col) (x y : V) (hxy : x ≠ y) :
    Even (∑ s ∈ K.simps.filter (fun s => x ∈ s ∧ y ∈ s), col ((s.erase x).erase y)) := by
  classical
  set S := K.simps.filter (fun s => x ∈ s ∧ y ∈ s) with hS
  have hSmem : ∀ s ∈ S, s ∈ K.simps ∧ x ∈ s ∧ y ∈ s := fun s hs => by
    rw [hS, Finset.mem_filter] at hs; exact ⟨hs.1, hs.2.1, hs.2.2⟩
  -- the sum of the tetrahedron parities
  have h1 : Even (∑ s ∈ S, ∑ v ∈ s.erase y, col ((s.erase y).erase v)) :=
    Finset.even_sum _ fun s hs => hp (s.erase y) (erase_mem_tets K (hSmem s hs).1 (hSmem s hs).2.2)
  have h2 : ∀ s ∈ S, ∑ v ∈ s.erase y, col ((s.erase y).erase v) =
      col ((s.erase x).erase y) + ∑ v ∈ (s.erase y).erase x, col ((s.erase y).erase v) := by
    intro s hs
    have hx : x ∈ s.erase y := Finset.mem_erase.2 ⟨hxy, (hSmem s hs).2.1⟩
    rw [← Finset.add_sum_erase _ _ hx, Finset.erase_right_comm]
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib] at h1
  -- the second sum counts every triangle twice
  set Q := ∑ s ∈ S, ∑ v ∈ (s.erase y).erase x, col ((s.erase y).erase v) with hQ
  have hQeven : Even Q := by
    set T := K.tets.filter (fun t => x ∈ t ∧ y ∈ t) with hT
    have hTmem : ∀ t ∈ T, t ∈ K.tets ∧ x ∈ t ∧ y ∈ t := fun t ht => by
      rw [hT, Finset.mem_filter] at ht; exact ⟨ht.1, ht.2.1, ht.2.2⟩
    have hQ' : Q = ∑ q ∈ T.sigma (fun t => K.star t), col (q.1.erase y) := by
      rw [hQ, Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => (⟨p.2 |> fun v => p.1.erase v, p.1⟩ : (_ : Finset V) × Finset V)) ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_sigma] at hp ⊢
        obtain ⟨hs, hv⟩ := hp
        obtain ⟨hsK, hxs, hys⟩ := hSmem _ hs
        have hv' : p.2 ∈ p.1 ∧ p.2 ≠ x ∧ p.2 ≠ y := by
          simp only [Finset.mem_erase] at hv
          exact ⟨hv.2.2, hv.1, hv.2.1⟩
        refine ⟨?_, ?_⟩
        · rw [hT, Finset.mem_filter]
          refine ⟨erase_mem_tets K hsK hv'.1, Finset.mem_erase.2 ⟨hv'.2.1.symm, hxs⟩, Finset.mem_erase.2 ⟨hv'.2.2.symm, hys⟩⟩
        · exact Complex4.mem_star.2 ⟨hsK, Finset.erase_subset _ _⟩
      · intro p hp q hq h
        rw [Finset.mem_sigma] at hp hq
        have h1 : p.1 = q.1 := by simpa using congrArg Sigma.snd h
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only at h1
        subst h1
        have h2 : p1.erase p2 = p1.erase q2 := by simpa using congrArg Sigma.fst h
        have hp2 : p2 ∈ p1 := (Finset.mem_erase.1 (Finset.mem_erase.1 hp.2).2).2
        have hq2 : q2 ∈ p1 := (Finset.mem_erase.1 (Finset.mem_erase.1 hq.2).2).2
        have : p2 = q2 := by
          by_contra hne
          have : q2 ∈ p1.erase p2 := Finset.mem_erase.2 ⟨fun e => hne e.symm, hq2⟩
          rw [h2] at this
          exact (Finset.notMem_erase q2 p1) this
        subst this; rfl
      · intro q hq
        rw [Finset.mem_sigma] at hq
        obtain ⟨hqT, hqS⟩ := hq
        obtain ⟨htK, hxt, hyt⟩ := hTmem _ hqT
        obtain ⟨hsK, hts⟩ := Complex4.mem_star.1 hqS
        have hcard : #(q.2 \ q.1) = 1 := by
          rw [Finset.card_sdiff_of_subset hts, K.card_eq _ hsK, Complex4.card_of_mem_faces htK]
        obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hcard
        have hvs : v ∈ q.2 \ q.1 := by rw [hv]; simp
        have hvs' := Finset.mem_sdiff.1 hvs
        refine ⟨⟨q.2, v⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma]
          refine ⟨?_, ?_⟩
          · rw [hS, Finset.mem_filter]; exact ⟨hsK, hts hxt, hts hyt⟩
          · simp only [Finset.mem_erase]
            exact ⟨fun e => hvs'.2 (e ▸ hxt), fun e => hvs'.2 (e ▸ hyt), hvs'.1⟩
        · have : q.2.erase v = q.1 := by
            ext w
            simp only [Finset.mem_erase]
            constructor
            · rintro ⟨hw, hws⟩
              by_contra hwt
              have : w ∈ q.2 \ q.1 := Finset.mem_sdiff.2 ⟨hws, hwt⟩
              rw [hv] at this
              exact hw (Finset.mem_singleton.1 this)
            · intro hw
              exact ⟨fun e => hvs'.2 (e ▸ hw), hts hw⟩
          exact Sigma.ext this (heq_of_eq rfl)
      · intro p hp
        simp only
        rw [Finset.erase_right_comm]
    rw [hQ', Finset.sum_sigma]
    refine Finset.even_sum _ fun t ht => ?_
    obtain ⟨htK, -, -⟩ := hTmem t ht
    show Even (∑ s ∈ K.star t, col (t.erase y))
    rw [Finset.sum_const, hK t htK]
    exact ⟨col (t.erase y), by simp only [smul_eq_mul]; ring⟩
  exact (Nat.even_add.1 h1).2 hQeven

end Lightlike.SpinFoam.EPRLStateSum
