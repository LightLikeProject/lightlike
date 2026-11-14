module

public import Lightlike.PonzanoRegge.Move14
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The gauge-fixed Ponzano–Regge amplitude: exact invariance under the 2-3 and 1-4 moves

The plain state sum diverges: each 1-4 move multiplies it by `Σ_j (2j+1)²`
(`amplitude_move14`). Freidel and Louapre traced the divergence to a residual gauge symmetry and
fixed it by putting **spin 0 on the edges of a maximal tree** `T` (*Class. Quantum Grav.* 21 (2004)
5685). The gauge set here is **modelled on** theirs; the model differs in that Freidel–Louapre also
fix the group variables on the edges of a dual tree `T*`, and there is no `T*` here.
(Barrett–Naish-Guzman, *Class. Quantum Grav.* 26 (2009) 155014, regularise by a cutoff and say
explicitly that they do not interpret it as gauge fixing, so it is not a source for this one.)
A 1-4 move adds one vertex `E` and one tree edge `DE`, so the new spin is `d = 0` and the factor is
`(0 + 1)² = 1`.

`amplitudeGF K T cut` sums the weight of `K` over colourings with spin `0` on the gauge edges `T`
and spin `≤ cut e` on every other edge `e` (an edge-wise cutoff).

* `amplitudeGF_move23`: the 2-3 move leaves it **unchanged**, provided the new edge's cutoff is at
  least `cut AD + cut AE` (beyond that every term vanishes by the triangle inequality).
* `amplitudeGF_move14`: the 1-4 move, with `DE` added to the gauge edges, leaves it **unchanged**,
  provided `cut AE ≥ cut AD`, `cut BE ≥ cut BD`, `cut CE ≥ cut CD`. No divergent factor appears.
* `amplitudeGF_eqvGen`: hence it is constant along any chain of 2-3, 1-4, 3-2 and 4-1 moves
  (equivalence closure), with cutoffs re-chosen on unused edges in between (`GFStep.recut`).
* `amplitudeGF_empty`: with no gauge edges and a uniform cutoff it is `amplitude K L`.

The theorems above hold for **every** gauge set `T ⊆ K.edges`. The maximal-tree versions restrict
to Freidel–Louapre's gauge set:
* `IsMaxTree K T`: `T` is a spanning tree of the 1-skeleton of `K` (`IsSpanningTree`: edges inside
  the vertex set, connected, `#T + 1 = #vertices`); `IsSpanningTree.isTree` checks this against
  Mathlib's `SimpleGraph.IsTree`.
* `IsMaxTree.move23`, `IsMaxTree.move14`: the moves preserve it (for 1-4, `T ∪ {DE}`: `E` is a new
  leaf).
* `amplitudeGF_move23_tree`, `amplitudeGF_move14_tree`, `amplitudeGF_eqvGen_tree` (chains of
  `GFTreeStep`, whose states all carry a maximal tree: `isMaxTree_iff_of_eqvGen`).

**Proven in other files.** Independence of the maximal tree `T` for trees connected by triangle
exchanges, for every cutoff (`GaugeChange.lean`); the 3-2 and 4-1 moves on an arbitrary complex
(`amplitudeGF_move32`, `amplitudeGF_move41`, `InverseMoves.lean`).

**Open.**
* Pachner's theorem, which is needed for "any two triangulations".
* Independence of the maximal tree in general (Freidel–Louapre, via the Bianchi identity). With
  finite cutoffs it fails on the ring of three tetrahedra in `Lightlike/Tests/TreeDependence.lean`,
  which is not a 3-manifold and so lies outside Freidel–Louapre's assumptions; the closed-manifold
  case is open.
* Convergence as the cutoffs are removed.
-/

@[expose] public section

open Finset Lightlike.Pentagon PhyslibAlpha.Sl2

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Sums over colourings of a set of edges -/

/-- Spins `σ` on the edges in `S`, extended by `0`. -/
def extS (S : Finset (Finset V)) (σ : ∀ e ∈ S, ℕ) : Colouring V :=
  fun e => if h : e ∈ S then σ e h else 0

lemma extS_cons {S : Finset (Finset V)} {a : Finset V} (ha : a ∉ S) (b : ℕ) (σ : ∀ e ∈ S, ℕ) :
    extS (insert a S) (Pi.cons S a b σ) = Function.update (extS S σ) a b := by
  funext e
  by_cases he : e = a
  · subst he
    simp [extS]
  · rw [Function.update_of_ne he]
    by_cases hS : e ∈ S
    · simp only [extS, mem_insert, he, hS, or_true, dite_true]
      exact Pi.cons_ne (Ne.symm he)
    · simp [extS, hS, he]

lemma extS_le {S : Finset (Finset V)} {cut : Finset V → ℕ} {σ : ∀ e ∈ S, ℕ}
    (hσ : σ ∈ S.pi (fun e => range (cut e + 1))) (e : Finset V) : extS S σ e ≤ cut e := by
  unfold extS
  split_ifs with h
  · have := mem_range.mp ((mem_pi.mp hσ) e h); omega
  · exact Nat.zero_le _

lemma extS_of_not_mem {S : Finset (Finset V)} {σ : ∀ e ∈ S, ℕ} {e : Finset V} (h : e ∉ S) :
    extS S σ e = 0 := by
  simp [extS, h]

/-- Summing over colourings of `insert a S` = summing over `S`, then over the spin of `a`. -/
lemma sum_pi_insert {S : Finset (Finset V)} {a : Finset V} (ha : a ∉ S)
    (t : Finset V → Finset ℕ) (F : Colouring V → ℝ) :
    ∑ σ ∈ (insert a S).pi t, F (extS (insert a S) σ) =
      ∑ σ ∈ S.pi t, ∑ x ∈ t a, F (Function.update (extS S σ) a x) := by
  have hdisj : (t a : Set ℕ).PairwiseDisjoint fun b => (S.pi t).image (Pi.cons S a b) := by
    intro x _ y _ hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro f hf hf'
    obtain ⟨σ, _, rfl⟩ := mem_image.mp hf
    obtain ⟨σ', _, h⟩ := mem_image.mp hf'
    have := congrFun (congrFun h a) (mem_insert_self a S)
    simp only [Pi.cons_same] at this
    exact hxy this.symm
  rw [pi_insert ha, sum_biUnion hdisj, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_image (fun σ _ σ' _ h => Pi.cons_injective ha h)]
  exact sum_congr rfl fun σ _ => by rw [extS_cons ha]

/-! ## The gauge-fixed amplitude -/

/-- **The gauge-fixed Ponzano–Regge amplitude** with edge-wise cutoffs: spin `0` on the gauge
edges `T`, spin `≤ cut e` on every other edge `e` of `K`. -/
noncomputable def amplitudeGF (K : Complex3 V) (T : Finset (Finset V)) (cut : Finset V → ℕ) : ℝ :=
  ∑ σ ∈ (K.edges \ T).pi (fun e => range (cut e + 1)), weight K (extS (K.edges \ T) σ)

/-- With no gauge edges and a uniform cutoff, this is the cut-off amplitude `amplitude K L`. -/
theorem amplitudeGF_empty (K : Complex3 V) (L : ℕ) :
    amplitudeGF K ∅ (fun _ => L) = amplitude K L := by
  rw [amplitudeGF, sdiff_empty]
  rfl

/-- `amplitudeGF` only sees the cutoff on the summed edges. -/
lemma amplitudeGF_congr_cut (K : Complex3 V) (T : Finset (Finset V)) {cut cut' : Finset V → ℕ}
    (h : ∀ e ∈ K.edges \ T, cut e = cut' e) : amplitudeGF K T cut = amplitudeGF K T cut' := by
  unfold amplitudeGF
  have : (K.edges \ T).pi (fun e => range (cut e + 1)) =
      (K.edges \ T).pi (fun e => range (cut' e + 1)) := by
    ext σ
    simp only [mem_pi]
    exact forall₂_congr fun e he => by rw [h e he]
  rw [this]

/-- A new edge `{X, E}` with `E` fresh is not an edge of `K`. -/
lemma not_mem_edges_of_fresh (K : Complex3 V) {E : V} (hE : ∀ t ∈ K.tets, E ∉ t) (X : V) :
    ({X, E} : Finset V) ∉ K.edges := fun hm => by
  obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp hm
  exact hE t ht (hst (by simp))

/-- **Exact invariance under the 2-3 move.** -/
theorem amplitudeGF_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    (T : Finset (Finset V)) (hT : T ⊆ K.edges) (cut : Finset V → ℕ)
    (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
    amplitudeGF (move23 K h) T cut = amplitudeGF K T cut := by
  have hDEK : ({D, E} : Finset V) ∉ K.edges := fun hm => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp hm
    exact h.fresh t ht hst
  have hS : (move23 K h).edges \ T = insert {D, E} (K.edges \ T) := by
    rw [edges_move23, insert_sdiff_of_notMem _ (fun hm => hDEK (hT hm))]
  have hDE' : ({D, E} : Finset V) ∉ K.edges \ T := fun hm => hDEK (mem_sdiff.mp hm).1
  rw [amplitudeGF, hS, sum_pi_insert hDE', amplitudeGF]
  refine sum_congr rfl fun σ hσ => ?_
  have hb : extS (K.edges \ T) σ {A, D} + extS (K.edges \ T) σ {A, E} ≤ cut {D, E} :=
    le_trans (Nat.add_le_add (extS_le hσ _) (extS_le hσ _)) hcut
  rw [weight_move23_unconditional K h (extS (K.edges \ T) σ)]
  exact sum_range_eq_of_vanish
    (fun x hx => weight_move23_eq_zero K h _ (by omega))
    (fun x hx => weight_move23_eq_zero K h _ (by omega))

/-- The weight after a 1-4 move vanishes when a new spin violates a triangle inequality. -/
lemma weight_move14_eq_zero (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    (col : Colouring V) (a b c d : ℕ)
    (habc : col {A, D} + d < a ∨ col {B, D} + d < b ∨ col {C, D} + d < c) :
    weight (move14 K h) (upd14 (Function.update col {D, E} d) A B C E a b c) = 0 := by
  have hAB := h.hAB; have hAC := h.hAC; have hAD := h.hAD; have hAE := h.hAE
  have hBC := h.hBC; have hBD := h.hBD; have hBE := h.hBE; have hCD := h.hCD
  have hCE := h.hCE; have hDE := h.hDE
  rw [weight_move14_eq, term14]
  rcases habc with ha | hb | hc
  · rw [tetAmp_eq_zero_of_not_tri _ ![C, D, A, E] (by ev14; unfold Tri; omega)]; ring
  · have h0 : tetAmp (upd14 (Function.update col {D, E} d) A B C E a b c) ![D, B, A, E] = 0 := by
      rw [tetAmp_reindex (p := ![A, D, B, E]) _
        (injective_vec4 hBD.symm hAD.symm hDE hAB.symm hBE hAE)
        (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨3, rfl⟩])]
      exact tetAmp_eq_zero_of_not_tri _ _ (by ev14; unfold Tri; omega)
    rw [h0]; ring
  · rw [tetAmp_eq_zero_of_not_tri _ ![B, C, D, E] (by ev14; unfold Tri; omega)]; ring

/-- The summed edges after a 1-4 move whose new gauge edge is `DE`. -/
lemma edges_move14_sdiff (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    {T : Finset (Finset V)} (hT : T ⊆ K.edges) :
    (move14 K h).edges \ insert {D, E} T =
      insert {A, E} (insert {C, E} (insert {B, E} (K.edges \ T))) := by
  have hK := not_mem_edges_of_fresh K h.fresh
  have nA : ({A, E} : Finset V) ≠ {D, E} := by simp [pair_eq_pair_iff', h.hAD, h.hDE.symm]
  have nB : ({B, E} : Finset V) ≠ {D, E} := by simp [pair_eq_pair_iff', h.hBD, h.hDE.symm]
  have nC : ({C, E} : Finset V) ≠ {D, E} := by simp [pair_eq_pair_iff', h.hCD, h.hDE.symm]
  rw [edges_move14]
  ext s
  simp only [mem_sdiff, mem_union, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨hs | rfl | rfl | rfl | rfl, hne, hnT⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hs, hnT⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl hne
  · rintro (rfl | rfl | rfl | ⟨hs, hnT⟩)
    · exact ⟨Or.inr (Or.inl rfl), nA, fun h' => hK A (hT h')⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), nC, fun h' => hK C (hT h')⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), nB, fun h' => hK B (hT h')⟩
    · exact ⟨Or.inl hs, fun h' => hK D (h' ▸ hs), hnT⟩

/-- **Exact invariance under the 1-4 move**, with the new edge `DE` gauge-fixed (added to `T`).
The divergent vertex factor of `amplitude_move14` becomes `(0 + 1)² = 1`. -/
theorem amplitudeGF_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    (T : Finset (Finset V)) (hT : T ⊆ K.edges) (cut : Finset V → ℕ)
    (hA : cut {A, D} ≤ cut {A, E}) (hB : cut {B, D} ≤ cut {B, E})
    (hC : cut {C, D} ≤ cut {C, E}) :
    amplitudeGF (move14 K h) (insert {D, E} T) cut = amplitudeGF K T cut := by
  have hK := not_mem_edges_of_fresh K h.fresh
  have h1 : ({A, E} : Finset V) ∉ insert {C, E} (insert {B, E} (K.edges \ T)) := by
    simp only [mem_insert, not_or]
    exact ⟨by simp [pair_eq_pair_iff', h.hAC, h.hCE.symm],
      by simp [pair_eq_pair_iff', h.hAB, h.hBE.symm], fun h' => hK A (mem_sdiff.mp h').1⟩
  have h2 : ({C, E} : Finset V) ∉ insert {B, E} (K.edges \ T) := by
    simp only [mem_insert, not_or]
    exact ⟨by simp [pair_eq_pair_iff', h.hBC.symm, h.hBE.symm], fun h' => hK C (mem_sdiff.mp h').1⟩
  have h3 : ({B, E} : Finset V) ∉ K.edges \ T := fun h' => hK B (mem_sdiff.mp h').1
  calc amplitudeGF (move14 K h) (insert {D, E} T) cut
      = ∑ σ ∈ (insert {A, E} (insert {C, E} (insert {B, E} (K.edges \ T)))).pi
            (fun e => range (cut e + 1)),
          weight (move14 K h)
            (extS (insert {A, E} (insert {C, E} (insert {B, E} (K.edges \ T)))) σ) := by
        rw [amplitudeGF, edges_move14_sdiff K h hT]
    _ = ∑ σ ∈ (insert {C, E} (insert {B, E} (K.edges \ T))).pi (fun e => range (cut e + 1)),
          ∑ a ∈ range (cut {A, E} + 1), weight (move14 K h)
            (Function.update (extS (insert {C, E} (insert {B, E} (K.edges \ T))) σ) {A, E} a) :=
        sum_pi_insert h1 _ _
    _ = ∑ σ ∈ (insert {B, E} (K.edges \ T)).pi (fun e => range (cut e + 1)),
          ∑ c ∈ range (cut {C, E} + 1), ∑ a ∈ range (cut {A, E} + 1), weight (move14 K h)
            (Function.update (Function.update (extS (insert {B, E} (K.edges \ T)) σ) {C, E} c)
              {A, E} a) :=
        sum_pi_insert h2 _ (fun col => ∑ a ∈ range (cut {A, E} + 1),
          weight (move14 K h) (Function.update col {A, E} a))
    _ = ∑ σ ∈ (K.edges \ T).pi (fun e => range (cut e + 1)),
          ∑ b ∈ range (cut {B, E} + 1), ∑ c ∈ range (cut {C, E} + 1),
            ∑ a ∈ range (cut {A, E} + 1), weight (move14 K h)
              (Function.update (Function.update (Function.update (extS (K.edges \ T) σ)
                {B, E} b) {C, E} c) {A, E} a) :=
        sum_pi_insert h3 _ (fun col => ∑ c ∈ range (cut {C, E} + 1),
          ∑ a ∈ range (cut {A, E} + 1), weight (move14 K h)
            (Function.update (Function.update col {C, E} c) {A, E} a))
    _ = ∑ σ ∈ (K.edges \ T).pi (fun e => range (cut e + 1)),
          weight K (extS (K.edges \ T) σ) := sum_congr rfl fun σ hσ => ?_
    _ = amplitudeGF K T cut := rfl
  -- one colouring of the old edges: the local 1-4 identity at `d = 0`
  have hDE0 : extS (K.edges \ T) σ {D, E} = 0 :=
    extS_of_not_mem fun h' => hK D (mem_sdiff.mp h').1
  have hupd : ∀ a b c, Function.update (Function.update (Function.update (extS (K.edges \ T) σ)
      {B, E} b) {C, E} c) {A, E} a =
      upd14 (Function.update (extS (K.edges \ T) σ) {D, E} 0) A B C E a b c := by
    intro a b c
    rw [upd14, ← hDE0, Function.update_eq_self]
  simp only [hupd]
  have key := weight_move14 K h (extS (K.edges \ T) σ) 0
  simp only [add_zero, Nat.cast_zero, zero_add, one_pow, one_mul] at key
  rw [← key]
  have hvan : ∀ a b c, (extS (K.edges \ T) σ {A, D} < a ∨ extS (K.edges \ T) σ {B, D} < b ∨
      extS (K.edges \ T) σ {C, D} < c) →
      weight (move14 K h) (upd14 (Function.update (extS (K.edges \ T) σ) {D, E} 0)
        A B C E a b c) = 0 := fun a b c habc =>
    weight_move14_eq_zero K h _ a b c 0 (by simpa using habc)
  have bA := extS_le hσ {A, D}
  have bB := extS_le hσ {B, D}
  have bC := extS_le hσ {C, D}
  rw [sum_congr rfl fun b _ => sum_comm, sum_comm]
  refine sum_range_eq_of_vanish (fun a ha => ?_) (fun a ha => ?_) |>.trans
    (sum_congr rfl fun a _ => ?_)
  · exact sum_eq_zero fun b _ => sum_eq_zero fun c _ => hvan a b c (Or.inl (by omega))
  · exact sum_eq_zero fun b _ => sum_eq_zero fun c _ => hvan a b c (Or.inl (by omega))
  refine sum_range_eq_of_vanish (fun b hb => ?_) (fun b hb => ?_) |>.trans
    (sum_congr rfl fun b _ => ?_)
  · exact sum_eq_zero fun c _ => hvan a b c (Or.inr (Or.inl (by omega)))
  · exact sum_eq_zero fun c _ => hvan a b c (Or.inr (Or.inl (by omega)))
  exact sum_range_eq_of_vanish (fun c hc => hvan a b c (Or.inr (Or.inr (by omega))))
    (fun c hc => hvan a b c (Or.inr (Or.inr (by omega))))

/-- Gauge edges stay edges after a 2-3 move. -/
lemma subset_edges_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    {T : Finset (Finset V)} (hT : T ⊆ K.edges) : T ⊆ (move23 K h).edges := by
  rw [edges_move23]; exact hT.trans (subset_insert _ _)

/-- ... and after a 1-4 move, with the new gauge edge `DE`. -/
lemma insert_subset_edges_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    {T : Finset (Finset V)} (hT : T ⊆ K.edges) : insert {D, E} T ⊆ (move14 K h).edges := by
  rw [edges_move14]
  exact insert_subset (mem_union_right _ (by simp)) (hT.trans subset_union_left)

/-! ## Chains of moves -/

/-- One step between gauge-fixed, cut-off state sums `(complex, gauge edges, cutoffs)`: a 2-3
move, a 1-4 move (its new edge `DE` joins the gauge edges), or a change of the cutoffs on edges
that are not summed (to make room for the next move). -/
inductive GFStep : Complex3 V × Finset (Finset V) × (Finset V → ℕ) →
    Complex3 V × Finset (Finset V) × (Finset V → ℕ) → Prop
  | move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) {T : Finset (Finset V)}
      (hT : T ⊆ K.edges) {cut : Finset V → ℕ} (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
      GFStep (K, T, cut) (move23 K h, T, cut)
  | move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) {T : Finset (Finset V)}
      (hT : T ⊆ K.edges) {cut : Finset V → ℕ} (hA : cut {A, D} ≤ cut {A, E})
      (hB : cut {B, D} ≤ cut {B, E}) (hC : cut {C, D} ≤ cut {C, E}) :
      GFStep (K, T, cut) (move14 K h, insert {D, E} T, cut)
  | recut {K : Complex3 V} {T : Finset (Finset V)} {cut cut' : Finset V → ℕ}
      (h : ∀ e ∈ K.edges \ T, cut e = cut' e) : GFStep (K, T, cut) (K, T, cut')

/-- **The gauge-fixed amplitude is constant along every chain of 2-3, 3-2, 1-4 and 4-1 moves**
(the equivalence closure of `GFStep`). -/
theorem amplitudeGF_eqvGen {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (hxy : Relation.EqvGen GFStep x y) :
    amplitudeGF x.1 x.2.1 x.2.2 = amplitudeGF y.1 y.2.1 y.2.2 := by
  induction hxy with
  | rel x y hs =>
    cases hs with
    | move23 h hT hcut => exact (amplitudeGF_move23 _ h _ hT _ hcut).symm
    | move14 h hT hA hB hC => exact (amplitudeGF_move14 _ h _ hT _ hA hB hC).symm
    | recut h => exact amplitudeGF_congr_cut _ _ h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Maximal trees -/

/-- The vertices of a complex. -/
def Complex3.verts (K : Complex3 V) : Finset V := K.tets.biUnion id

lemma Complex3.mem_verts {K : Complex3 V} {v : V} : v ∈ K.verts ↔ ∃ t ∈ K.tets, v ∈ t := by
  simp [Complex3.verts]

/-- `T` is a **spanning tree** of the graph on the vertex set `W`: its edges are 2-element subsets
of `W`, they connect all of `W`, and there are `#W - 1` of them. A connected graph with one edge
fewer than vertices is a tree (`SimpleGraph.isTree_iff_connected_and_card`); `IsSpanningTree.isTree`
transfers this to Mathlib's `SimpleGraph.IsTree`. -/
structure IsSpanningTree (W : Finset V) (T : Finset (Finset V)) : Prop where
  edge : ∀ e ∈ T, e ⊆ W ∧ #e = 2
  conn : ∀ u ∈ W, ∀ v ∈ W, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) u v
  card : #T + 1 = #W

/-- `T` is a **maximal tree** of `K`: a spanning tree of its 1-skeleton (Freidel–Louapre's gauge
set). -/
def IsMaxTree (K : Complex3 V) (T : Finset (Finset V)) : Prop :=
  T ⊆ K.edges ∧ IsSpanningTree K.verts T

/-- Adding a new vertex `v` joined to `u ∈ W` by one edge keeps a spanning tree spanning. -/
lemma IsSpanningTree.insert_leaf {W : Finset V} {T : Finset (Finset V)} (hT : IsSpanningTree W T)
    {u v : V} (hu : u ∈ W) (hv : v ∉ W) : IsSpanningTree (insert v W) (insert {u, v} T) := by
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  have hnot : ({u, v} : Finset V) ∉ T := fun h => hv ((hT.edge _ h).1 (by simp))
  have hmono : ∀ {x y}, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) x y →
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ insert {u, v} T) x y :=
    fun h => Relation.ReflTransGen.mono (fun a b hab => mem_insert_of_mem hab) _ _ h
  have huv' : ({u, v} : Finset V) ∈ insert {u, v} T := mem_insert_self _ _
  have hvu' : ({v, u} : Finset V) ∈ insert {u, v} T := by rw [pair_comm]; exact mem_insert_self _ _
  refine ⟨fun e he => ?_, fun x hx y hy => ?_, ?_⟩
  · rcases mem_insert.mp he with rfl | he
    · exact ⟨insert_subset (mem_insert_of_mem hu) (by simp), card_pair huv⟩
    · exact ⟨(hT.edge e he).1.trans (subset_insert _ _), (hT.edge e he).2⟩
  · rcases mem_insert.mp hx with rfl | hxW <;> rcases mem_insert.mp hy with rfl | hyW
    · exact .refl
    · exact .head hvu' (hmono (hT.conn u hu y hyW))
    · exact (hmono (hT.conn x hxW u hu)).tail huv'
    · exact hmono (hT.conn x hxW y hyW)
  · rw [card_insert_of_notMem hnot, card_insert_of_notMem hv, hT.card]

/-- The 2-3 move keeps the vertex set. -/
theorem verts_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    (move23 K h).verts = K.verts := by
  have hA : A ∈ K.verts := Complex3.mem_verts.mpr ⟨_, h.mem₁, by simp⟩
  have hB : B ∈ K.verts := Complex3.mem_verts.mpr ⟨_, h.mem₁, by simp⟩
  have hC : C ∈ K.verts := Complex3.mem_verts.mpr ⟨_, h.mem₁, by simp⟩
  have hD : D ∈ K.verts := Complex3.mem_verts.mpr ⟨_, h.mem₁, by simp⟩
  have hE : E ∈ K.verts := Complex3.mem_verts.mpr ⟨_, h.mem₂, by simp⟩
  have hA' : A ∈ (move23 K h).verts := Complex3.mem_verts.mpr ⟨{A, B, D, E}, by simp [move23], by simp⟩
  have hB' : B ∈ (move23 K h).verts := Complex3.mem_verts.mpr ⟨{A, B, D, E}, by simp [move23], by simp⟩
  have hC' : C ∈ (move23 K h).verts := Complex3.mem_verts.mpr ⟨{B, C, D, E}, by simp [move23], by simp⟩
  have hD' : D ∈ (move23 K h).verts := Complex3.mem_verts.mpr ⟨{A, B, D, E}, by simp [move23], by simp⟩
  have hE' : E ∈ (move23 K h).verts := Complex3.mem_verts.mpr ⟨{A, B, D, E}, by simp [move23], by simp⟩
  ext v
  constructor
  · intro hv
    obtain ⟨t, ht, hvt⟩ := Complex3.mem_verts.mp hv
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hvt <;>
        rcases hvt with rfl | rfl | rfl | rfl <;> assumption
    · exact Complex3.mem_verts.mpr ⟨t, mem_of_mem_erase (mem_of_mem_erase ht), hvt⟩
  · intro hv
    obtain ⟨t, ht, hvt⟩ := Complex3.mem_verts.mp hv
    by_cases h1 : t = {A, B, C, D}
    · subst h1; simp only [mem_insert, mem_singleton] at hvt
      rcases hvt with rfl | rfl | rfl | rfl <;> assumption
    by_cases h2 : t = {A, B, C, E}
    · subst h2; simp only [mem_insert, mem_singleton] at hvt
      rcases hvt with rfl | rfl | rfl | rfl <;> assumption
    exact Complex3.mem_verts.mpr ⟨t, mem_union_right _ (mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, ht⟩⟩),
      hvt⟩

/-- The 1-4 move adds exactly the new vertex `E`. -/
theorem verts_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    (move14 K h).verts = insert E K.verts := by
  have hK : ∀ x ∈ ({A, B, C, D} : Finset V), x ∈ K.verts :=
    fun x hx => Complex3.mem_verts.mpr ⟨_, h.mem, hx⟩
  ext v
  simp only [mem_insert]
  constructor
  · intro hv
    obtain ⟨t, ht, hvt⟩ := Complex3.mem_verts.mp hv
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      by_cases hvE : v = E
      · exact Or.inl hvE
      refine Or.inr (hK v ?_)
      rcases ht with rfl | rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hvt ⊢ <;>
        tauto
    · exact Or.inr (Complex3.mem_verts.mpr ⟨t, mem_of_mem_erase ht, hvt⟩)
  · rintro (rfl | hv)
    · exact Complex3.mem_verts.mpr ⟨{A, B, C, v}, by simp [move14], by simp⟩
    obtain ⟨t, ht, hvt⟩ := Complex3.mem_verts.mp hv
    by_cases h1 : t = {A, B, C, D}
    · have hA' : A ∈ (move14 K h).verts :=
        Complex3.mem_verts.mpr ⟨{A, B, C, E}, by simp [move14], by simp⟩
      have hB' : B ∈ (move14 K h).verts :=
        Complex3.mem_verts.mpr ⟨{A, B, C, E}, by simp [move14], by simp⟩
      have hC' : C ∈ (move14 K h).verts :=
        Complex3.mem_verts.mpr ⟨{A, B, C, E}, by simp [move14], by simp⟩
      have hD' : D ∈ (move14 K h).verts :=
        Complex3.mem_verts.mpr ⟨{A, B, D, E}, by simp [move14], by simp⟩
      subst h1; simp only [mem_insert, mem_singleton] at hvt
      rcases hvt with rfl | rfl | rfl | rfl <;> assumption
    exact Complex3.mem_verts.mpr ⟨t, mem_union_right _ (mem_erase.mpr ⟨h1, ht⟩), hvt⟩

/-- A maximal tree of `K` stays one after a 2-3 move (same vertices, more edges). -/
theorem IsMaxTree.move23 {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T)
    {A B C D E : V} (h : IsMove23 K A B C D E) : IsMaxTree (move23 K h) T :=
  ⟨subset_edges_move23 K h hT.1, by rw [verts_move23]; exact hT.2⟩

/-- After a 1-4 move, a maximal tree plus the new edge `DE` is a maximal tree (`E` is a new leaf). -/
theorem IsMaxTree.move14 {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T)
    {A B C D E : V} (h : IsMove14 K A B C D E) : IsMaxTree (move14 K h) (insert {D, E} T) :=
  ⟨insert_subset_edges_move14 K h hT.1, by
    rw [verts_move14]
    refine hT.2.insert_leaf (Complex3.mem_verts.mpr ⟨_, h.mem, by simp⟩) fun hE => ?_
    obtain ⟨t, ht, hEt⟩ := Complex3.mem_verts.mp hE
    exact h.fresh t ht hEt⟩

/-- **2-3 move, maximal-tree version.** If `T` is a maximal tree of `K`, it is one of the new
complex, and the gauge-fixed amplitude is unchanged. -/
theorem amplitudeGF_move23_tree (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    {T : Finset (Finset V)} (hT : IsMaxTree K T) (cut : Finset V → ℕ)
    (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
    IsMaxTree (move23 K h) T ∧ amplitudeGF (move23 K h) T cut = amplitudeGF K T cut :=
  ⟨hT.move23 h, amplitudeGF_move23 K h T hT.1 cut hcut⟩

/-- **1-4 move, maximal-tree version.** If `T` is a maximal tree of `K`, then `T ∪ {DE}` is one of
the new complex, and the gauge-fixed amplitude is unchanged. -/
theorem amplitudeGF_move14_tree (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    {T : Finset (Finset V)} (hT : IsMaxTree K T) (cut : Finset V → ℕ)
    (hA : cut {A, D} ≤ cut {A, E}) (hB : cut {B, D} ≤ cut {B, E})
    (hC : cut {C, D} ≤ cut {C, E}) :
    IsMaxTree (move14 K h) (insert {D, E} T) ∧
      amplitudeGF (move14 K h) (insert {D, E} T) cut = amplitudeGF K T cut :=
  ⟨hT.move14 h, amplitudeGF_move14 K h T hT.1 cut hA hB hC⟩

/-- `GFStep` restricted to maximal trees: every step starts from a state whose gauge set is a
maximal tree (and then also ends in one, `GFTreeStep.isMaxTree`). -/
inductive GFTreeStep : Complex3 V × Finset (Finset V) × (Finset V → ℕ) →
    Complex3 V × Finset (Finset V) × (Finset V → ℕ) → Prop
  | move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) {T : Finset (Finset V)}
      (hT : IsMaxTree K T) {cut : Finset V → ℕ} (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
      GFTreeStep (K, T, cut) (move23 K h, T, cut)
  | move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) {T : Finset (Finset V)}
      (hT : IsMaxTree K T) {cut : Finset V → ℕ} (hA : cut {A, D} ≤ cut {A, E})
      (hB : cut {B, D} ≤ cut {B, E}) (hC : cut {C, D} ≤ cut {C, E}) :
      GFTreeStep (K, T, cut) (move14 K h, insert {D, E} T, cut)
  | recut {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T)
      {cut cut' : Finset V → ℕ} (h : ∀ e ∈ K.edges \ T, cut e = cut' e) :
      GFTreeStep (K, T, cut) (K, T, cut')

lemma GFTreeStep.toGFStep {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (h : GFTreeStep x y) : GFStep x y := by
  cases h with
  | move23 h hT hcut => exact .move23 h hT.1 hcut
  | move14 h hT hA hB hC => exact .move14 h hT.1 hA hB hC
  | recut _ h => exact .recut h

/-- Both ends of a `GFTreeStep` carry a maximal tree. -/
lemma GFTreeStep.isMaxTree {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (h : GFTreeStep x y) : IsMaxTree x.1 x.2.1 ∧ IsMaxTree y.1 y.2.1 := by
  cases h with
  | move23 h hT _ => exact ⟨hT, hT.move23 h⟩
  | move14 h hT _ _ _ => exact ⟨hT, hT.move14 h⟩
  | recut hT _ => exact ⟨hT, hT⟩

/-- Along a chain of tree-restricted moves (and their inverses), "the gauge set is a maximal tree"
is preserved. -/
theorem isMaxTree_iff_of_eqvGen {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (hxy : Relation.EqvGen GFTreeStep x y) : IsMaxTree x.1 x.2.1 ↔ IsMaxTree y.1 y.2.1 := by
  induction hxy with
  | rel _ _ hs => exact iff_of_true hs.isMaxTree.1 hs.isMaxTree.2
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Maximal-tree version of `amplitudeGF_eqvGen`:** the gauge-fixed amplitude is constant along
every chain of 2-3, 3-2, 1-4 and 4-1 moves in which the gauge set is always a maximal tree. -/
theorem amplitudeGF_eqvGen_tree {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (hxy : Relation.EqvGen GFTreeStep x y) :
    amplitudeGF x.1 x.2.1 x.2.2 = amplitudeGF y.1 y.2.1 y.2.2 :=
  amplitudeGF_eqvGen (Relation.EqvGen.mono (fun _ _ h => GFTreeStep.toGFStep h) _ _ hxy)

/-! ## `IsSpanningTree` is a tree in Mathlib's sense -/

/-- The graph on `W` whose edges are the pairs in `T`. -/
def treeGraph (W : Finset V) (T : Finset (Finset V)) : SimpleGraph W :=
  SimpleGraph.fromRel fun a b => ({a.1, b.1} : Finset V) ∈ T

/-- The pair of vertices of `V` underlying an unordered pair in `W`. -/
def pairOf (W : Finset V) : Sym2 W → Finset V :=
  Sym2.lift ⟨fun a b => {a.1, b.1}, fun _ _ => pair_comm _ _⟩

lemma pairOf_mk (W : Finset V) (a b : W) : pairOf W s(a, b) = {a.1, b.1} := rfl

/-- **Sanity check of the definition:** a spanning tree in the sense of `IsSpanningTree` is a tree
in Mathlib's sense (`SimpleGraph.IsTree`: connected and acyclic) on the vertex set `W`. -/
theorem IsSpanningTree.isTree {W : Finset V} {T : Finset (Finset V)} (hT : IsSpanningTree W T) :
    (treeGraph W T).IsTree := by
  have hne : ∀ {x y : V}, ({x, y} : Finset V) ∈ T → x ≠ y := fun h hxy => by
    have := (hT.edge _ h).2; subst hxy; simp at this
  have hreach : ∀ {x y : V}, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) x y →
      ∀ (hx : x ∈ W) (hy : y ∈ W), (treeGraph W T).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y hxy
    induction hxy with
    | refl => intro _ _; rfl
    | @tail b c _ hbc ih =>
      intro hx hc
      have hb : b ∈ W := (hT.edge _ hbc).1 (by simp)
      refine (ih hx hb).trans (SimpleGraph.Adj.reachable ?_)
      rw [treeGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun h => hne hbc (congrArg Subtype.val h), Or.inl hbc⟩
  have hW : 0 < #W := by rw [← hT.card]; omega
  obtain ⟨w, hw⟩ := card_pos.mp hW
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨(SimpleGraph.connected_iff _).mpr
    ⟨fun a b => hreach (hT.conn a.1 a.2 b.1 b.2) a.2 b.2, ⟨⟨w, hw⟩⟩⟩, ?_⟩
  have hmem : ∀ e ∈ (treeGraph W T).edgeSet, pairOf W e ∈ T := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      intro he
      rw [SimpleGraph.mem_edgeSet, treeGraph, SimpleGraph.fromRel_adj] at he
      rcases he.2 with h | h
      · exact h
      · rw [pairOf_mk, pair_comm]; exact h
  have hbij : Function.Bijective
      (fun e : (treeGraph W T).edgeSet => (⟨pairOf W e.1, hmem e.1 e.2⟩ : T)) := by
    constructor
    · rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
      simp only [Subtype.mk.injEq] at heq
      apply Subtype.ext
      induction e₁ using Sym2.ind with | h a b => ?_
      induction e₂ using Sym2.ind with | h c d => ?_
      rw [pairOf_mk, pairOf_mk, pair_eq_pair_iff'] at heq
      rw [Sym2.eq_iff]
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    · rintro ⟨t, ht⟩
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (hT.edge t ht).2
      have hx : x ∈ W := (hT.edge _ ht).1 (by simp)
      have hy : y ∈ W := (hT.edge _ ht).1 (by simp)
      refine ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩, rfl⟩
      rw [SimpleGraph.mem_edgeSet, treeGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun h => hxy (congrArg Subtype.val h), Or.inl ht⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_coe, Fintype.card_coe, hT.card]

end Lightlike.PR
