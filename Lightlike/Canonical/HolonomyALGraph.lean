import Lightlike.Canonical.HolonomyGraph

/-!
# Graphs with the edges of Ashtekar–Lewandowski

The edges of Ashtekar–Lewandowski are closed-piecewise analytic (arXiv:gr-qc/0404018, footnote 17, p. 33): a path
`e : [t₀, t₁] → M` with a subdivision `t₀ = τ₀ < τ₁ < ⋯ < τ_k = t₁` such that the image of each `[τ_{j−1}, τ_j]` is
analytic (`ALEdge`: on each piece the path agrees with a regular analytic arc). A graph (`ALGraph`, footnote 13, p. 27) is
a finite family of such edges, each embedded, two of them meeting only at end points; the end points are the vertices.
Corners of an edge (the `τ_j` with `0 < j < k`) are not vertices.

The `C¹` results of `Lightlike/Canonical/HolonomyGraph.lean` are used for the analytic pieces of the edges: the pieces of
all edges form a `C¹` graph (`ALGraph.pieceGraph`). The holonomy of an edge is the ordered product of the holonomies of its
pieces (`ALEdge.hol`).
-/

open Matrix Set
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

/-- An **edge of Ashtekar–Lewandowski** (footnote 17, p. 33): a path with a subdivision `τ₀ < τ₁ < ⋯ < τ_k` of its
parameter interval such that on each `[τ_{j−1}, τ_j]` the path agrees with a regular analytic arc (analytic, with nonzero
velocity, given as a `C¹` map on `ℝ`). -/
structure ALEdge where
  /-- The path. -/
  path : ℝ → Fin 3 → ℝ
  /-- The number of analytic pieces. -/
  k : ℕ
  /-- There is at least one piece. -/
  k_pos : 0 < k
  /-- The subdivision of the parameter interval. -/
  τ : Fin (k + 1) → ℝ
  /-- The subdivision is strictly increasing. -/
  τ_mono : StrictMono τ
  /-- The analytic arc of each piece. -/
  arc : Fin k → ℝ → Fin 3 → ℝ
  /-- The arcs are `C¹` on `ℝ`. -/
  arc_smooth : ∀ j, ContDiff ℝ 1 (arc j)
  /-- The arcs are analytic, with nonzero velocity, on their pieces. -/
  arc_analytic : ∀ j, ∀ t ∈ Icc (τ j.castSucc) (τ j.succ), AnalyticAt ℝ (arc j) t ∧ deriv (arc j) t ≠ 0
  /-- The path agrees with the arc on each piece. -/
  arc_eq : ∀ j, EqOn path (arc j) (Icc (τ j.castSucc) (τ j.succ))

namespace ALEdge

variable (E : ALEdge)

/-- The initial parameter. -/
def t₀ : ℝ := E.τ 0

/-- The final parameter. -/
def t₁ : ℝ := E.τ (Fin.last E.k)

/-- The `j`-th analytic piece, as an edge. -/
def piece (j : Fin E.k) : Edge :=
  ⟨E.arc j, E.τ j.castSucc, E.τ j.succ, (E.τ_mono (show j.castSucc < j.succ from Fin.castSucc_lt_succ)).le, E.arc_smooth j⟩

/-- The pieces have nonempty interiors. -/
lemma piece_lt (j : Fin E.k) : (E.piece j).t₀ < (E.piece j).t₁ := E.τ_mono (show j.castSucc < j.succ from Fin.castSucc_lt_succ)

/-- The pieces lie in the parameter interval. -/
lemma piece_subset (j : Fin E.k) : Icc (E.piece j).t₀ (E.piece j).t₁ ⊆ Icc E.t₀ E.t₁ :=
  Icc_subset_Icc (E.τ_mono.monotone (Fin.zero_le _)) (E.τ_mono.monotone (Fin.le_last _))

/-- Two different pieces meet only at a common end point of their parameter intervals. -/
lemma piece_inter {j j' : Fin E.k} (hjj : j ≠ j') {s : ℝ} (hs : s ∈ Icc (E.piece j).t₀ (E.piece j).t₁)
    (hs' : s ∈ Icc (E.piece j').t₀ (E.piece j').t₁) :
    (s = (E.piece j).t₀ ∨ s = (E.piece j).t₁) ∧ (s = (E.piece j').t₀ ∨ s = (E.piece j').t₁) := by
  simp only [piece] at hs hs' ⊢
  rcases lt_or_gt_of_ne hjj with h | h
  · have : E.τ j.succ ≤ E.τ j'.castSucc := E.τ_mono.monotone (Fin.succ_le_castSucc_iff.2 h)
    have e1 : s = E.τ j.succ := le_antisymm hs.2 (this.trans hs'.1)
    exact ⟨Or.inr e1, Or.inl (le_antisymm (e1.le.trans this) hs'.1)⟩
  · have : E.τ j'.succ ≤ E.τ j.castSucc := E.τ_mono.monotone (Fin.succ_le_castSucc_iff.2 h)
    have e1 : s = E.τ j'.succ := le_antisymm hs'.2 (this.trans hs.1)
    exact ⟨Or.inl (le_antisymm (e1.le.trans this) hs.1), Or.inr e1⟩

/-- The **holonomy along an edge**: the ordered product `A(e_k) ⋯ A(e_1)` of the holonomies of its pieces. -/
def hol {n : ℕ} (A : MatConn n) : Matrix (Fin n) (Fin n) ℂ :=
  (List.ofFn fun j => (E.piece j).hol A).reverse.prod

end ALEdge

/-- A **graph of Ashtekar–Lewandowski** (footnote 13, p. 27): finitely many edges, each embedded on `[t₀, t₁)` and on
`(t₀, t₁]` (an embedded interval, or an embedded circle with a marked point), two edges meeting only at end points. -/
structure ALGraph where
  /-- The number of edges. -/
  m : ℕ
  /-- The edges. -/
  edge : Fin m → ALEdge
  /-- Each edge is embedded on `[t₀, t₁)`. -/
  injOn_Ico : ∀ i, InjOn (edge i).path (Ico (edge i).t₀ (edge i).t₁)
  /-- Each edge is embedded on `(t₀, t₁]`. -/
  injOn_Ioc : ∀ i, InjOn (edge i).path (Ioc (edge i).t₀ (edge i).t₁)
  /-- Two edges meet only at end points. -/
  meet : ∀ i j, i ≠ j → ∀ s ∈ Icc (edge i).t₀ (edge i).t₁, ∀ t ∈ Icc (edge j).t₀ (edge j).t₁,
    (edge i).path s = (edge j).path t → (s = (edge i).t₀ ∨ s = (edge i).t₁) ∧ (t = (edge j).t₀ ∨ t = (edge j).t₁)

namespace ALEdge

variable (E : ALEdge)

/-- `t₀ < t₁`. -/
lemma t₀_lt_t₁ : E.t₀ < E.t₁ := E.τ_mono (Fin.lt_def.2 (by simpa using E.k_pos))

/-- The piece starting at `t₀` starts exactly there. -/
lemma eq_piece_t₀ (j : Fin E.k) {s : ℝ} (hs : s ∈ Icc (E.piece j).t₀ (E.piece j).t₁) (h : s = E.t₀) :
    s = (E.piece j).t₀ :=
  le_antisymm (h ▸ (E.piece_subset j ⟨le_rfl, (E.piece_lt j).le⟩).1) hs.1

/-- The piece ending at `t₁` ends exactly there. -/
lemma eq_piece_t₁ (j : Fin E.k) {s : ℝ} (hs : s ∈ Icc (E.piece j).t₀ (E.piece j).t₁) (h : s = E.t₁) :
    s = (E.piece j).t₁ :=
  le_antisymm hs.2 (h ▸ (E.piece_subset j ⟨(E.piece_lt j).le, le_rfl⟩).2)

/-- The path of an embedded edge takes equal values only at equal parameters or at the two end points. -/
lemma eq_or_ends {s t : ℝ} (hs : s ∈ Icc E.t₀ E.t₁) (ht : t ∈ Icc E.t₀ E.t₁)
    (hIco : InjOn E.path (Ico E.t₀ E.t₁)) (hIoc : InjOn E.path (Ioc E.t₀ E.t₁)) (h : E.path s = E.path t) :
    s = t ∨ (s = E.t₀ ∧ t = E.t₁) ∨ (s = E.t₁ ∧ t = E.t₀) := by
  have hlt := E.t₀_lt_t₁
  by_cases h1 : s < E.t₁ ∧ t < E.t₁
  · exact Or.inl (hIco ⟨hs.1, h1.1⟩ ⟨ht.1, h1.2⟩ h)
  by_cases h2 : E.t₀ < s ∧ E.t₀ < t
  · exact Or.inl (hIoc ⟨h2.1, hs.2⟩ ⟨h2.2, ht.2⟩ h)
  rw [not_and_or] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso; push Not at h1 h2; linarith [hs.1, hs.2]
  · right; right; push Not at h1 h2; exact ⟨le_antisymm hs.2 h1, le_antisymm h2 ht.1⟩
  · right; left; push Not at h1 h2; exact ⟨le_antisymm h2 hs.1, le_antisymm ht.2 h1⟩
  · exfalso; push Not at h1 h2; linarith [ht.1, ht.2]

end ALEdge

namespace ALGraph

variable (α : ALGraph)

/-- The pieces of all edges, indexed by `(edge, piece)`. -/
abbrev PieceIdx := (i : Fin α.m) × Fin (α.edge i).k

/-- A piece, as an edge. -/
def pieceOf (p : α.PieceIdx) : Edge := (α.edge p.1).piece p.2

/-- **Two different pieces meet only at end points of both.** -/
lemma pieceOf_meet (p q : α.PieceIdx) (hpq : p ≠ q) {s t : ℝ}
    (hs : s ∈ Icc (α.pieceOf p).t₀ (α.pieceOf p).t₁) (ht : t ∈ Icc (α.pieceOf q).t₀ (α.pieceOf q).t₁)
    (h : (α.pieceOf p).path s = (α.pieceOf q).path t) :
    (s = (α.pieceOf p).t₀ ∨ s = (α.pieceOf p).t₁) ∧ (t = (α.pieceOf q).t₀ ∨ t = (α.pieceOf q).t₁) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  simp only [pieceOf] at hs ht h ⊢
  have hs' := (α.edge i).piece_subset j hs
  have ht' := (α.edge i').piece_subset j' ht
  have hpath : (α.edge i).path s = (α.edge i').path t := by
    rw [(α.edge i).arc_eq j hs, (α.edge i').arc_eq j' ht]; exact h
  by_cases hii : i = i'
  · subst hii
    have hjj : j ≠ j' := fun hj => hpq (by rw [hj])
    rcases (α.edge i).eq_or_ends hs' ht' (α.injOn_Ico i) (α.injOn_Ioc i) hpath with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; exact (α.edge i).piece_inter hjj hs ht
    · exact ⟨Or.inl ((α.edge i).eq_piece_t₀ j hs h1), Or.inr ((α.edge i).eq_piece_t₁ j' ht h2)⟩
    · exact ⟨Or.inr ((α.edge i).eq_piece_t₁ j hs h1), Or.inl ((α.edge i).eq_piece_t₀ j' ht h2)⟩
  · obtain ⟨h1, h2⟩ := α.meet i i' hii s hs' t ht' hpath
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      exacts [Or.inl ((α.edge i).eq_piece_t₀ j hs h1), Or.inr ((α.edge i).eq_piece_t₁ j hs h1)]
    · rcases h2 with h2 | h2
      exacts [Or.inl ((α.edge i').eq_piece_t₀ j' ht h2), Or.inr ((α.edge i').eq_piece_t₁ j' ht h2)]

/-- The pieces are embedded on `[t₀, t₁)`. -/
lemma pieceOf_injOn_Ico (p : α.PieceIdx) :
    InjOn (α.pieceOf p).path (Ico (α.pieceOf p).t₀ (α.pieceOf p).t₁) := by
  obtain ⟨i, j⟩ := p
  intro s hs t ht h
  have hsub : Ico ((α.edge i).piece j).t₀ ((α.edge i).piece j).t₁ ⊆ Ico (α.edge i).t₀ (α.edge i).t₁ :=
    fun x hx => ⟨((α.edge i).piece_subset j (Ico_subset_Icc_self hx)).1,
      lt_of_lt_of_le hx.2 ((α.edge i).piece_subset j ⟨(α.edge i).piece_lt j |>.le, le_rfl⟩).2⟩
  refine α.injOn_Ico i (hsub hs) (hsub ht) ?_
  simp only [pieceOf] at h
  rw [(α.edge i).arc_eq j (Ico_subset_Icc_self hs), (α.edge i).arc_eq j (Ico_subset_Icc_self ht)]
  exact h

/-- The pieces are embedded on `(t₀, t₁]`. -/
lemma pieceOf_injOn_Ioc (p : α.PieceIdx) :
    InjOn (α.pieceOf p).path (Ioc (α.pieceOf p).t₀ (α.pieceOf p).t₁) := by
  obtain ⟨i, j⟩ := p
  intro s hs t ht h
  have hsub : Ioc ((α.edge i).piece j).t₀ ((α.edge i).piece j).t₁ ⊆ Ioc (α.edge i).t₀ (α.edge i).t₁ :=
    fun x hx => ⟨lt_of_le_of_lt ((α.edge i).piece_subset j ⟨le_rfl, (α.edge i).piece_lt j |>.le⟩).1 hx.1,
      ((α.edge i).piece_subset j (Ioc_subset_Icc_self hx)).2⟩
  refine α.injOn_Ioc i (hsub hs) (hsub ht) ?_
  simp only [pieceOf] at h
  rw [(α.edge i).arc_eq j (Ioc_subset_Icc_self hs), (α.edge i).arc_eq j (Ioc_subset_Icc_self ht)]
  exact h

/-- The index of a piece in the piece graph. -/
def pidx (p : α.PieceIdx) : Fin (∑ i, (α.edge i).k) := finSigmaFinEquiv p

/-- **The piece graph**: the analytic pieces of all edges form a `C¹` graph. -/
def pieceGraph : Graph where
  m := ∑ i, (α.edge i).k
  edge n := α.pieceOf (finSigmaFinEquiv.symm n)
  nondeg _ := (α.edge _).piece_lt _
  injOn_Ico _ := α.pieceOf_injOn_Ico _
  injOn_Ioc _ := α.pieceOf_injOn_Ioc _
  meet _ _ hnn' _ hs _ ht h :=
    α.pieceOf_meet _ _ (fun he => hnn' (finSigmaFinEquiv.symm.injective he)) hs ht h

/-- The edges of the piece graph are the pieces. -/
lemma pieceGraph_edge (p : α.PieceIdx) : α.pieceGraph.edge (α.pidx p) = α.pieceOf p := by
  simp [pieceGraph, pidx]

end ALGraph



/-- **Telescoping**: for unitary `a`, `∏_j a(j+1)⁻¹ h_j a(j) = a(k)⁻¹ (∏_j h_j) a(0)` (products in decreasing order). -/
lemma telescope_ofFn {n : ℕ} : ∀ {k : ℕ} (h : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ),
    (∀ j, a j * (a j)ᴴ = 1) →
    (List.ofFn fun j : Fin k => (a j.succ)ᴴ * h j * a j.castSucc).reverse.prod =
      (a (Fin.last k))ᴴ * (List.ofFn h).reverse.prod * a 0
  | 0, h, a, hu => by
    simp only [List.ofFn_zero, List.reverse_nil, List.prod_nil, Matrix.mul_one, Fin.last_zero]
    exact (mul_eq_one_comm.1 (hu 0)).symm
  | k + 1, h, a, hu => by
    rw [List.ofFn_succ', List.ofFn_succ']
    simp only [List.concat_eq_append, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.prod_cons]
    have ih := telescope_ofFn (k := k) (fun j => h j.castSucc) (fun j => a j.castSucc) (fun j => hu _)
    simp only [Fin.castSucc_zero] at ih
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last]
    have hc : a (Fin.last k).castSucc * (a (Fin.last k).castSucc)ᴴ = 1 := hu _
    calc (a (Fin.last (k + 1)))ᴴ * h (Fin.last k) * a (Fin.last k).castSucc *
          ((a (Fin.last k).castSucc)ᴴ * (List.ofFn fun j => h j.castSucc).reverse.prod * a 0)
        = (a (Fin.last (k + 1)))ᴴ * h (Fin.last k) * (a (Fin.last k).castSucc * (a (Fin.last k).castSucc)ᴴ) *
          (List.ofFn fun j => h j.castSucc).reverse.prod * a 0 := by noncomm_ring
      _ = _ := by rw [hc, Matrix.mul_one]; noncomm_ring

namespace ALGraph

variable (α : ALGraph)

/-- A **connection on the graph** (`A_α`, p. 28): an `su(2)`-valued 1-form along each edge, given on each analytic piece
of the edge. -/
abbrev Conn := α.pieceGraph.Conn

/-- A **gauge transformation on the graph** (`G_α`, p. 28): an `SU(2)`-valued map on the points of the graph, `C¹` along
each analytic piece. -/
abbrev Gauge := α.pieceGraph.Gauge

/-- The holonomy of a connection on the graph along the piece `p`. -/
def pieceIE (M : α.Conn) (p : α.PieceIdx) : Matrix (Fin 2) (Fin 2) ℂ := α.pieceGraph.IE M (α.pidx p)

/-- **The map `I_E`** (Ashtekar–Lewandowski (4.16)): the holonomy along each edge, the ordered product of the holonomies of
its pieces. -/
def IE (M : α.Conn) (i : Fin α.m) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.ofFn fun j => α.pieceIE M ⟨i, j⟩).reverse.prod

/-- On the restriction of a connection of the chart, `I_E` is the holonomy along the edges. -/
lemma IE_restrict {A : MatConn 2} (hA : ∀ a, Continuous fun x => A x a) (hAH : ∀ x a, (A x a)ᴴ = -A x a)
    (htr : ∀ x a, (A x a).trace = 0) (i : Fin α.m) :
    α.IE (α.pieceGraph.restrict hA hAH htr) i = (α.edge i).hol A := by
  simp only [IE, pieceIE, ALEdge.hol]
  refine congrArg (fun l : List (Matrix (Fin 2) (Fin 2) ℂ) => l.reverse.prod) (congrArg List.ofFn (funext fun j => ?_))
  show (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).hol A = _
  rw [pieceGraph_edge]
  rfl

end ALGraph


namespace ALGraph

variable (α : ALGraph)

/-- The first piece of an edge. -/
def first (i : Fin α.m) : Fin (α.edge i).k := ⟨0, (α.edge i).k_pos⟩

/-- The last piece of an edge. -/
def last (i : Fin α.m) : Fin (α.edge i).k := ⟨(α.edge i).k - 1, Nat.sub_lt (α.edge i).k_pos one_pos⟩

/-- The piece ending at the subdivision point `j > 0`, and the first piece for `j = 0`. -/
def pieceAt (i : Fin α.m) (j : Fin ((α.edge i).k + 1)) : Fin (α.edge i).k :=
  if h : j.val = 0 then α.first i else ⟨j.val - 1, by have := j.2; omega⟩

/-- The value of a gauge transformation at the `j`-th subdivision point `τ_j` of the edge `i`. -/
def ptVal (γ : α.Gauge) (i : Fin α.m) (j : Fin ((α.edge i).k + 1)) : Matrix (Fin 2) (Fin 2) ℂ :=
  γ.val (α.pidx ⟨i, α.pieceAt i j⟩) ((α.edge i).τ j)

/-- The path of the piece graph at a piece. -/
lemma pieceGraph_path (p : α.PieceIdx) : (α.pieceGraph.edge (α.pidx p)).path = (α.pieceOf p).path := by
  rw [pieceGraph_edge]

/-- The values of a gauge transformation at the end points of a piece are its values at the subdivision points. -/
lemma val_start (γ : α.Gauge) (i : Fin α.m) (j : Fin (α.edge i).k) :
    γ.val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.castSucc) = α.ptVal γ i j.castSucc := by
  unfold ptVal pieceAt
  split_ifs with h
  · have hj : j = α.first i := Fin.ext (by simpa [first] using h)
    rw [hj]
  · set j' : Fin (α.edge i).k := ⟨j.castSucc.val - 1, by have := j.castSucc.2; omega⟩ with hj'
    have hsucc : j'.succ = j.castSucc := Fin.ext (by simp only [hj', Fin.val_succ]; omega)
    have hmem1 : (α.edge i).τ j.castSucc ∈ ({(α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₀,
        (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₁} : Set ℝ) := by
      left; rw [pieceGraph_edge]; rfl
    have hmem2 : (α.edge i).τ j.castSucc ∈ ({(α.pieceGraph.edge (α.pidx ⟨i, j'⟩)).t₀,
        (α.pieceGraph.edge (α.pidx ⟨i, j'⟩)).t₁} : Set ℝ) := by
      right; rw [pieceGraph_edge]; show _ = (α.edge i).τ j'.succ; rw [hsucc]
    refine γ.consistent _ _ _ hmem1 _ hmem2 ?_
    rw [pieceGraph_path, pieceGraph_path]
    show (α.edge i).arc j _ = (α.edge i).arc j' _
    have h1 := (α.edge i).arc_eq j ⟨le_rfl, ((α.edge i).piece_lt j).le⟩
    have h2 := (α.edge i).arc_eq j' (show (α.edge i).τ j.castSucc ∈ Icc ((α.edge i).piece j').t₀
      ((α.edge i).piece j').t₁ from ⟨by rw [← hsucc]; exact ((α.edge i).piece_lt j').le, by rw [← hsucc]; rfl⟩)
    exact h1.symm.trans h2

/-- The value at the end of a piece is the value at the next subdivision point. -/
lemma val_end (γ : α.Gauge) (i : Fin α.m) (j : Fin (α.edge i).k) :
    γ.val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.succ) = α.ptVal γ i j.succ := by
  unfold ptVal pieceAt
  split_ifs with h
  · exact absurd h (by simp)
  · congr 3

/-- The subdivision point `τ_j` lies on the piece `pieceAt j`. -/
lemma mem_pieceAt (i : Fin α.m) (j : Fin ((α.edge i).k + 1)) :
    (α.edge i).τ j ∈ Icc ((α.edge i).piece (α.pieceAt i j)).t₀ ((α.edge i).piece (α.pieceAt i j)).t₁ := by
  have hm := (α.edge i).τ_mono.monotone
  unfold pieceAt
  split_ifs with h
  · simp only [ALEdge.piece, first]
    exact ⟨hm (Fin.le_def.2 (by simp)), hm (Fin.le_def.2 (by simp [h]))⟩
  · simp only [ALEdge.piece]
    exact ⟨hm (Fin.le_def.2 (by simp only [Fin.val_castSucc]; omega)),
      hm (Fin.le_def.2 (by simp only [Fin.val_succ]; omega))⟩

/-- The values of a gauge transformation are unitary. -/
lemma ptVal_unitary (γ : α.Gauge) (i : Fin α.m) (j : Fin ((α.edge i).k + 1)) :
    α.ptVal γ i j * (α.ptVal γ i j)ᴴ = 1 := by
  have hmem : (α.edge i).τ j ∈ α.pieceGraph.I (α.pidx ⟨i, α.pieceAt i j⟩) := by
    show _ ∈ Icc (α.pieceGraph.edge (α.pidx ⟨i, α.pieceAt i j⟩)).t₀ (α.pieceGraph.edge (α.pidx ⟨i, α.pieceAt i j⟩)).t₁
    rw [pieceGraph_edge]
    exact α.mem_pieceAt i j
  exact mul_eq_one_comm.1 (Graph.conjTranspose_mul_self_of_mem (γ.mem _ _ hmem))

/-- The holonomy along an edge for raw components `c` along the pieces. -/
def IEc (c : Fin α.pieceGraph.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (i : Fin α.m) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.ofFn fun j => transportM (c (α.pidx ⟨i, j⟩)) ((α.edge i).τ j.castSucc) ((α.edge i).τ j.succ)).reverse.prod

/-- `I_E` is `IEc` of the components. -/
lemma IE_eq_IEc (M : α.Conn) (i : Fin α.m) : α.IE M i = α.IEc M.coeff i := by
  simp only [IE, IEc, pieceIE, Graph.IE]
  refine congrArg (fun l : List (Matrix (Fin 2) (Fin 2) ℂ) => l.reverse.prod) (congrArg List.ofFn (funext fun j => ?_))
  show transportM _ (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₀ (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₁ = _
  rw [pieceGraph_edge]
  rfl

/-- **Equivariance of `I_E`** on the graph (Ashtekar–Lewandowski (4.14)-(4.17)): `I_E(M^γ)_e = γ(t(e))⁻¹ I_E(M)_e γ(s(e))`,
with `γ` at the end points of the edge; the values at the corners cancel. -/
theorem IE_actCoeff (γ : α.Gauge) (M : α.Conn) (i : Fin α.m) :
    α.IEc (α.pieceGraph.actCoeff γ M) i =
      (α.ptVal γ i (Fin.last _))ᴴ * α.IE M i * α.ptVal γ i 0 := by
  have hpiece : ∀ j : Fin (α.edge i).k,
      transportM (α.pieceGraph.actCoeff γ M (α.pidx ⟨i, j⟩)) ((α.edge i).τ j.castSucc) ((α.edge i).τ j.succ) =
        (α.ptVal γ i j.succ)ᴴ * α.pieceIE M ⟨i, j⟩ * α.ptVal γ i j.castSucc := fun j => by
    have h := α.pieceGraph.transportM_actCoeff γ M (α.pidx ⟨i, j⟩)
    rw [pieceGraph_edge] at h
    rw [← val_start, ← val_end]
    exact h
  rw [IEc, IE]
  simp only [hpiece]
  exact telescope_ofFn _ _ (α.ptVal_unitary γ i)

/-- `G⁰_α`: the gauge transformations that are the identity at the vertices, the end points of the edges (p. 27, footnote
13: "The end points of an edge are called vertices"; p. 28: "identity on the vertices of `α`"); they need not be the
identity at the corners. -/
def TrivialAtVertices (γ : α.Gauge) : Prop := ∀ i, α.ptVal γ i 0 = 1 ∧ α.ptVal γ i (Fin.last _) = 1

/-- **`I_E` descends to `A_α / G⁰_α`.** -/
theorem IE_actCoeff_of_trivial (γ : α.Gauge) (hγ : α.TrivialAtVertices γ) (M : α.Conn) (i : Fin α.m) :
    α.IEc (α.pieceGraph.actCoeff γ M) i = α.IE M i := by
  rw [IE_actCoeff, (hγ i).1, (hγ i).2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end ALGraph


namespace ALGraph

variable (α : ALGraph)

/-- Every index of the piece graph is the index of a piece. -/
lemma exists_pidx (n : Fin α.pieceGraph.m) : ∃ p, n = α.pidx p :=
  ⟨finSigmaFinEquiv.symm n, (finSigmaFinEquiv.apply_symm_apply n).symm⟩

/-- An end point of a piece is a subdivision point. -/
lemma endpoint_eq (i : Fin α.m) (j : Fin (α.edge i).k) {s : ℝ}
    (hs : s ∈ ({((α.edge i).piece j).t₀, ((α.edge i).piece j).t₁} : Set ℝ)) :
    s = (α.edge i).τ j.castSucc ∨ s = (α.edge i).τ j.succ := hs

/-- **Consistency from the subdivision points.** Maps along the pieces whose values at the end points of the pieces are
values `b i σ` at the subdivision points, which at the end points of the edges are values `F` of the point, agree at
common end points. -/
lemma consistent_of_ptValues (val : Fin α.pieceGraph.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (b : ∀ i, Fin ((α.edge i).k + 1) → Matrix (Fin 2) (Fin 2) ℂ) (F : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hstart : ∀ i j, val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.castSucc) = b i j.castSucc)
    (hend : ∀ i j, val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.succ) = b i j.succ)
    (h0 : ∀ i, b i 0 = F ((α.edge i).path (α.edge i).t₀))
    (hlast : ∀ i, b i (Fin.last _) = F ((α.edge i).path (α.edge i).t₁)) :
    ∀ n n', ∀ s ∈ ({(α.pieceGraph.edge n).t₀, (α.pieceGraph.edge n).t₁} : Set ℝ),
      ∀ t ∈ ({(α.pieceGraph.edge n').t₀, (α.pieceGraph.edge n').t₁} : Set ℝ),
      (α.pieceGraph.edge n).path s = (α.pieceGraph.edge n').path t → val n s = val n' t := by
  intro n n' s hs t ht hst
  obtain ⟨⟨i, j⟩, rfl⟩ := α.exists_pidx n
  obtain ⟨⟨i', j'⟩, rfl⟩ := α.exists_pidx n'
  rw [pieceGraph_edge] at hs ht
  rw [pieceGraph_edge, pieceGraph_edge] at hst
  -- the end points as subdivision points
  have key : ∀ (i : Fin α.m) (j : Fin (α.edge i).k) (s : ℝ),
      s ∈ ({((α.edge i).piece j).t₀, ((α.edge i).piece j).t₁} : Set ℝ) →
      ∃ σ, s = (α.edge i).τ σ ∧ val (α.pidx ⟨i, j⟩) s = b i σ ∧ s ∈ Icc ((α.edge i).piece j).t₀ ((α.edge i).piece j).t₁ :=
    fun i j s hs => by
      rcases hs with rfl | rfl
      · exact ⟨_, rfl, hstart i j, le_rfl, ((α.edge i).piece_lt j).le⟩
      · exact ⟨_, rfl, hend i j, ((α.edge i).piece_lt j).le, le_rfl⟩
  obtain ⟨σ, rfl, hv, hsI⟩ := key i j s hs
  obtain ⟨σ', rfl, hv', htI⟩ := key i' j' t ht
  rw [hv, hv']
  have hpath : (α.edge i).path ((α.edge i).τ σ) = (α.edge i').path ((α.edge i').τ σ') := by
    rw [(α.edge i).arc_eq j hsI, (α.edge i').arc_eq j' htI]; exact hst
  have hF : ∀ (i : Fin α.m) σ, ((α.edge i).τ σ = (α.edge i).t₀ ∨ (α.edge i).τ σ = (α.edge i).t₁) →
      b i σ = F ((α.edge i).path ((α.edge i).τ σ)) := fun i σ h => by
    rcases h with h | h
    · have : σ = 0 := (α.edge i).τ_mono.injective h
      subst this; rw [h0]; rfl
    · have : σ = Fin.last _ := (α.edge i).τ_mono.injective h
      subst this; rw [hlast]; rfl
  have hs' := (α.edge i).piece_subset j hsI
  have ht' := (α.edge i').piece_subset j' htI
  by_cases hii : i = i'
  · subst hii
    rcases (α.edge i).eq_or_ends hs' ht' (α.injOn_Ico i) (α.injOn_Ioc i) hpath with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [(α.edge i).τ_mono.injective h1]
    · rw [hF i σ (Or.inl h1), hF i σ' (Or.inr h2), hpath]
    · rw [hF i σ (Or.inr h1), hF i σ' (Or.inl h2), hpath]
  · obtain ⟨h1, h2⟩ := α.meet i i' hii _ hs' _ ht' hpath
    rw [hF i σ h1, hF i' σ' h2, hpath]

/-- The holonomy of a connection along the first `σ` pieces of an edge. -/
def partialHol (M : α.Conn) (i : Fin α.m) (σ : Fin ((α.edge i).k + 1)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.ofFn fun j => α.pieceIE M ⟨i, j⟩).take σ.val).reverse.prod

/-- No pieces: the identity. -/
lemma partialHol_zero (M : α.Conn) (i : Fin α.m) : α.partialHol M i 0 = 1 := by simp [partialHol]

/-- All pieces: the holonomy along the edge. -/
lemma partialHol_last (M : α.Conn) (i : Fin α.m) : α.partialHol M i (Fin.last _) = α.IE M i := by
  rw [partialHol, Fin.val_last, List.take_of_length_le (by simp)]
  rfl

/-- One more piece. -/
lemma partialHol_succ (M : α.Conn) (i : Fin α.m) (j : Fin (α.edge i).k) :
    α.partialHol M i j.succ = α.pieceIE M ⟨i, j⟩ * α.partialHol M i j.castSucc := by
  simp only [partialHol, Fin.val_succ, Fin.val_castSucc]
  rw [List.take_add_one, List.getElem?_ofFn]
  simp [List.reverse_append, List.prod_cons, j.2]

/-- The holonomy of a piece is in `SU(2)`. -/
lemma pieceIE_mem (M : α.Conn) (p : α.PieceIdx) : α.pieceIE M p ∈ specialUnitaryGroup (Fin 2) ℂ :=
  α.pieceGraph.IE_mem M _

/-- Partial holonomies are in `SU(2)`. -/
lemma partialHol_mem (M : α.Conn) (i : Fin α.m) (σ : Fin ((α.edge i).k + 1)) :
    α.partialHol M i σ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  rw [List.mem_reverse] at hx
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 (List.mem_of_mem_take hx)
  exact α.pieceIE_mem M _

end ALGraph


namespace ALGraph

variable (α : ALGraph)

/-- The transport of a connection on the graph along a piece, from its start, is in `SU(2)`. -/
lemma transport_mem (M : α.Conn) (n : Fin α.pieceGraph.m) {τ : ℝ} (hτ : τ ∈ α.pieceGraph.I n) :
    transportM (M.coeff n) (α.pieceGraph.edge n).t₀ τ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hsub : Icc (α.pieceGraph.edge n).t₀ τ ⊆ α.pieceGraph.I n := Icc_subset_Icc_right hτ.2
  exact transportM_mem_specialUnitaryGroup ((M.cont n).mono hsub) (fun σ hσ => M.antiHerm n σ (hsub hσ))
    (fun σ hσ => M.traceless n σ (hsub hσ)) hτ.1

/-- The algebra of the gauge transformation `γ = U c U'ᴴ` of `IE_injective_mod`. -/
lemma gauge_alg (U c U' M M' : Matrix (Fin 2) (Fin 2) ℂ) (hM' : M'ᴴ = -M') :
    (U * c * U'ᴴ)ᴴ * M * (U * c * U'ᴴ) + (U * c * U'ᴴ)ᴴ * (-(M * U) * c * U'ᴴ + U * c * (-(M' * U'))ᴴ) =
      U' * (cᴴ * (Uᴴ * U) * c) * U'ᴴ * M' := by
  simp only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose, hM']
  noncomm_ring

/-- **`I_E` is one-to-one on `A_α / G⁰_α`** (Ashtekar–Lewandowski (4.16)): two connections on the graph with the same
holonomy along every edge are related by a gauge transformation that is the identity at the vertices; it is in general
not the identity at the corners. -/
theorem IE_injective_mod (M M' : α.Conn) (h : α.IE M = α.IE M') :
    ∃ γ : α.Gauge, α.TrivialAtVertices γ ∧
      ∀ n, ∀ τ ∈ α.pieceGraph.I n, M'.coeff n τ = α.pieceGraph.actCoeff γ M n τ := by
  set b : ∀ i, Fin ((α.edge i).k + 1) → Matrix (Fin 2) (Fin 2) ℂ :=
    fun i σ => α.partialHol M i σ * (α.partialHol M' i σ)ᴴ with hb
  set c : Fin α.pieceGraph.m → Matrix (Fin 2) (Fin 2) ℂ :=
    fun n => b (finSigmaFinEquiv.symm n).1 (finSigmaFinEquiv.symm n).2.castSucc with hc
  set U := fun n => transportM (M.coeff n) (α.pieceGraph.edge n).t₀ with hU
  set U' := fun n => transportM (M'.coeff n) (α.pieceGraph.edge n).t₀ with hU'
  have hUd := fun n => hasDerivWithinAt_transportM (M.cont n) (α.pieceGraph.nondeg n).le
  have hU'd := fun n => hasDerivWithinAt_transportM (M'.cont n) (α.pieceGraph.nondeg n).le
  have hU'H : ∀ n, ∀ τ ∈ α.pieceGraph.I n,
      HasDerivWithinAt (fun σ => (U' n σ)ᴴ) ((-(M'.coeff n τ * U' n τ))ᴴ) (α.pieceGraph.I n) τ := fun n τ hτ =>
    (conjTransposeCLM (n := 2)).hasFDerivAt.comp_hasDerivWithinAt τ ((hU'd n).2 τ hτ)
  have hcmem : ∀ n, c n ∈ specialUnitaryGroup (Fin 2) ℂ := fun n =>
    Submonoid.mul_mem _ (α.partialHol_mem M _ _) (Graph.conjTranspose_mem (α.partialHol_mem M' _ _))
  have hc_pidx : ∀ i j, c (α.pidx ⟨i, j⟩) = b i j.castSucc := fun i j => by
    have e : finSigmaFinEquiv.symm (α.pidx ⟨i, j⟩) = ⟨i, j⟩ := Equiv.symm_apply_apply _ _
    simp only [hc]
    rw [e]
  have ht₀ : ∀ i j, (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₀ = (α.edge i).τ j.castSucc := fun i j => by
    rw [pieceGraph_edge]; rfl
  have ht₁ : ∀ i j, (α.pieceGraph.edge (α.pidx ⟨i, j⟩)).t₁ = (α.edge i).τ j.succ := fun i j => by
    rw [pieceGraph_edge]; rfl
  let val : Fin α.pieceGraph.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun n τ => U n τ * c n * (U' n τ)ᴴ
  have hstart : ∀ i j, val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.castSucc) = b i j.castSucc := fun i j => by
    have e1 : U (α.pidx ⟨i, j⟩) ((α.edge i).τ j.castSucc) = 1 := by rw [← ht₀]; exact (hUd _).1
    have e2 : U' (α.pidx ⟨i, j⟩) ((α.edge i).τ j.castSucc) = 1 := by rw [← ht₀]; exact (hU'd _).1
    show U _ _ * c _ * (U' _ _)ᴴ = _
    rw [e1, e2, hc_pidx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hend : ∀ i j, val (α.pidx ⟨i, j⟩) ((α.edge i).τ j.succ) = b i j.succ := fun i j => by
    have e1 : U (α.pidx ⟨i, j⟩) ((α.edge i).τ j.succ) = α.pieceIE M ⟨i, j⟩ := by
      rw [← ht₁]; rfl
    have e2 : U' (α.pidx ⟨i, j⟩) ((α.edge i).τ j.succ) = α.pieceIE M' ⟨i, j⟩ := by
      rw [← ht₁]; rfl
    show U _ _ * c _ * (U' _ _)ᴴ = b i j.succ
    rw [e1, e2, hc_pidx]
    simp only [hb, partialHol_succ, conjTranspose_mul]
    noncomm_ring
  have hlastb : ∀ i, b i (Fin.last _) = 1 := fun i => by
    show α.partialHol M i _ * (α.partialHol M' i _)ᴴ = 1
    have hm := α.partialHol_mem M' i (Fin.last _)
    rw [partialHol_last] at hm
    rw [partialHol_last, partialHol_last, h]
    exact mul_eq_one_comm.1 (Graph.conjTranspose_mul_self_of_mem hm)
  let γ : α.Gauge :=
    { val := val
      der := fun n τ => -(M.coeff n τ * U n τ) * c n * (U' n τ)ᴴ + U n τ * c n * (-(M'.coeff n τ * U' n τ))ᴴ
      hasDeriv := fun n τ hτ => (((hUd n).2 τ hτ).mul_const (c n)).fun_mul (hU'H n τ hτ)
      cont := fun n => by
        have hUc : ContinuousOn (U n) (α.pieceGraph.I n) := fun τ hτ => ((hUd n).2 τ hτ).continuousWithinAt
        have hU'c : ContinuousOn (U' n) (α.pieceGraph.I n) := fun τ hτ => ((hU'd n).2 τ hτ).continuousWithinAt
        have hU'Hc : ContinuousOn (fun τ => (U' n τ)ᴴ) (α.pieceGraph.I n) := fun τ hτ =>
          (hU'H n τ hτ).continuousWithinAt
        have hc1 : ContinuousOn (fun τ => (-(M'.coeff n τ * U' n τ))ᴴ) (α.pieceGraph.I n) :=
          (conjTransposeCLM (n := 2)).continuous.comp_continuousOn (((M'.cont n).mul hU'c).neg)
        exact ((((M.cont n).mul hUc).neg.mul continuousOn_const).mul hU'Hc).add
          ((hUc.mul continuousOn_const).mul hc1)
      mem := fun n τ hτ => Submonoid.mul_mem _ (Submonoid.mul_mem _ (α.transport_mem M n hτ) (hcmem n))
        (Graph.conjTranspose_mem (α.transport_mem M' n hτ))
      consistent := α.consistent_of_ptValues val b (fun _ => 1) hstart hend
        (fun i => α.partialHol_zero M i ▸ α.partialHol_zero M' i ▸ by simp [hb, α.partialHol_zero]) hlastb }
  refine ⟨γ, fun i => ⟨?_, ?_⟩, fun n τ hτ => ?_⟩
  · have := α.val_start γ i (α.first i)
    rw [show (α.first i).castSucc = 0 from rfl] at this
    rw [← this]
    refine (hstart i (α.first i)).trans ?_
    show α.partialHol M i 0 * (α.partialHol M' i 0)ᴴ = 1
    rw [partialHol_zero, partialHol_zero, conjTranspose_one, Matrix.mul_one]
  · have hl : (α.last i).succ = Fin.last _ := Fin.ext (by simp [last]; have := (α.edge i).k_pos; omega)
    have := α.val_end γ i (α.last i)
    rw [hl] at this
    rw [← this]
    have := hend i (α.last i)
    rw [hl] at this
    exact this.trans (hlastb i)
  · have hUU : (U n τ)ᴴ * U n τ = 1 := Graph.conjTranspose_mul_self_of_mem (α.transport_mem M _ hτ)
    have hU'U' : U' n τ * (U' n τ)ᴴ = 1 :=
      mul_eq_one_comm.1 (Graph.conjTranspose_mul_self_of_mem (α.transport_mem M' _ hτ))
    have hcc : (c n)ᴴ * c n = 1 := Graph.conjTranspose_mul_self_of_mem (hcmem _)
    have e := gauge_alg (U n τ) (c n) (U' n τ) (M.coeff n τ) (M'.coeff n τ) (M'.antiHerm n τ hτ)
    show _ = (U n τ * c n * (U' n τ)ᴴ)ᴴ * M.coeff n τ * (U n τ * c n * (U' n τ)ᴴ) +
      (U n τ * c n * (U' n τ)ᴴ)ᴴ * (-(M.coeff n τ * U n τ) * c n * (U' n τ)ᴴ +
        U n τ * c n * (-(M'.coeff n τ * U' n τ))ᴴ)
    rw [e, hUU, Matrix.mul_one, hcc, Matrix.mul_one, hU'U', Matrix.one_mul]

end ALGraph


/-- A product with one factor `x` in front and ones after it. -/
lemma ofFn_first_prod {n : ℕ} {k : ℕ} (hk : 0 < k) (x : Matrix (Fin n) (Fin n) ℂ) :
    (List.ofFn fun j : Fin k => if j.val = 0 then x else 1).reverse.prod = x := by
  cases k with
  | zero => omega
  | succ k =>
    rw [List.ofFn_succ]
    simp [List.reverse_cons, List.prod_append, Fin.val_succ]

namespace ALGraph

variable (α : ALGraph)

/-- **`I_E` is onto `SU(2)ⁿ`**: every family of elements of `SU(2)` is the family of holonomies along the edges of a
connection on the graph. -/
theorem IE_surjective (h : Fin α.m → Matrix (Fin 2) (Fin 2) ℂ) (hh : ∀ i, h i ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ M : α.Conn, α.IE M = h := by
  set g : Fin α.pieceGraph.m → Matrix (Fin 2) (Fin 2) ℂ := fun n =>
    if (finSigmaFinEquiv.symm n).2.val = 0 then h (finSigmaFinEquiv.symm n).1 else 1 with hg
  obtain ⟨M, hM⟩ := α.pieceGraph.IE_surjective g fun n => by
    simp only [hg]; split_ifs
    exacts [hh _, Submonoid.one_mem _]
  refine ⟨M, funext fun i => ?_⟩
  have hpiece : ∀ j, α.pieceIE M ⟨i, j⟩ = if j.val = 0 then h i else 1 := fun j => by
    have e : finSigmaFinEquiv.symm (α.pidx ⟨i, j⟩) = ⟨i, j⟩ := Equiv.symm_apply_apply _ _
    rw [pieceIE, hM]
    simp only [hg]
    rw [e]
  simp only [IE, hpiece]
  exact ofFn_first_prod (α.edge i).k_pos _

/-- The **vertices** of the graph: the end points of its edges (footnote 13, p. 27). -/
def vertices : Set (Fin 3 → ℝ) := {v | ∃ i, v = (α.edge i).path (α.edge i).t₀ ∨ v = (α.edge i).path (α.edge i).t₁}

/-- The vertices of the graph are vertices of the piece graph. -/
lemma vertices_subset {v : Fin 3 → ℝ} (hv : v ∈ α.vertices) : v ∈ α.pieceGraph.vertices := by
  obtain ⟨i, hv | hv⟩ := hv
  · refine ⟨α.pidx ⟨i, α.first i⟩, Or.inl ?_⟩
    rw [Edge.source, pieceGraph_edge, hv]
    show (α.edge i).path ((α.edge i).τ (α.first i).castSucc) =
      (α.edge i).arc (α.first i) ((α.edge i).τ (α.first i).castSucc)
    exact (α.edge i).arc_eq (α.first i) ⟨le_rfl, ((α.edge i).piece_lt (α.first i)).le⟩
  · refine ⟨α.pidx ⟨i, α.last i⟩, Or.inr ?_⟩
    have hl : (α.last i).succ = Fin.last _ := Fin.ext (by simp [last]; have := (α.edge i).k_pos; omega)
    rw [Edge.target, pieceGraph_edge, hv]
    have := (α.edge i).arc_eq (α.last i) ⟨((α.edge i).piece_lt (α.last i)).le, le_rfl⟩
    show (α.edge i).path ((α.edge i).τ (Fin.last _)) = (α.edge i).arc (α.last i) ((α.edge i).τ (α.last i).succ)
    rw [hl]
    simpa [ALEdge.piece, hl] using this

/-- **The map `I_V`** (Ashtekar–Lewandowski (4.17)): the values of a gauge transformation at the vertices. -/
def IV (γ : α.Gauge) (v : α.vertices) : Matrix (Fin 2) (Fin 2) ℂ := α.pieceGraph.IV γ ⟨v.1, α.vertices_subset v.2⟩

/-- `I_V` at the initial point of an edge. -/
lemma IV_start (γ : α.Gauge) (i : Fin α.m) (hv : (α.edge i).path (α.edge i).t₀ ∈ α.vertices) :
    α.IV γ ⟨_, hv⟩ = α.ptVal γ i 0 := by
  have h := α.pieceGraph.IV_eq γ (v := ⟨_, α.vertices_subset hv⟩) (j := α.pidx ⟨i, α.first i⟩)
    (t := (α.edge i).τ 0) (by left; rw [pieceGraph_edge]; rfl)
    (by rw [pieceGraph_edge]; exact ((α.edge i).arc_eq _ ⟨le_rfl, ((α.edge i).piece_lt _).le⟩).symm)
  rw [IV, h]
  rfl

/-- `I_V` at the final point of an edge. -/
lemma IV_end (γ : α.Gauge) (i : Fin α.m) (hv : (α.edge i).path (α.edge i).t₁ ∈ α.vertices) :
    α.IV γ ⟨_, hv⟩ = α.ptVal γ i (Fin.last _) := by
  have hl : (α.last i).succ = Fin.last _ := Fin.ext (by simp [last]; have := (α.edge i).k_pos; omega)
  have h := α.pieceGraph.IV_eq γ (v := ⟨_, α.vertices_subset hv⟩) (j := α.pidx ⟨i, α.last i⟩)
    (t := (α.edge i).τ (Fin.last _)) (by right; rw [pieceGraph_edge]; show _ = (α.edge i).τ (α.last i).succ; rw [hl])
    (by
      rw [pieceGraph_edge]
      have := (α.edge i).arc_eq (α.last i) ⟨((α.edge i).piece_lt _).le, le_rfl⟩
      simp only [ALEdge.piece, hl] at this
      exact this.symm)
  rw [IV, h]
  have := α.val_end γ i (α.last i)
  rw [hl] at this
  exact this

/-- **`I_V` is one-to-one on `G_α / G⁰_α`** (Ashtekar–Lewandowski (4.17)): two gauge transformations have the same
values at the vertices if and only if `γ'⁻¹ γ` is the identity at the vertices. -/
theorem IV_eq_iff (γ γ' : α.Gauge) : α.IV γ = α.IV γ' ↔ α.TrivialAtVertices (γ'.quot γ) := by
  have hq : ∀ i σ, α.ptVal (γ'.quot γ) i σ = (α.ptVal γ' i σ)ᴴ * α.ptVal γ i σ := fun _ _ => rfl
  have hu : ∀ (g : α.Gauge) i σ, (α.ptVal g i σ)ᴴ * α.ptVal g i σ = 1 := fun g i σ =>
    mul_eq_one_comm.1 (α.ptVal_unitary g i σ)
  have hcancel : ∀ i σ, (α.ptVal γ' i σ)ᴴ * α.ptVal γ i σ = 1 → α.ptVal γ i σ = α.ptVal γ' i σ := fun i σ h1 =>
    calc α.ptVal γ i σ = α.ptVal γ' i σ * (α.ptVal γ' i σ)ᴴ * α.ptVal γ i σ := by
          rw [α.ptVal_unitary γ' i σ, Matrix.one_mul]
      _ = α.ptVal γ' i σ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  constructor
  · intro h i
    have hv0 : (α.edge i).path (α.edge i).t₀ ∈ α.vertices := ⟨i, Or.inl rfl⟩
    have hv1 : (α.edge i).path (α.edge i).t₁ ∈ α.vertices := ⟨i, Or.inr rfl⟩
    have e0 : α.ptVal γ i 0 = α.ptVal γ' i 0 :=
      (α.IV_start γ i hv0).symm.trans ((congrFun h ⟨_, hv0⟩).trans (α.IV_start γ' i hv0))
    have e1 : α.ptVal γ i (Fin.last _) = α.ptVal γ' i (Fin.last _) :=
      (α.IV_end γ i hv1).symm.trans ((congrFun h ⟨_, hv1⟩).trans (α.IV_end γ' i hv1))
    rw [hq, hq, e0, e1]
    exact ⟨hu γ' i 0, hu γ' i _⟩
  · intro h
    funext v
    obtain ⟨v, i, hv | hv⟩ := v
    · subst hv
      exact (α.IV_start γ i _).trans ((hcancel i 0 ((hq i 0).symm.trans (h i).1)).trans (α.IV_start γ' i _).symm)
    · subst hv
      exact (α.IV_end γ i _).trans ((hcancel i _ ((hq i _).symm.trans (h i).2)).trans (α.IV_end γ' i _).symm)

/-- **`I_V` is onto `SU(2)^m`**: every assignment of elements of `SU(2)` to the vertices is the family of values of a
gauge transformation on the graph. -/
theorem IV_surjective (f : α.vertices → Matrix (Fin 2) (Fin 2) ℂ) (hf : ∀ v, f v ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ γ : α.Gauge, α.IV γ = f := by
  classical
  set F : α.pieceGraph.vertices → Matrix (Fin 2) (Fin 2) ℂ := fun w =>
    if h : w.1 ∈ α.vertices then f ⟨w.1, h⟩ else 1 with hF
  obtain ⟨γ, hγ⟩ := α.pieceGraph.IV_surjective F fun w => by
    simp only [hF]; split_ifs
    exacts [hf _, Submonoid.one_mem _]
  refine ⟨γ, funext fun v => ?_⟩
  rw [IV, hγ]
  simp only [hF, v.2, dite_true]

end ALGraph

/-- The `L`-shaped path: `t e₀` for `t ≤ 1`, then `e₀ + (t − 1) e₁`. -/
def lPath (t : ℝ) : Fin 3 → ℝ :=
  if t ≤ 1 then t • (Pi.single 0 1 : Fin 3 → ℝ) else Pi.single 0 1 + (t - 1) • (Pi.single 1 1 : Fin 3 → ℝ)

/-- The two arcs of the `L`-shaped path. -/
def lArc : Fin 2 → ℝ → Fin 3 → ℝ
  | 0 => fun t => t • (Pi.single 0 1 : Fin 3 → ℝ)
  | 1 => fun t => Pi.single 0 1 + (t - 1) • (Pi.single 1 1 : Fin 3 → ℝ)

/-- The arcs of the `L`-shaped path are affine, so analytic with constant velocity. -/
lemma lArc_hasDerivAt (j : Fin 2) (t : ℝ) :
    HasDerivAt (lArc j) (if j = 0 then (Pi.single 0 1 : Fin 3 → ℝ) else Pi.single 1 1) t := by
  fin_cases j
  · simpa [lArc] using (hasDerivAt_id t).smul_const (Pi.single 0 1 : Fin 3 → ℝ)
  · simpa [lArc] using (((hasDerivAt_id t).sub_const 1).smul_const (Pi.single 1 1 : Fin 3 → ℝ)).const_add
      (Pi.single 0 1 : Fin 3 → ℝ)

/-- The `L`-shaped edge: an edge of Ashtekar–Lewandowski with two analytic pieces and a corner at `e₀`. -/
def lEdge : ALEdge where
  path := lPath
  k := 2
  k_pos := two_pos
  τ := ![0, 1, 2]
  τ_mono := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def]
  arc := lArc
  arc_smooth j := by
    fin_cases j
    · exact contDiff_id.smul contDiff_const
    · exact contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)
  arc_analytic j t _ := by
    refine ⟨?_, ?_⟩
    · fin_cases j
      · exact (analyticAt_id.smul analyticAt_const)
      · exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const)
    · rw [(lArc_hasDerivAt j t).deriv]
      fin_cases j <;> simp [funext_iff, Pi.single_apply]
  arc_eq j t ht := by
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one] at ht
      have : t ≤ 1 := by simpa using ht.2
      simp [lPath, lArc, this]
    · simp only [Fin.mk_one, Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two] at ht
      have h1 : (1 : ℝ) ≤ t := by simpa using ht.1
      rcases eq_or_lt_of_le h1 with h | h
      · subst h; simp [lPath, lArc]
      · simp [lPath, lArc, not_le.2 h]


/-- The `L`-shaped path is injective. -/
lemma lPath_injective : Function.Injective lPath := by
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  unfold lPath at h0 h1
  split_ifs at h0 h1 with hs ht ht <;> simp at h0 h1 <;> linarith

/-- **Trust check: an edge with a corner.** The one-edge graph on the `L`-shaped edge satisfies the hypotheses of a
graph of Ashtekar–Lewandowski, and every element of `SU(2)` is the holonomy of a connection along it. -/
def lGraph : ALGraph where
  m := 1
  edge _ := lEdge
  injOn_Ico _ := lPath_injective.injOn
  injOn_Ioc _ := lPath_injective.injOn
  meet i j hij := absurd (Subsingleton.elim i j) hij

/-- On the `L`-shaped edge every element of `SU(2)` is a holonomy. -/
theorem lGraph_IE_surjective {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ M : lGraph.Conn, lGraph.IE M ⟨0, one_pos⟩ = h := by
  obtain ⟨M, hM⟩ := lGraph.IE_surjective (fun _ => h) fun _ => hh
  exact ⟨M, congrFun hM _⟩

end Lightlike.Canonical
