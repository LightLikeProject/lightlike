import Lightlike.Regge.Schlaefli
import Lightlike.Regge.Complex

/-!
# Regge's equations: the variation of the Regge action

For a triangulation with non-degenerate tetrahedra, the derivative of the Regge action
`S = Σ_{interior} ℓ_e δ_e + Σ_{boundary} ℓ_e ψ_e` in the edge lengths is

  `dS = Σ_{interior} δ_e dℓ_e + Σ_{boundary} ψ_e dℓ_e`,

the variation of the angles cancelling by Schläfli's identity (Regge 1961). So the stationary
points of the action with the boundary lengths held fixed are the length assignments with zero
deficit at every interior edge: Regge's discrete vacuum Einstein equations.

## Main results

* `sum_curvature_eq`: for any weights `w`, `Σ_{int} w_e δ_e + Σ_{bdry} w_e ψ_e` equals
  `2π Σ_{int} w_e + π Σ_{bdry} w_e - Σ_{tetrahedra t} Σ_{e ⊂ t} w_e θ_t(e)`; with `w = ℓ` this
  rewrites the Regge action tetrahedron by tetrahedron (`reggeAction_eq_sum_tets`).
* `tetSum_eq`: the sum over the six edges of one tetrahedron is the Ponzano–Regge expression of
  `Lightlike/Regge/Schlaefli.lean` in a labelling of its vertices.
* `hasDerivAt_reggeAction` (**Regge's equations**): along every direction `v` of change of the edge
  lengths, the derivative of the Regge action is `Σ_{int} v_e δ_e + Σ_{bdry} v_e ψ_e`.
* `reggeAction_stationary_iff`: with the boundary lengths held fixed, the action is stationary
  exactly when every interior deficit angle vanishes.
-/

open Real Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3 dihedral)

variable {V : Type*} [DecidableEq V]

/-! ## Sums over the edges of a tetrahedron -/

/-- A sum over the 2-element subsets of `insert x s` splits into the pairs inside `s` and the pairs
`{x, y}`, `y ∈ s`. -/
theorem sum_powersetCard_two_insert {x : V} {s : Finset V} (h : x ∉ s) (f : Finset V → ℝ) :
    ∑ e ∈ (insert x s).powersetCard 2, f e = ∑ e ∈ s.powersetCard 2, f e + ∑ y ∈ s, f {x, y} := by
  rw [powersetCard_succ_insert h 1, sum_union, powersetCard_one, sum_image, sum_map]
  · rfl
  · intro a ha b hb hab
    simp only [coe_map, Set.mem_image, mem_coe, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have : a' ∈ insert x ({b'} : Finset V) := by rw [← hab]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact absurd (h' ▸ ha') h
    · rw [h']
  · rw [disjoint_left]
    intro e he he'
    rw [mem_image] at he'
    obtain ⟨z, -, rfl⟩ := he'
    exact h ((mem_powersetCard.mp he).1 (mem_insert_self x z))

/-- A sum over the `(n+1)`-element subsets of `insert x s` splits into those inside `s` and
those containing `x`. -/
theorem sum_powersetCard_succ_insert {x : V} {s : Finset V} (h : x ∉ s) (n : ℕ)
    (f : Finset V → ℝ) :
    ∑ e ∈ (insert x s).powersetCard (n + 1), f e =
      ∑ e ∈ s.powersetCard (n + 1), f e + ∑ e ∈ s.powersetCard n, f (insert x e) := by
  rw [powersetCard_succ_insert h n, sum_union, sum_image]
  · intro a ha b hb hab
    have hxa : x ∉ a := fun hx => h ((mem_powersetCard.mp ha).1 hx)
    have hxb : x ∉ b := fun hx => h ((mem_powersetCard.mp hb).1 hx)
    rw [← erase_insert hxa, ← erase_insert hxb]
    exact congrArg (·.erase x) hab
  · rw [disjoint_left]
    intro e he he'
    rw [mem_image] at he'
    obtain ⟨z, -, rfl⟩ := he'
    exact h ((mem_powersetCard.mp he).1 (mem_insert_self x z))

/-- The sum over the three edges of the triangle `{p, q, r}`. -/
theorem sum_powersetCard_two_three {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (f : Finset V → ℝ) :
    ∑ e ∈ ({p, q, r} : Finset V).powersetCard 2, f e = f {p, q} + f {q, r} + f {r, p} := by
  have h2 : ({q, r} : Finset V).powersetCard 2 = {{q, r}} := by
    rw [← card_pair hqr, powersetCard_self]
  rw [sum_powersetCard_two_insert (by simp [hpq, hpr]), h2, sum_singleton, sum_pair hqr,
    pair_comm p r]
  ring

/-- The sum over the four faces of the tetrahedron `{p, q, r, s}`. -/
theorem sum_powersetCard_three_four {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (f : Finset V → ℝ) :
    ∑ e ∈ ({p, q, r, s} : Finset V).powersetCard 3, f e =
      f {p, q, r} + f {p, q, s} + f {p, r, s} + f {q, r, s} := by
  have h3 : ({q, r, s} : Finset V).powersetCard 3 = {{q, r, s}} := by
    rw [show (3 : ℕ) = #({q, r, s} : Finset V) by
      rw [card_insert_of_notMem (by simp [hqr, hqs]), card_pair hrs], powersetCard_self]
  rw [sum_powersetCard_succ_insert (by simp [hpq, hpr, hps]) 2, h3, sum_singleton,
    sum_powersetCard_two_three hqr hqs hrs, pair_comm s q]
  ring

/-- The sum over the six edges of the tetrahedron `{p, q, r, s}`. -/
theorem sum_powersetCard_two_four {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (f : Finset V → ℝ) :
    ∑ e ∈ ({p, q, r, s} : Finset V).powersetCard 2, f e =
      f {p, q} + f {q, r} + f {r, p} + f {r, s} + f {p, s} + f {q, s} := by
  have h2 : ({r, s} : Finset V).powersetCard 2 = {{r, s}} := by
    rw [← card_pair hrs, powersetCard_self]
  rw [sum_powersetCard_two_insert (by simp [hpq, hpr, hps]),
    sum_powersetCard_two_insert (by simp [hqr, hqs]), h2, sum_singleton, sum_pair hrs,
    sum_insert (by simp [hqr, hqs]), sum_pair hrs, pair_comm p r]
  ring

/-- The lengths of the tetrahedron `{p, q, r, s}` in the labelling `A, B, C, D = p, q, r, s` of
`Lightlike.PR.extAngles`: `(AB, BC, CA, CD, AD, BD)`. -/
def labLen (m : Finset V → ℝ) (p q r s : V) : Fin 6 → ℝ :=
  ![m {p, q}, m {q, r}, m {r, p}, m {r, s}, m {p, s}, m {q, s}]

/-- **One tetrahedron, labelled.** For lengths `m` nonzero on the edges of the tetrahedron
`t = {p, q, r, s}` and any weights `w`, `Σ_{e ⊂ t} w_e θ_t(e)` is
`Σ_i w_i (π - Lightlike.PR.extAngles m i)` in the labelling `A, B, C, D = p, q, r, s`. -/
theorem tetSum_eq (m w : Finset V → ℝ) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (hm : ∀ i, labLen m p q r s i ≠ 0) :
    ∑ e ∈ ({p, q, r, s} : Finset V).powersetCard 2, w e * dihedralAt m {p, q, r, s} e =
      ∑ i, labLen w p q r s i * (π - Lightlike.PR.extAngles (labLen m p q r s) i) := by
  have m0 : m {p, q} ≠ 0 := hm 0
  have m1 : m {q, r} ≠ 0 := hm 1
  have m2 : m {r, p} ≠ 0 := hm 2
  have m3 : m {r, s} ≠ 0 := hm 3
  have m4 : m {p, s} ≠ 0 := hm 4
  have m5 : m {q, s} ≠ 0 := hm 5
  rw [sum_powersetCard_two_four hpq hpr hps hqr hqs hrs]
  rw [dihedralAt_eq m hpq hpr hps hqr hqs hrs m0,
    show ({p, q, r, s} : Finset V) = {q, r, p, s} by ext; simp; tauto,
    dihedralAt_eq m hqr hpq.symm hqs hpr.symm hrs hps m1,
    show ({q, r, p, s} : Finset V) = {r, p, q, s} by ext; simp; tauto,
    dihedralAt_eq m hpr.symm hqr.symm hrs hpq hps hqs m2,
    show ({r, p, q, s} : Finset V) = {r, s, p, q} by ext; simp; tauto,
    dihedralAt_eq m hrs hpr.symm hqr.symm hps.symm hqs.symm hpq m3,
    show ({r, s, p, q} : Finset V) = {p, s, q, r} by ext; simp; tauto,
    dihedralAt_eq m hps hpq hpr hqs.symm hrs.symm hqr m4,
    show ({p, s, q, r} : Finset V) = {q, s, p, r} by ext; simp; tauto,
    dihedralAt_eq m hqs hpq.symm hqr hps.symm hrs.symm hpr m5]
  rw [pair_comm p r, pair_comm q p, pair_comm r q, pair_comm s p, pair_comm s q, pair_comm s r]
  simp [Fin.sum_univ_six, Lightlike.PR.extAngles, labLen]

/-! ## The Regge action, tetrahedron by tetrahedron -/

/-- Exchanging the sum over edges with the sum over tetrahedra: the pairs (edge, tetrahedron
containing it) are the pairs (tetrahedron, one of its six edges). -/
theorem sum_edges_star (K : Complex3 V) (F : Finset V → Finset V → ℝ) :
    ∑ e ∈ K.edges, ∑ t ∈ star K e, F e t = ∑ t ∈ K.tets, ∑ e ∈ t.powersetCard 2, F e t := by
  apply sum_comm'
  intro e t
  simp only [star, mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨he, ht, hs⟩
    obtain ⟨_, _, _, h2⟩ := Complex3.mem_edges.mp he
    exact ⟨⟨hs, h2⟩, ht⟩
  · rintro ⟨⟨hs, h2⟩, ht⟩
    exact ⟨Complex3.mem_edges.mpr ⟨t, ht, hs, h2⟩, ht, hs⟩

/-- **The curvature sum, tetrahedron by tetrahedron.** For any weights `w`,
`Σ_{int} w_e δ_e + Σ_{bdry} w_e ψ_e = 2π Σ_{int} w_e + π Σ_{bdry} w_e - Σ_t Σ_{e ⊂ t} w_e θ_t(e)`. -/
theorem sum_curvature_eq (K : Complex3 V) (ℓ w : Finset V → ℝ) :
    ∑ e ∈ intEdges K, w e * deficit K ℓ e + ∑ e ∈ bdryEdges K, w e * bdryAngle K ℓ e =
      ∑ e ∈ intEdges K, 2 * π * w e + ∑ e ∈ bdryEdges K, π * w e -
        ∑ t ∈ K.tets, ∑ e ∈ t.powersetCard 2, w e * dihedralAt ℓ t e := by
  have hsplit : ∑ e ∈ intEdges K, w e * angleSum K ℓ e + ∑ e ∈ bdryEdges K, w e * angleSum K ℓ e =
      ∑ e ∈ K.edges, w e * angleSum K ℓ e := by
    rw [← sum_union (disjoint_intEdges_bdryEdges K), intEdges_union_bdryEdges]
  have hswap : ∑ e ∈ K.edges, w e * angleSum K ℓ e =
      ∑ t ∈ K.tets, ∑ e ∈ t.powersetCard 2, w e * dihedralAt ℓ t e := by
    simp only [angleSum, mul_sum]
    exact sum_edges_star K fun e t => w e * dihedralAt ℓ t e
  simp only [deficit, bdryAngle, mul_sub, sum_sub_distrib]
  rw [← hswap, ← hsplit]
  simp only [mul_comm (w _) (2 * π), mul_comm (w _) π]
  ring

/-- The Regge action rewritten tetrahedron by tetrahedron. -/
theorem reggeAction_eq_sum_tets (K : Complex3 V) (ℓ : Finset V → ℝ) :
    reggeAction K ℓ = ∑ e ∈ intEdges K, 2 * π * ℓ e + ∑ e ∈ bdryEdges K, π * ℓ e -
      ∑ t ∈ K.tets, ∑ e ∈ t.powersetCard 2, ℓ e * dihedralAt ℓ t e :=
  sum_curvature_eq K ℓ ℓ

/-! ## Regge's equations -/

/-- Sixteen times the squared area of the triangle `f` from the edge lengths `ℓ`, without
choosing a labelling: `(Σ x_e)² - 2 Σ x_e²` over the three edges, `x_e = ℓ_e²` (Heron's formula;
`triH_eq`). -/
def triH (ℓ : Finset V → ℝ) (f : Finset V) : ℝ :=
  (∑ e ∈ f.powersetCard 2, ℓ e ^ 2) ^ 2 - 2 * ∑ e ∈ f.powersetCard 2, ℓ e ^ 4

/-- The squared volume of the tetrahedron `t` from the edge lengths `ℓ`, without choosing a
labelling (the Cayley–Menger determinant in the Euler–Tartaglia form; `tetV2_eq`): with
`x_e = ℓ_e²` and `S = Σ_e x_e`,
`144 V² = ½ Σ_e x_e x_{t∖e} (S - 2x_e - 2x_{t∖e}) - Σ_{faces F} Π_{e ⊂ F} x_e`, the products
written through power sums (`x₁x₂x₃ = (p₁³ - 3p₁p₂ + 2p₃)/6`). -/
noncomputable def tetV2 (ℓ : Finset V → ℝ) (t : Finset V) : ℝ :=
  ((∑ e ∈ t.powersetCard 2, ℓ e ^ 2 * ℓ (t \ e) ^ 2 *
        (∑ d ∈ t.powersetCard 2, ℓ d ^ 2 - 2 * ℓ e ^ 2 - 2 * ℓ (t \ e) ^ 2)) / 2 -
    ∑ f ∈ t.powersetCard 3, ((∑ e ∈ f.powersetCard 2, ℓ e ^ 2) ^ 3 -
      3 * (∑ e ∈ f.powersetCard 2, ℓ e ^ 2) * (∑ e ∈ f.powersetCard 2, ℓ e ^ 4) +
      2 * ∑ e ∈ f.powersetCard 2, ℓ e ^ 6) / 6) / 144

/-- `triH` is Heron's `heron` in any labelling of the triangle. -/
theorem triH_eq (ℓ : Finset V → ℝ) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    triH ℓ {p, q, r} = heron (ℓ {p, q}) (ℓ {q, r}) (ℓ {r, p}) := by
  rw [triH, sum_powersetCard_two_three hpq hpr hqr, sum_powersetCard_two_three hpq hpr hqr]
  unfold heron
  ring

/-- `tetV2` is `Lightlike.PR.vol2` in any labelling `A, B, C, D = p, q, r, s` of the tetrahedron. -/
theorem tetV2_eq (ℓ : Finset V → ℝ) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    tetV2 ℓ {p, q, r, s} =
      Lightlike.PR.vol2 (ℓ {p, q}) (ℓ {q, r}) (ℓ {r, p}) (ℓ {r, s}) (ℓ {p, s}) (ℓ {q, s}) := by
  have d1 : ({p, q, r, s} : Finset V) \ {p, q} = {r, s} := by ext x; simp; aesop
  have d2 : ({p, q, r, s} : Finset V) \ {q, r} = {p, s} := by ext x; simp; aesop
  have d3 : ({p, q, r, s} : Finset V) \ {r, p} = {q, s} := by ext x; simp; aesop
  have d4 : ({p, q, r, s} : Finset V) \ {r, s} = {p, q} := by ext x; simp; aesop
  have d5 : ({p, q, r, s} : Finset V) \ {p, s} = {q, r} := by ext x; simp; aesop
  have d6 : ({p, q, r, s} : Finset V) \ {q, s} = {r, p} := by ext x; simp; aesop
  rw [tetV2]
  simp only [sum_powersetCard_two_four hpq hpr hps hqr hqs hrs,
    sum_powersetCard_three_four hpq hpr hps hqr hqs hrs, d1, d2, d3, d4, d5, d6]
  simp only [sum_powersetCard_two_three hpq hpr hqr, sum_powersetCard_two_three hpq hps hqs,
    sum_powersetCard_two_three hpr hps hrs, sum_powersetCard_two_three hqr hqs hrs]
  rw [pair_comm s p, pair_comm s q, pair_comm p r]
  unfold Lightlike.PR.vol2
  ring

/-- Non-degenerate edge lengths on `K`: on every tetrahedron the six edge lengths are positive,
the four faces have positive area (`triH`) and the volume is positive (`tetV2`). The conditions
do not refer to any labelling of the vertices. -/
def LengthsNondeg (K : Complex3 V) (ℓ : Finset V → ℝ) : Prop :=
  ∀ t ∈ K.tets, (∀ e ∈ t.powersetCard 2, 0 < ℓ e) ∧ (∀ f ∈ t.powersetCard 3, 0 < triH ℓ f) ∧
    0 < tetV2 ℓ t

/-- **One condition for all labellings**: non-degenerate lengths make every tetrahedron
non-degenerate (`TetNondeg`) in every labelling `p, q, r, s` of its vertices. -/
theorem LengthsNondeg.tetNondeg {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ)
    {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (hrs : r ≠ s) (ht : ({p, q, r, s} : Finset V) ∈ K.tets) : TetNondeg (labLen ℓ p q r s) := by
  obtain ⟨hl, hf, hv⟩ := hK _ ht
  have e2 : ∀ {a b : V}, a ∈ ({p, q, r, s} : Finset V) → b ∈ ({p, q, r, s} : Finset V) → a ≠ b →
      0 < ℓ {a, b} := fun ha hb hab =>
    hl _ (mem_powersetCard.mpr ⟨by simp [insert_subset_iff, ha, hb], card_pair hab⟩)
  have e3 : ∀ {a b c : V}, a ∈ ({p, q, r, s} : Finset V) → b ∈ ({p, q, r, s} : Finset V) →
      c ∈ ({p, q, r, s} : Finset V) → a ≠ b → a ≠ c → b ≠ c → 0 < triH ℓ {a, b, c} :=
    fun ha hb hc hab hac hbc => hf _ (mem_powersetCard.mpr
      ⟨by simp [insert_subset_iff, ha, hb, hc],
        by rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]⟩)
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases i
    · exact e2 (by simp) (by simp) hpq
    · exact e2 (by simp) (by simp) hqr
    · exact e2 (by simp) (by simp) hpr.symm
    · exact e2 (by simp) (by simp) hrs
    · exact e2 (by simp) (by simp) hps
    · exact e2 (by simp) (by simp) hqs
  · have := e3 (a := p) (b := q) (c := r) (by simp) (by simp) (by simp) hpq hpr hqr
    rw [triH_eq ℓ hpq hpr hqr] at this
    exact this
  · have := e3 (a := p) (b := q) (c := s) (by simp) (by simp) (by simp) hpq hps hqs
    rw [triH_eq ℓ hpq hps hqs, pair_comm s p] at this
    exact this
  · have := e3 (a := r) (b := s) (c := p) (by simp) (by simp) (by simp) hrs hpr.symm hps.symm
    rw [triH_eq ℓ hrs hpr.symm hps.symm, pair_comm s p, pair_comm p r] at this
    show 0 < heron (ℓ {r, p}) (ℓ {r, s}) (ℓ {p, s})
    unfold heron at this ⊢
    linarith
  · have := e3 (a := q) (b := r) (c := s) (by simp) (by simp) (by simp) hqr hqs hrs
    rw [triH_eq ℓ hqr hqs hrs, pair_comm s q] at this
    exact this
  · rw [tetV2_eq ℓ hpq hpr hps hqr hqs hrs] at hv
    exact hv

omit [DecidableEq V] in
/-- With all lengths equal to `c`, a triangle has `triH = 3 c⁴`. -/
theorem triH_const {f : Finset V} (hf : #f = 3) (c : ℝ) : triH (fun _ => c) f = 3 * c ^ 4 := by
  simp only [triH, sum_const, card_powersetCard, hf, nsmul_eq_mul]
  norm_num [Nat.choose]
  ring

/-- With all lengths equal to `c`, a tetrahedron has `tetV2 = c⁶/72` (the regular tetrahedron). -/
theorem tetV2_const {t : Finset V} (ht : #t = 4) (c : ℝ) : tetV2 (fun _ => c) t = c ^ 6 / 72 := by
  have hf : ∀ f ∈ t.powersetCard 3, ((∑ e ∈ f.powersetCard 2, c ^ 2) ^ 3 -
      3 * (∑ e ∈ f.powersetCard 2, c ^ 2) * (∑ e ∈ f.powersetCard 2, c ^ 4) +
      2 * ∑ e ∈ f.powersetCard 2, c ^ 6) / 6 = c ^ 6 := by
    intro f hf
    simp only [sum_const, card_powersetCard, (mem_powersetCard.mp hf).2, nsmul_eq_mul]
    norm_num [Nat.choose]
    ring
  simp only [tetV2]
  rw [sum_congr rfl hf]
  simp only [sum_const, card_powersetCard, ht, nsmul_eq_mul]
  norm_num [Nat.choose]
  ring

/-- Equal positive lengths are non-degenerate on every complex. -/
theorem lengthsNondeg_const (K : Complex3 V) {c : ℝ} (hc : 0 < c) : LengthsNondeg K fun _ => c := by
  intro t ht
  refine ⟨fun _ _ => hc, fun f hf => ?_, ?_⟩
  · rw [triH_const (mem_powersetCard.mp hf).2]
    positivity
  · rw [tetV2_const (K.card_eq t ht)]
    positivity

/-- **One tetrahedron's contribution to the variation** (Schläfli): along a direction `v`, the
derivative of `Σ_{e ⊂ t} ℓ_e θ_t(e)` is `Σ_{e ⊂ t} v_e θ_t(e)`. -/
theorem hasDerivAt_tetSum {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ)
    (v : Finset V → ℝ) {t : Finset V} (ht : t ∈ K.tets) :
    HasDerivAt (fun τ => ∑ e ∈ t.powersetCard 2,
        (ℓ e + τ * v e) * dihedralAt (fun f => ℓ f + τ * v f) t e)
      (∑ e ∈ t.powersetCard 2, v e * dihedralAt ℓ t e) 0 := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label ht
  have hnd := hK.tetNondeg hpq hpr hps hqr hqs hrs ht
  have hlab : ∀ τ : ℝ, labLen (fun f => ℓ f + τ * v f) p q r s =
      fun i => labLen ℓ p q r s i + τ * labLen v p q r s i := by
    intro τ
    funext i
    fin_cases i <;> rfl
  -- near `τ = 0` all six lengths stay positive
  have hev : ∀ᶠ τ in nhds (0 : ℝ), ∀ i, labLen (fun f => ℓ f + τ * v f) p q r s i ≠ 0 := by
    have : ∀ i, ∀ᶠ τ in nhds (0 : ℝ), 0 < labLen ℓ p q r s i + τ * labLen v p q r s i := fun i =>
      (hasDerivAt_line _ _).continuousAt.eventually (lt_mem_nhds (by simpa using hnd.1 i))
    filter_upwards [Filter.eventually_all.mpr this] with τ hτ i
    rw [hlab]
    exact (hτ i).ne'
  have hR := hasDerivAt_reggeAction_tet (labLen ℓ p q r s) (labLen v p q r s) hnd
  have hlin : HasDerivAt (fun τ => π * ∑ i, (labLen ℓ p q r s i + τ * labLen v p q r s i))
      (π * ∑ i, labLen v p q r s i) 0 := by
    refine HasDerivAt.const_mul π ?_
    have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_line (labLen ℓ p q r s i)
      (labLen v p q r s i)
    convert this using 1
  refine ((hlin.sub hR).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with τ hτ
    rw [show (fun e => (ℓ e + τ * v e) * dihedralAt (fun f => ℓ f + τ * v f) {p, q, r, s} e) =
      (fun e => (fun f => ℓ f + τ * v f) e * dihedralAt (fun f => ℓ f + τ * v f) {p, q, r, s} e)
      from rfl]
    rw [tetSum_eq _ _ hpq hpr hps hqr hqs hrs hτ, hlab]
    simp only [Lightlike.PR.reggeAction, Pi.sub_apply, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  · rw [tetSum_eq ℓ v hpq hpr hps hqr hqs hrs fun i => (hnd.1 i).ne']
    simp only [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring

/-- **Regge's equations.** For non-degenerate edge lengths `ℓ` on `K` and any direction `v` of
change of the lengths, the derivative of the Regge action along `ℓ + τ v` at `τ = 0` is
`Σ_{interior} v_e δ_e + Σ_{boundary} v_e ψ_e`. In particular `∂S/∂ℓ_e` is the deficit angle at an
interior edge and the boundary angle at a boundary edge, so the action is stationary under
variations of the interior lengths exactly when all interior deficit angles vanish. -/
theorem hasDerivAt_reggeAction {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ)
    (v : Finset V → ℝ) :
    HasDerivAt (fun τ => reggeAction K fun e => ℓ e + τ * v e)
      (∑ e ∈ intEdges K, v e * deficit K ℓ e + ∑ e ∈ bdryEdges K, v e * bdryAngle K ℓ e) 0 := by
  have hint : HasDerivAt (fun τ => ∑ e ∈ intEdges K, 2 * π * (ℓ e + τ * v e))
      (∑ e ∈ intEdges K, 2 * π * v e) 0 :=
    HasDerivAt.fun_sum fun e _ => (hasDerivAt_line (ℓ e) (v e)).const_mul (2 * π)
  have hbd : HasDerivAt (fun τ => ∑ e ∈ bdryEdges K, π * (ℓ e + τ * v e))
      (∑ e ∈ bdryEdges K, π * v e) 0 :=
    HasDerivAt.fun_sum fun e _ => (hasDerivAt_line (ℓ e) (v e)).const_mul π
  have htets := HasDerivAt.fun_sum (u := K.tets) fun t ht => hasDerivAt_tetSum hK v ht
  rw [sum_curvature_eq]
  convert (hint.add hbd).sub htets using 1
  funext τ
  rw [reggeAction_eq_sum_tets]
  simp only [Pi.sub_apply, Pi.add_apply]

/-- **The discrete vacuum Einstein equations.** For non-degenerate edge lengths, the Regge action
is stationary under every variation that keeps the boundary lengths fixed exactly when the deficit
angle vanishes at every interior edge. -/
theorem reggeAction_stationary_iff {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ) :
    (∀ v : Finset V → ℝ, (∀ e ∈ bdryEdges K, v e = 0) →
      HasDerivAt (fun τ => reggeAction K fun e => ℓ e + τ * v e) 0 0) ↔
      ∀ e ∈ intEdges K, deficit K ℓ e = 0 := by
  constructor
  · intro h e he
    have hv : ∀ f ∈ bdryEdges K, (if f = e then (1 : ℝ) else 0) = 0 := by
      intro f hf
      have : f ≠ e := fun hfe =>
        disjoint_left.mp (disjoint_intEdges_bdryEdges K) he (hfe ▸ hf)
      simp [this]
    have h1 := h _ hv
    have h2 := hasDerivAt_reggeAction hK fun f => if f = e then (1 : ℝ) else 0
    have := h2.unique h1
    rw [sum_eq_zero (s := bdryEdges K) (fun f hf => by rw [hv f hf, zero_mul]), add_zero] at this
    simpa [ite_mul, sum_ite_eq', he] using this
  · intro h v hv
    convert hasDerivAt_reggeAction hK v using 1
    rw [sum_eq_zero (s := intEdges K) (fun e he => by rw [h e he, mul_zero]),
      sum_eq_zero (s := bdryEdges K) (fun e he => by rw [hv e he, zero_mul]), add_zero]

end Lightlike.Regge
