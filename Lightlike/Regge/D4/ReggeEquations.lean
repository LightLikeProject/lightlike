import Lightlike.Regge.D4.Schlaefli
import Lightlike.Regge.D4.Manifold

/-!
# Regge's equations in 4D

The 4D Regge action `S = Σ_{interior} A_t δ_t + Σ_{boundary} A_t ψ_t`
(`Lightlike/Regge/D4/Complex.lean`) depends on the edge lengths through the areas and through the
dihedral angles. By Schläfli's identity (`Lightlike/Regge/D4/Schlaefli.lean`) the variation of the
angles drops out 4-simplex by 4-simplex, so only the areas vary:

  `dS = Σ_{interior} dA_t δ_t + Σ_{boundary} dA_t ψ_t`.

In terms of the edge lengths this is Regge's equation (Regge 1961): for every interior edge `e`,
`∂S/∂ℓ_e = Σ_{t ∋ e} (∂A_t/∂ℓ_e) δ_t`, with `∂A_t/∂ℓ_e = ℓ_e (ℓ_f² + ℓ_g² - ℓ_e²) / (8 A_t)` for
the other two edges `f, g` of `t`. Unlike in 3D, stationarity does not force the deficit angles to
vanish; flat space is one solution (`Lightlike/Regge/D4/FlatSolution.lean`).

## Main results

* `bdryEdges4 K`, `intEdges4 K`: edges of boundary triangles, and the other edges.
* `LengthsNondeg4 K ℓ`: positive areas, volumes and 4-volumes, in every labelling.
* `areaDeriv ℓ v t`: the derivative of the area of `t` along `ℓ + τ v`; `areaPartial ℓ t e`:
  the partial derivative `∂A_t/∂ℓ_e`.
* `reggePartial4 K ℓ e = Σ_{t ∋ e} ∂A_t/∂ℓ_e · (δ_t or ψ_t)`.

* `reggeAction4_eq_sum_simps`: the action regrouped 4-simplex by 4-simplex.
* `hasDerivAt_simpSum4`: one 4-simplex's contribution varies only through its areas (Schläfli).
* `hasDerivAt_reggeAction4`, `hasDerivAt_reggeAction4_grad` (**Regge's equations**): the
  derivative of the action along every line of lengths, as a sum over triangles and as
  `Σ_e v_e ∂S/∂ℓ_e`.
* `reggeAction4_stationary_iff`: with the boundary lengths fixed, the action is stationary exactly
  when `Σ_{t ∋ e} (∂A_t/∂ℓ_e) δ_t = 0` at every interior edge.
-/

open Real Finset

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces mem_star mem_bdryTets card_of_mem_faces)
open Lightlike.Regge (triH triH_eq hasDerivAt_line)

variable {V : Type*} [DecidableEq V]

/-! ## Boundary and interior edges -/

/-- The boundary edges of `K`: edges of boundary triangles. -/
def bdryEdges4 (K : Complex4 V) : Finset (Finset V) :=
  K.edges.filter fun e => ∃ t ∈ bdryTris4 K, e ⊆ t

/-- The interior edges of `K`: edges contained in no boundary triangle. -/
def intEdges4 (K : Complex4 V) : Finset (Finset V) :=
  K.edges.filter fun e => ¬ ∃ t ∈ bdryTris4 K, e ⊆ t

/-! ## The action, 4-simplex by 4-simplex -/

/-- Exchanging the sum over triangles with the sum over 4-simplices: the pairs (triangle,
4-simplex containing it) are the pairs (4-simplex, one of its ten triangles). -/
theorem sum_tris_star (K : Complex4 V) (F : Finset V → Finset V → ℝ) :
    ∑ t ∈ K.tris, ∑ σ ∈ K.star t, F t σ = ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, F t σ := by
  apply sum_comm'
  intro t σ
  simp only [mem_star, mem_powersetCard]
  constructor
  · rintro ⟨ht, hσ, hs⟩
    exact ⟨⟨hs, card_of_mem_faces ht⟩, hσ⟩
  · rintro ⟨⟨hs, h3⟩, hσ⟩
    exact ⟨mem_faces.mpr ⟨σ, hσ, hs, h3⟩, hσ, hs⟩

/-- **The curvature sum, 4-simplex by 4-simplex.** For any weights `w` on triangles,
`Σ_{int} w_t δ_t + Σ_{bdry} w_t ψ_t = 2π Σ_{int} w_t + π Σ_{bdry} w_t - Σ_σ Σ_{t ⊂ σ} w_t θ_σ(t)`. -/
theorem sum_curvature4_eq (K : Complex4 V) (ℓ w : Finset V → ℝ) :
    ∑ t ∈ intTris4 K, w t * deficit4 K ℓ t + ∑ t ∈ bdryTris4 K, w t * bdryAngle4 K ℓ t =
      ∑ t ∈ intTris4 K, 2 * π * w t + ∑ t ∈ bdryTris4 K, π * w t -
        ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, w t * dihedralAt4 ℓ σ t := by
  have hsplit : ∑ t ∈ intTris4 K, w t * angleSum4 K ℓ t + ∑ t ∈ bdryTris4 K, w t * angleSum4 K ℓ t =
      ∑ t ∈ K.tris, w t * angleSum4 K ℓ t := by
    rw [← sum_union (disjoint_intTris4_bdryTris4 K), intTris4_union_bdryTris4]
  have hswap : ∑ t ∈ K.tris, w t * angleSum4 K ℓ t =
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, w t * dihedralAt4 ℓ σ t := by
    simp only [angleSum4, mul_sum]
    exact sum_tris_star K fun t σ => w t * dihedralAt4 ℓ σ t
  simp only [deficit4, bdryAngle4, mul_sub, sum_sub_distrib]
  rw [← hswap, ← hsplit]
  simp only [mul_comm (w _) (2 * π), mul_comm (w _) π]
  ring

/-- The Regge action rewritten 4-simplex by 4-simplex. -/
theorem reggeAction4_eq_sum_simps (K : Complex4 V) (ℓ : Finset V → ℝ) :
    reggeAction4 K ℓ = ∑ t ∈ intTris4 K, 2 * π * area4 ℓ t + ∑ t ∈ bdryTris4 K, π * area4 ℓ t -
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, area4 ℓ t * dihedralAt4 ℓ σ t :=
  sum_curvature4_eq K ℓ (area4 ℓ)

/-! ## Non-degenerate lengths -/

/-- Non-degenerate edge lengths on `K`: every triangle has positive area (`triH`), and every
tetrahedron and every 4-simplex has positive volume (`gram3`, `gram4`) in every labelling of its
vertices. -/
structure LengthsNondeg4 (K : Complex4 V) (ℓ : Finset V → ℝ) : Prop where
  /-- Positive areas. -/
  tri : ∀ t ∈ K.tris, 0 < triH ℓ t
  /-- Positive volumes. -/
  tet : ∀ p q r s : V, ({p, q, r, s} : Finset V) ∈ K.tets → 0 < gram3 ℓ p q r s
  /-- Positive 4-volumes. -/
  simp4 : ∀ p q r s u : V, ({p, q, r, s, u} : Finset V) ∈ K.simps → 0 < gram4 ℓ p q r s u

/-- The vertices of a 4-simplex can be labelled `p, q, r, s, u`. -/
theorem exists_label5 {σ : Finset V} (hσ : #σ = 5) :
    ∃ p q r s u, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ u ∧ q ≠ r ∧ q ≠ s ∧ q ≠ u ∧ r ≠ s ∧ r ≠ u ∧
      s ≠ u ∧ σ = {p, q, r, s, u} := by
  obtain ⟨p, t', hp, rfl, h4⟩ := card_eq_succ.mp hσ
  obtain ⟨q, r, s, u, hqr, hqs, hqu, hrs, hru, hsu, rfl⟩ := card_eq_four.mp h4
  simp only [mem_insert, mem_singleton, not_or] at hp
  exact ⟨p, q, r, s, u, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hqr, hqs, hqu, hrs, hru, hsu, rfl⟩

/-- A triangle of a 4-simplex of `K` is a triangle of `K`. -/
theorem mem_tris_of_subset {K : Complex4 V} {σ : Finset V} (hσ : σ ∈ K.simps) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : ({a, b, c} : Finset V) ⊆ σ) :
    ({a, b, c} : Finset V) ∈ K.tris :=
  mem_faces.mpr ⟨σ, hσ, h, card_three hab hac hbc⟩

/-- A tetrahedron of a 4-simplex of `K` is a tetrahedron of `K`. -/
theorem mem_tets_of_subset {K : Complex4 V} {σ : Finset V} (hσ : σ ∈ K.simps) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : ({a, b, c, d} : Finset V) ⊆ σ) : ({a, b, c, d} : Finset V) ∈ K.tets :=
  mem_faces.mpr ⟨σ, hσ, h, card_four hab hac had hbc hbd hcd⟩

/-- `gram2 > 0` for the triangles of `K`. -/
theorem LengthsNondeg4.gram2_pos {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ht : ({a, b, c} : Finset V) ∈ K.tris) :
    0 < gram2 ℓ a b c := by
  have := hK.tri _ ht
  rw [triH_eq_gram2 ℓ hab hac hbc] at this
  linarith

/-- **One condition for all labellings**: non-degenerate lengths make every 4-simplex
non-degenerate (`Nondeg4`) in every labelling. -/
theorem LengthsNondeg4.nondeg4 {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ)
    {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r)
    (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hσ : ({p, q, r, s, u} : Finset V) ∈ K.simps) : Nondeg4 ℓ p q r s u := by
  have sub : ∀ {A : Finset V}, A ⊆ {p, q, r, s, u} → A ⊆ ({p, q, r, s, u} : Finset V) := id
  have T : ∀ {a b c : V}, a ∈ ({p, q, r, s, u} : Finset V) → b ∈ ({p, q, r, s, u} : Finset V) →
      c ∈ ({p, q, r, s, u} : Finset V) → a ≠ b → a ≠ c → b ≠ c → 0 < gram2 ℓ a b c :=
    fun ha hb hc hab hac hbc => hK.gram2_pos hab hac hbc
      (mem_tris_of_subset hσ hab hac hbc (by simp [insert_subset_iff, ha, hb, hc]))
  have F : ∀ {a b c d : V}, a ∈ ({p, q, r, s, u} : Finset V) → b ∈ ({p, q, r, s, u} : Finset V) →
      c ∈ ({p, q, r, s, u} : Finset V) → d ∈ ({p, q, r, s, u} : Finset V) → a ≠ b → a ≠ c →
      a ≠ d → b ≠ c → b ≠ d → c ≠ d → 0 < gram3 ℓ a b c d :=
    fun ha hb hc hd hab hac had hbc hbd hcd => hK.tet _ _ _ _
      (mem_tets_of_subset hσ hab hac had hbc hbd hcd
        (by simp [insert_subset_iff, ha, hb, hc, hd]))
  clear sub
  exact ⟨T (by simp) (by simp) (by simp) hpq hpr hqr, T (by simp) (by simp) (by simp) hpq hps hqs,
    T (by simp) (by simp) (by simp) hpq hpu hqu, T (by simp) (by simp) (by simp) hpr hps hrs,
    T (by simp) (by simp) (by simp) hpr hpu hru, T (by simp) (by simp) (by simp) hps hpu hsu,
    T (by simp) (by simp) (by simp) hqr hqs hrs, T (by simp) (by simp) (by simp) hqr hqu hru,
    T (by simp) (by simp) (by simp) hqs hqu hsu, T (by simp) (by simp) (by simp) hrs hru hsu,
    F (by simp) (by simp) (by simp) (by simp) hpq hpr hps hqr hqs hrs,
    F (by simp) (by simp) (by simp) (by simp) hpq hpr hpu hqr hqu hru,
    F (by simp) (by simp) (by simp) (by simp) hpq hps hpu hqs hqu hsu,
    F (by simp) (by simp) (by simp) (by simp) hpr hps hpu hrs hru hsu,
    F (by simp) (by simp) (by simp) (by simp) hqr hqs hqu hrs hru hsu, hK.simp4 _ _ _ _ _ hσ⟩

/-! ## Equal lengths -/

set_option linter.unusedSimpArgs false in
/-- With all lengths `a`, a tetrahedron has `gram3 = a⁶/2` (`V² = a⁶/72`). -/
theorem gram3_const (a : ℝ) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) : gram3 (fun _ => a) p q r s = (a ^ 2) ^ 3 / 2 := by
  simp only [gram3, det3, ip, sq, hpq, hpr, hps, hqr, hqs, hrs, Ne.symm hpq, Ne.symm hpr,
    Ne.symm hps, Ne.symm hqr, Ne.symm hqs, Ne.symm hrs, ite_true, ite_false]
  ring

set_option linter.unusedSimpArgs false in
/-- With all lengths `a`, a 4-simplex has `gram4 = 5 a⁸/16` (`V₄² = 5 a⁸/9216`). -/
theorem gram4_const (a : ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u)
    (hsu : s ≠ u) : gram4 (fun _ => a) p q r s u = 5 * (a ^ 2) ^ 4 / 16 := by
  simp only [gram4, det3, ip, sq, hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu,
    Ne.symm hpq, Ne.symm hpr, Ne.symm hps, Ne.symm hpu, Ne.symm hqr, Ne.symm hqs, Ne.symm hqu,
    Ne.symm hrs, Ne.symm hru, Ne.symm hsu, ite_true, ite_false]
  ring

/-- Equal nonzero lengths are non-degenerate on every 4-complex. -/
theorem lengthsNondeg4_const (K : Complex4 V) {a : ℝ} (ha : a ≠ 0) :
    LengthsNondeg4 K fun _ => a := by
  have ha2 : 0 < a ^ 2 := by positivity
  refine ⟨fun t ht => ?_, fun p q r s hτ => ?_, fun p q r s u hσ => ?_⟩
  · rw [Lightlike.Regge.triH_const (card_of_mem_faces ht)]
    positivity
  · have h4 : #({p, q, r, s} : Finset V) = 4 := card_of_mem_faces hτ
    -- the given labelling is injective since the set has four elements
    have hd : p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
        simp only [insert_eq_of_mem, mem_insert, mem_singleton, true_or, or_true] at h4 <;>
        exact absurd h4 (ne_of_lt (lt_of_le_of_lt card_le_three (by norm_num)))
    obtain ⟨h1, h2, h3, h4', h5, h6⟩ := hd
    rw [gram3_const a h1 h2 h3 h4' h5 h6]
    positivity
  · have h5 : #({p, q, r, s, u} : Finset V) = 5 := K.card_eq _ hσ
    have hd : p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ u ∧ q ≠ r ∧ q ≠ s ∧ q ≠ u ∧ r ≠ s ∧ r ≠ u ∧
        s ≠ u := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
        simp only [insert_eq_of_mem, mem_insert, mem_singleton, true_or, or_true] at h5 <;>
        exact absurd h5 (ne_of_lt (lt_of_le_of_lt card_le_four (by norm_num)))
    obtain ⟨h1, h2, h3, h4, h5', h6, h7, h8, h9, h10⟩ := hd
    rw [gram4_const a h1 h2 h3 h4 h5' h6 h7 h8 h9 h10]
    positivity

/-! ## Areas along a line of lengths -/

/-- The derivative of the area of the triangle `t` along `ℓ + τ v` at `τ = 0`:
`(4 (Σ ℓ_e²)(Σ ℓ_e v_e) - 8 Σ ℓ_e³ v_e) / (8 √triH)`, sums over the three edges. -/
noncomputable def areaDeriv (ℓ v : Finset V → ℝ) (t : Finset V) : ℝ :=
  (4 * (∑ e ∈ t.powersetCard 2, ℓ e ^ 2) * (∑ e ∈ t.powersetCard 2, ℓ e * v e) -
    8 * ∑ e ∈ t.powersetCard 2, ℓ e ^ 3 * v e) / (8 * √(triH ℓ t))

omit [DecidableEq V] in
/-- The areas vary as `areaDeriv` along a line of lengths. -/
theorem hasDerivAt_area4 [DecidableEq V] (ℓ v : Finset V → ℝ) {t : Finset V}
    (h : 0 < triH ℓ t) : HasDerivAt (fun τ => area4 (lineL ℓ v τ) t) (areaDeriv ℓ v t) 0 := by
  have h2 : HasDerivAt (fun τ => ∑ e ∈ t.powersetCard 2, (ℓ e + τ * v e) ^ 2)
      (∑ e ∈ t.powersetCard 2, 2 * ℓ e * v e) 0 := by
    refine (HasDerivAt.fun_sum fun e _ => (hasDerivAt_line (ℓ e) (v e)).pow 2).congr_deriv ?_
    refine sum_congr rfl fun e _ => ?_
    simp
  have h4 : HasDerivAt (fun τ => ∑ e ∈ t.powersetCard 2, (ℓ e + τ * v e) ^ 4)
      (∑ e ∈ t.powersetCard 2, 4 * ℓ e ^ 3 * v e) 0 := by
    refine (HasDerivAt.fun_sum fun e _ => (hasDerivAt_line (ℓ e) (v e)).pow 4).congr_deriv ?_
    refine sum_congr rfl fun e _ => ?_
    simp
  have hH : HasDerivAt (fun τ => triH (lineL ℓ v τ) t)
      (2 * (∑ e ∈ t.powersetCard 2, ℓ e ^ 2) * (∑ e ∈ t.powersetCard 2, 2 * ℓ e * v e) -
        2 * ∑ e ∈ t.powersetCard 2, 4 * ℓ e ^ 3 * v e) 0 := by
    have := (h2.pow 2).sub (h4.const_mul 2)
    simp only [triH, lineL]
    convert this using 1
    simp
  have hS := hH.sqrt (by simpa [lineL] using h.ne')
  refine (hS.div_const 4).congr_deriv ?_
  have e1 : ∑ e ∈ t.powersetCard 2, 2 * ℓ e * v e = 2 * ∑ e ∈ t.powersetCard 2, ℓ e * v e := by
    rw [mul_sum]
    exact sum_congr rfl fun e _ => by ring
  have e2 : ∑ e ∈ t.powersetCard 2, 4 * ℓ e ^ 3 * v e =
      4 * ∑ e ∈ t.powersetCard 2, ℓ e ^ 3 * v e := by
    rw [mul_sum]
    exact sum_congr rfl fun e _ => by ring
  simp only [lineL_zero]
  rw [e1, e2, areaDeriv]
  have hs : √(triH ℓ t) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  field_simp
  ring

/-- The partial derivative `∂A_t/∂ℓ_e = ℓ_e (Σ_{f ⊂ t} ℓ_f² - 2 ℓ_e²) / (2 √triH)`; for the edge
`e` of `t` with the other edges `f, g` this is `ℓ_e (ℓ_f² + ℓ_g² - ℓ_e²) / (8 A_t)`. -/
noncomputable def areaPartial (ℓ : Finset V → ℝ) (t e : Finset V) : ℝ :=
  ℓ e * (∑ f ∈ t.powersetCard 2, ℓ f ^ 2 - 2 * ℓ e ^ 2) / (2 * √(triH ℓ t))

omit [DecidableEq V] in
/-- `areaDeriv` is linear in the variation: `dA_t = Σ_{e ⊂ t} v_e ∂A_t/∂ℓ_e`. -/
theorem areaDeriv_eq_sum (ℓ v : Finset V → ℝ) (t : Finset V) :
    areaDeriv ℓ v t = ∑ e ∈ t.powersetCard 2, v e * areaPartial ℓ t e := by
  have key : ∑ e ∈ t.powersetCard 2, v e * (ℓ e * (∑ f ∈ t.powersetCard 2, ℓ f ^ 2 - 2 * ℓ e ^ 2)) =
      (∑ f ∈ t.powersetCard 2, ℓ f ^ 2) * (∑ e ∈ t.powersetCard 2, ℓ e * v e) -
        2 * ∑ e ∈ t.powersetCard 2, ℓ e ^ 3 * v e := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  simp only [areaPartial, mul_div_assoc']
  rw [← sum_div, key, areaDeriv]
  by_cases h : √(triH ℓ t) = 0
  · simp [h]
  field_simp
  ring

/-! ## One 4-simplex -/

/-- The dihedral angles of a 4-simplex of `K` are differentiable along every line of lengths. -/
theorem LengthsNondeg4.hasDerivAt_dihedralAt4 {K : Complex4 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg4 K ℓ) (v : Finset V → ℝ) {σ : Finset V} (hσ : σ ∈ K.simps)
    {t : Finset V} (ht : t ∈ σ.powersetCard 3) :
    HasDerivAt (fun τ => dihedralAt4 (lineL ℓ v τ) σ t)
      (deriv (fun τ => dihedralAt4 (lineL ℓ v τ) σ t) 0) 0 := by
  obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
  obtain ⟨a, b, c, x, y, hab, hac, hax, hay, hbc, hbx, hby, hcx, hcy, hxy, rfl, rfl⟩ :=
    exists_label4 (K.card_eq σ hσ) ht3 hts
  have hfun : (fun τ => dihedralAt4 (lineL ℓ v τ) {a, b, c, x, y} {a, b, c}) =
      fun τ => dihedral4 (lineL ℓ v τ) a b c x y :=
    funext fun τ => dihedralAt4_eq _ hab hac hax hay hbc hbx hby hcx hcy hxy
  have hnd := hK.nondeg4 hab hac hax hay hbc hbx hby hcx hcy hxy hσ
  rw [hfun]
  exact (hasDerivAt_dihedral4_line ℓ v a b c x y hnd.f_u hnd.f_s hnd.t₁ hnd.g4).differentiableAt
    |>.hasDerivAt

/-- **One 4-simplex's contribution to the variation** (Schläfli): along a direction `v`, the
derivative of `Σ_{t ⊂ σ} A_t θ_σ(t)` is `Σ_{t ⊂ σ} dA_t θ_σ(t)`; the variation of the angles
cancels. -/
theorem hasDerivAt_simpSum4 {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ)
    (v : Finset V → ℝ) {σ : Finset V} (hσ : σ ∈ K.simps) :
    HasDerivAt (fun τ => ∑ t ∈ σ.powersetCard 3,
        area4 (lineL ℓ v τ) t * dihedralAt4 (lineL ℓ v τ) σ t)
      (∑ t ∈ σ.powersetCard 3, areaDeriv ℓ v t * dihedralAt4 ℓ σ t) 0 := by
  have hA : ∀ t ∈ σ.powersetCard 3, HasDerivAt (fun τ => area4 (lineL ℓ v τ) t)
      (areaDeriv ℓ v t) 0 := fun t ht => by
    obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
    exact hasDerivAt_area4 ℓ v (hK.tri t (mem_faces.mpr ⟨σ, hσ, hts, ht3⟩))
  have hθ : ∀ t ∈ σ.powersetCard 3, HasDerivAt (fun τ => dihedralAt4 (lineL ℓ v τ) σ t)
      (deriv (fun τ => dihedralAt4 (lineL ℓ v τ) σ t) 0) 0 :=
    fun t ht => hK.hasDerivAt_dihedralAt4 v hσ ht
  have hprod := HasDerivAt.fun_sum fun t ht => (hA t ht).mul (hθ t ht)
  -- Schläfli: the angle variation, weighted by the areas at `ℓ`, vanishes
  obtain ⟨p, q, r, s, u, hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu, rfl⟩ :=
    exists_label5 (K.card_eq σ hσ)
  have hS := schlaefli4_finset ℓ v hpq hpr hps hpu hqr hqs hqu hrs hru hsu
    (hK.nondeg4 hpq hpr hps hpu hqr hqs hqu hrs hru hsu hσ)
  have hS' := HasDerivAt.fun_sum fun t ht => (hθ t ht).const_mul (area4 ℓ t)
  have hzero := hS'.unique hS
  refine hprod.congr_deriv ?_
  simp only [lineL_zero, sum_add_distrib, hzero, add_zero]

/-! ## Regge's equations -/

/-- **Regge's equations.** For non-degenerate edge lengths `ℓ` on `K` and any direction `v` of
change of the lengths, the derivative of the 4D Regge action along `ℓ + τ v` at `τ = 0` is
`Σ_{interior} dA_t δ_t + Σ_{boundary} dA_t ψ_t`: only the areas vary. -/
theorem hasDerivAt_reggeAction4 {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ)
    (v : Finset V → ℝ) :
    HasDerivAt (fun τ => reggeAction4 K (lineL ℓ v τ))
      (∑ t ∈ intTris4 K, areaDeriv ℓ v t * deficit4 K ℓ t +
        ∑ t ∈ bdryTris4 K, areaDeriv ℓ v t * bdryAngle4 K ℓ t) 0 := by
  have hA : ∀ t ∈ K.tris, HasDerivAt (fun τ => area4 (lineL ℓ v τ) t) (areaDeriv ℓ v t) 0 :=
    fun t ht => hasDerivAt_area4 ℓ v (hK.tri t ht)
  have hint : HasDerivAt (fun τ => ∑ t ∈ intTris4 K, 2 * π * area4 (lineL ℓ v τ) t)
      (∑ t ∈ intTris4 K, 2 * π * areaDeriv ℓ v t) 0 :=
    HasDerivAt.fun_sum fun t ht => (hA t (mem_filter.mp ht).1).const_mul (2 * π)
  have hbd : HasDerivAt (fun τ => ∑ t ∈ bdryTris4 K, π * area4 (lineL ℓ v τ) t)
      (∑ t ∈ bdryTris4 K, π * areaDeriv ℓ v t) 0 :=
    HasDerivAt.fun_sum fun t ht => (hA t (mem_filter.mp ht).1).const_mul π
  have hsimps := HasDerivAt.fun_sum (u := K.simps) fun σ hσ => hasDerivAt_simpSum4 hK v hσ
  rw [sum_curvature4_eq]
  convert (hint.add hbd).sub hsimps using 1
  funext τ
  rw [reggeAction4_eq_sum_simps]
  simp only [Pi.sub_apply, Pi.add_apply]

/-- The partial derivative of the Regge action with respect to the length of the edge `e`:
`∂S/∂ℓ_e = Σ_{t ∋ e} (∂A_t/∂ℓ_e) δ_t` over interior triangles plus the same with `ψ_t` over
boundary triangles. -/
noncomputable def reggePartial4 (K : Complex4 V) (ℓ : Finset V → ℝ) (e : Finset V) : ℝ :=
  ∑ t ∈ (intTris4 K).filter (e ⊆ ·), areaPartial ℓ t e * deficit4 K ℓ t +
    ∑ t ∈ (bdryTris4 K).filter (e ⊆ ·), areaPartial ℓ t e * bdryAngle4 K ℓ t

/-- Exchanging the sum over triangles of a set `T ⊆ K.tris` with the sum over edges. -/
theorem sum_tris_edges {K : Complex4 V} {T : Finset (Finset V)} (hT : T ⊆ K.tris)
    (F : Finset V → Finset V → ℝ) :
    ∑ t ∈ T, ∑ e ∈ t.powersetCard 2, F t e = ∑ e ∈ K.edges, ∑ t ∈ T.filter (e ⊆ ·), F t e := by
  apply sum_comm'
  intro t e
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨ht, hs, h2⟩
    obtain ⟨σ, hσ, htσ, -⟩ := mem_faces.mp (hT ht)
    exact ⟨⟨ht, hs⟩, mem_faces.mpr ⟨σ, hσ, hs.trans htσ, h2⟩⟩
  · rintro ⟨⟨ht, hs⟩, he⟩
    exact ⟨ht, hs, card_of_mem_faces he⟩

/-- **Regge's equations, edge by edge.** Along every direction `v` the derivative of the Regge
action is `Σ_e v_e ∂S/∂ℓ_e`. -/
theorem hasDerivAt_reggeAction4_grad {K : Complex4 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg4 K ℓ) (v : Finset V → ℝ) :
    HasDerivAt (fun τ => reggeAction4 K (lineL ℓ v τ))
      (∑ e ∈ K.edges, v e * reggePartial4 K ℓ e) 0 := by
  refine (hasDerivAt_reggeAction4 hK v).congr_deriv ?_
  have hi : intTris4 K ⊆ K.tris := filter_subset _ _
  have hb : bdryTris4 K ⊆ K.tris := filter_subset _ _
  simp only [areaDeriv_eq_sum, sum_mul]
  rw [sum_tris_edges hi, sum_tris_edges hb, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  simp only [reggePartial4, mul_add, mul_sum]
  congr 1 <;> exact sum_congr rfl fun t _ => by ring

/-- An interior edge lies only in interior triangles. -/
theorem filter_bdryTris4_eq_empty {K : Complex4 V} {e : Finset V} (he : e ∈ intEdges4 K) :
    (bdryTris4 K).filter (e ⊆ ·) = ∅ :=
  filter_eq_empty_iff.mpr fun t ht hsub => (mem_filter.mp he).2 ⟨t, ht, hsub⟩

/-- **The discrete Einstein equations in 4D.** For non-degenerate edge lengths, the Regge action is
stationary under every variation that keeps the boundary lengths fixed exactly when
`∂S/∂ℓ_e = Σ_{t ∋ e} (∂A_t/∂ℓ_e) δ_t` vanishes at every interior edge. -/
theorem reggeAction4_stationary_iff {K : Complex4 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg4 K ℓ) :
    (∀ v : Finset V → ℝ, (∀ e ∈ bdryEdges4 K, v e = 0) →
      HasDerivAt (fun τ => reggeAction4 K (lineL ℓ v τ)) 0 0) ↔
    ∀ e ∈ intEdges4 K,
      ∑ t ∈ (intTris4 K).filter (e ⊆ ·), areaPartial ℓ t e * deficit4 K ℓ t = 0 := by
  have hpart : ∀ e ∈ intEdges4 K, reggePartial4 K ℓ e =
      ∑ t ∈ (intTris4 K).filter (e ⊆ ·), areaPartial ℓ t e * deficit4 K ℓ t := fun e he => by
    rw [reggePartial4, filter_bdryTris4_eq_empty he, sum_empty, add_zero]
  constructor
  · intro h e he
    have hv : ∀ f ∈ bdryEdges4 K, (fun g => if g = e then (1 : ℝ) else 0) f = 0 := by
      intro f hf
      have : f ≠ e := fun hfe => (mem_filter.mp he).2 (hfe ▸ (mem_filter.mp hf).2)
      simp [this]
    have h1 := (hasDerivAt_reggeAction4_grad hK fun g => if g = e then (1 : ℝ) else 0).unique
      (h _ hv)
    rw [sum_eq_single e (fun f _ hfe => by simp [hfe]) (fun hn => absurd (mem_filter.mp he).1 hn),
      ite_eq_left rfl, one_mul] at h1
    rw [← hpart e he]
    exact h1
  · intro h v hv
    refine (hasDerivAt_reggeAction4_grad hK v).congr_deriv ?_
    refine sum_eq_zero fun e he => ?_
    by_cases hb : ∃ t ∈ bdryTris4 K, e ⊆ t
    · rw [hv e (mem_filter.mpr ⟨he, hb⟩), zero_mul]
    · have he' : e ∈ intEdges4 K := mem_filter.mpr ⟨he, hb⟩
      rw [hpart e he', h e he', mul_zero]

end Lightlike.Regge4
