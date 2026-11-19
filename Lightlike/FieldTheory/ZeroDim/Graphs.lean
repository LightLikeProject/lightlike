import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Physlib.Mathematics.ForMathlib.Fin.Involutions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Vacuum Feynman graphs of the quartic theory and their symmetry factors

Borinsky (2018), Chapter 2: a graph is a set of half-edges `H` with a map `ν : H → V` to the vertices and an
involution `ι` of `H` (Def. 2.1.1/2.1.2, p. 10); an automorphism is a pair of bijections of half-edges and
vertices compatible with `ν` and `ι` (Def. 2.1.6, 2.1.7, p. 11); unlabelled graphs are the orbits of labelled
ones under relabelling, and `|Orb G|/(m! k!) = 1/|Aut G|` (Prop. 2.3.1, p. 15).

Here (representation): the vacuum graphs with `m` four-valent vertices have the fixed corollas
`Fin m × Fin 4 → Fin m` and a fixed-point-free involution `ι` of the half-edges (`Pairing m`); relabellings
that keep the corollas are the wreath product `S₄ ≀ S_m` (`vertexPerm m`, order `24^m m!`), acting by
conjugation. An automorphism in Borinsky's sense is determined by its half-edge bijection, which then lies in
`vertexPerm m` and commutes with `ι`; so `Aut Γ` is the stabilizer, and a graph is an orbit.

`sum_inv_card_stabilizer`: for any finite group action, `∑_{orbits} 1/|Stab| = |X|/|G|` (class formula).
`sum_inv_aut`: `∑_Γ 1/|Aut Γ| = (4m - 1)!!/(24^m m!)` over the vacuum graphs with `m` vertices, the coefficient
of `(-g)^m` in `quartic_expansion` divided by `√(2π)`: the expansion is the sum over Feynman graphs with their
symmetry factors (Borinsky, Prop. 3.1.1, p. 23, for `λ₄ = -g`, `a = 1`).
-/

namespace Lightlike.FieldTheory

open MulAction Nat

/-- **Orbit counting with symmetry factors**: `∑_{ω ∈ X/G} 1/|G_ω| = |X|/|G|`. -/
theorem sum_inv_card_stabilizer (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
    [Fintype (Quotient (orbitRel G X))] :
    ∑ ω : Quotient (orbitRel G X), (1 : ℚ) / Nat.card (stabilizer G ω.out) =
      (Nat.card X : ℚ) / Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  simp_rw [Nat.card_eq_fintype_card]
  have h := card_eq_sum_card_group_div_card_stabilizer G X
  have hG : (0 : ℚ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [eq_div_iff hG.ne', h, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hdvd : Fintype.card (stabilizer G ω.out) ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card (stabilizer G ω.out)
  rw [Nat.cast_div hdvd (by exact_mod_cast (Fintype.card_pos (α := stabilizer G ω.out)).ne')]
  field_simp

end Lightlike.FieldTheory

/-! ## The half-edges of `m` quartic vertices and their symmetries -/

namespace Lightlike.FieldTheory

/-- The permutations of the half-edges `Fin m × Fin 4` that map vertices to vertices (the wreath product
`S₄ ≀ S_m`). -/
def vertexPerm (m : ℕ) : Subgroup (Equiv.Perm (Fin m × Fin 4)) where
  carrier := {σ | ∃ π : Equiv.Perm (Fin m), ∀ v i, (σ (v, i)).1 = π v}
  one_mem' := ⟨1, fun v i => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨π, hπ⟩ ⟨ρ, hρ⟩
    refine ⟨π * ρ, fun v i => ?_⟩
    show (σ (τ (v, i))).1 = π (ρ v)
    rw [← hρ v i]
    exact hπ _ _
  inv_mem' := by
    rintro σ ⟨π, hπ⟩
    refine ⟨π⁻¹, fun v i => ?_⟩
    have h := hπ (σ⁻¹ (v, i)).1 (σ⁻¹ (v, i)).2
    rw [Prod.mk.eta, show σ (σ⁻¹ (v, i)) = (v, i) from σ.apply_symm_apply (v, i)] at h
    rw [Equiv.Perm.eq_inv_iff_eq]
    exact h.symm

/-- The pairings (fixed-point-free involutions) of the half-edges. -/
def Pairing (m : ℕ) : Type :=
  {f : Fin m × Fin 4 → Fin m × Fin 4 // Function.Involutive f ∧ ∀ h, f h ≠ h}

instance (m : ℕ) : Finite (Pairing m) := by unfold Pairing; infer_instance

/-- The vertex-preserving permutations act on pairings by conjugation. -/
instance (m : ℕ) : MulAction (vertexPerm m) (Pairing m) where
  smul g f := ⟨g.1 ∘ f.1 ∘ g.1.symm, fun h => by
      simp only [Function.comp_apply, Equiv.symm_apply_apply, f.2.1 (g.1.symm h), Equiv.apply_symm_apply],
    fun h hh => by
      apply f.2.2 (g.1.symm h)
      have := congrArg g.1.symm hh
      simpa using this⟩
  one_smul f := by apply Subtype.ext; rfl
  mul_smul g k f := by apply Subtype.ext; rfl

end Lightlike.FieldTheory

namespace Lightlike.FieldTheory

open MulAction Nat

/-- A vertex-preserving permutation is a permutation `π` of the vertices with a permutation of the
half-edges at each vertex: `vertexPerm m ≃ S_m × (Fin m → S₄)`. -/
noncomputable def vertexPermEquiv (m : ℕ) :
    vertexPerm m ≃ Equiv.Perm (Fin m) × (Fin m → Equiv.Perm (Fin 4)) where
  toFun σ := by
    classical
    refine ⟨Classical.choose σ.2, fun v => Equiv.ofBijective (fun i => (σ.1 (v, i)).2) ?_⟩
    refine Finite.injective_iff_bijective.1 fun i j hij => ?_
    have h1 := Classical.choose_spec σ.2 v i
    have h2 := Classical.choose_spec σ.2 v j
    have : σ.1 (v, i) = σ.1 (v, j) := Prod.ext (h1.trans h2.symm) hij
    simpa using σ.1.injective this
  invFun p := ⟨Equiv.prodShear p.1 p.2, p.1, fun v i => rfl⟩
  left_inv σ := by
    apply Subtype.ext
    refine Equiv.ext fun ⟨v, i⟩ => Prod.ext ?_ rfl
    exact (Classical.choose_spec σ.2 v i).symm
  right_inv p := by
    have hπ : Classical.choose (⟨p.1, fun v i => rfl⟩ :
        ∃ π : Equiv.Perm (Fin m), ∀ v i, (Equiv.prodShear p.1 p.2 (v, i)).1 = π v) = p.1 := by
      refine Equiv.ext fun v => ?_
      exact ((Classical.choose_spec (⟨p.1, fun v i => rfl⟩ :
        ∃ π : Equiv.Perm (Fin m), ∀ v i, (Equiv.prodShear p.1 p.2 (v, i)).1 = π v)) v 0).symm
    exact Prod.ext hπ (funext fun v => Equiv.ext fun i => rfl)

/-- `|S₄ ≀ S_m| = 24^m m!`. -/
lemma card_vertexPerm (m : ℕ) : Nat.card (vertexPerm m) = 24 ^ m * m.factorial := by
  rw [Nat.card_congr (vertexPermEquiv m), Nat.card_prod, Nat.card_fun, Nat.card_perm, Nat.card_perm]
  simp [Nat.factorial, mul_comm]

/-- The pairings of `4m` half-edges number `(4m - 1)!!`. -/
lemma card_pairing (m : ℕ) : Nat.card (Pairing m) = (4 * m - 1)‼ := by
  classical
  let e : Fin m × Fin 4 ≃ Fin (m * 4) := finProdFinEquiv
  have eq : Pairing m ≃ {f : Fin (m * 4) → Fin (m * 4) // Function.Involutive f ∧ ∀ i, f i ≠ i} :=
    (Equiv.arrowCongr e e).subtypeEquiv fun f => by
      simp only [Equiv.arrowCongr_apply, Function.comp_def]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i => by simp [h1 _], fun i hi => h2 (e.symm i) ?_⟩
        simpa using congrArg e.symm hi
      · rintro ⟨h1, h2⟩
        refine ⟨fun h => ?_, fun h hh => h2 (e h) (by simp [hh])⟩
        simpa using h1 (e h)
  rw [Nat.card_congr eq, Nat.card_eq_fintype_card,
    Physlib.Fin.involutionNoFixed_card_even (m * 4) ⟨2 * m, by ring⟩]
  congr 1
  omega

/-- **The vacuum graphs of the quartic theory with their symmetry factors**: summed over the graphs
(orbits of pairings) with `m` vertices, `∑ 1/|Aut Γ| = (4m - 1)!! / (24^m m!)`, the coefficient of
`(-g)^m` in the expansion of `∫ e^{-x²/2 - g x⁴/24} dx / √(2π)` (`quartic_expansion`). -/
theorem sum_inv_aut (m : ℕ) [Fintype (Quotient (orbitRel (vertexPerm m) (Pairing m)))] :
    ∑ Γ : Quotient (orbitRel (vertexPerm m) (Pairing m)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm m) Γ.out) =
      ((4 * m - 1)‼ : ℚ) / (24 ^ m * m.factorial) := by
  rw [sum_inv_card_stabilizer, card_pairing, card_vertexPerm]
  push_cast
  ring

/-- **Trust check, order `g²`**: the symmetry factors of the vacuum graphs with two four-valent vertices sum to
`35/384`, Borinsky's coefficient in (3.1.8), p. 24 (`1/128 + 1/16 + 1/48` for the three graphs). -/
theorem sum_inv_aut_two [Fintype (Quotient (orbitRel (vertexPerm 2) (Pairing 2)))] :
    ∑ Γ : Quotient (orbitRel (vertexPerm 2) (Pairing 2)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm 2) Γ.out) = 35 / 384 := by
  rw [sum_inv_aut]
  norm_num [Nat.doubleFactorial, Nat.factorial]

/-- **Trust check, order `g`**: the vacuum graphs with one four-valent vertex (the figure-eight) have total
symmetry factor `1/8`. -/
theorem sum_inv_aut_one [Fintype (Quotient (orbitRel (vertexPerm 1) (Pairing 1)))] :
    ∑ Γ : Quotient (orbitRel (vertexPerm 1) (Pairing 1)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm 1) Γ.out) = 1 / 8 := by
  rw [sum_inv_aut]
  norm_num [Nat.doubleFactorial, Nat.factorial]

/-! ## The three vacuum graphs with two vertices -/

/-- Points in one orbit have stabilizers of the same order. -/
lemma card_stabilizer_eq_of_rel {G X : Type*} [Group G] [MulAction G X] {x y : X} (h : orbitRel G X x y) :
    Nat.card (stabilizer G x) = Nat.card (stabilizer G y) := by
  obtain ⟨g, rfl⟩ := h
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- The number of half-edges paired with a half-edge at another vertex. -/
def crossCount {m : ℕ} (p : Pairing m) : ℕ := (Finset.univ.filter fun h => (p.1 h).1 ≠ h.1).card

/-- The relabellings keep the number of half-edges on edges between different vertices. -/
lemma crossCount_smul {m : ℕ} (g : vertexPerm m) (p : Pairing m) : crossCount (g • p) = crossCount p := by
  obtain ⟨π, hπ⟩ := g.2
  have hg : ∀ x, (g.1 x).1 = π x.1 := fun x => hπ x.1 x.2
  have key : ∀ a, (((g • p).1 a).1 ≠ a.1 ↔ (p.1 (g.1.symm a)).1 ≠ (g.1.symm a).1) := fun a => by
    change (g.1 (p.1 (g.1.symm a))).1 ≠ a.1 ↔ _
    conv_lhs => rw [show a.1 = (g.1 (g.1.symm a)).1 by rw [Equiv.apply_symm_apply]]
    rw [hg, hg, π.injective.ne_iff]
  unfold crossCount
  refine Finset.card_bij' (fun a _ => g.1.symm a) (fun a _ => g.1 a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (key a).1 ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [key, Equiv.symm_apply_apply]
    exact ha
  · intro a _; exact Equiv.apply_symm_apply _ a
  · intro a _; exact Equiv.symm_apply_apply _ a

/-- The pairing of the four half-edges at a vertex into two loops: `0 ↔ 1`, `2 ↔ 3`. -/
def loopPair : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- **The two figure-eights**: two loops at each vertex. -/
def figEights : Pairing 2 := ⟨fun h => (h.1, loopPair h.2), by unfold Function.Involutive; decide, by decide⟩

/-- **The dumbbell**: a loop at each vertex (half-edges `0 ↔ 1`) and two edges between the vertices (half-edges `2`,
`3`). -/
def dumbbell : Pairing 2 :=
  ⟨fun h => if h.2 = 0 ∨ h.2 = 1 then (h.1, loopPair h.2) else (Equiv.swap 0 1 h.1, h.2),
    by unfold Function.Involutive; decide, by decide⟩

/-- **The melon (sunset)**: four edges between the two vertices. -/
def melon : Pairing 2 := ⟨fun h => (Equiv.swap 0 1 h.1, h.2), by unfold Function.Involutive; decide, by decide⟩

/-- The stabilizer of a pairing of two vertices, in the coordinates `S₂ × (S₄)²` of `vertexPerm 2`. -/
lemma card_stabilizer_two (p : Pairing 2) :
    Nat.card (stabilizer (vertexPerm 2) p) =
      (Finset.univ.filter fun q : Equiv.Perm (Fin 2) × (Fin 2 → Equiv.Perm (Fin 4)) =>
        ∀ h, Equiv.prodShear q.1 q.2 (p.1 h) = p.1 (Equiv.prodShear q.1 q.2 h)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (((vertexPermEquiv 2).symm.subtypeEquiv fun q => ?_))).symm
  rw [mem_stabilizer_iff]
  constructor
  · intro hq
    apply Subtype.ext
    funext h
    have := hq ((Equiv.prodShear q.1 q.2).symm h)
    rw [Equiv.apply_symm_apply] at this
    change Equiv.prodShear q.1 q.2 (p.1 ((Equiv.prodShear q.1 q.2).symm h)) = p.1 h
    exact this
  · intro hq h
    have := congrFun (congrArg Subtype.val hq) (Equiv.prodShear q.1 q.2 h)
    change Equiv.prodShear q.1 q.2 (p.1 ((Equiv.prodShear q.1 q.2).symm (Equiv.prodShear q.1 q.2 h))) =
      p.1 (Equiv.prodShear q.1 q.2 h) at this
    rwa [Equiv.symm_apply_apply] at this

set_option maxRecDepth 20000 in
/-- `|Aut| = 128` for the two figure-eights. -/
lemma card_stabilizer_figEights : Nat.card (stabilizer (vertexPerm 2) figEights) = 128 := by
  rw [card_stabilizer_two]; decide

set_option maxRecDepth 20000 in
/-- `|Aut| = 16` for the dumbbell. -/
lemma card_stabilizer_dumbbell : Nat.card (stabilizer (vertexPerm 2) dumbbell) = 16 := by
  rw [card_stabilizer_two]; decide

set_option maxRecDepth 20000 in
/-- `|Aut| = 48` for the melon. -/
lemma card_stabilizer_melon : Nat.card (stabilizer (vertexPerm 2) melon) = 48 := by
  rw [card_stabilizer_two]; decide

/-- The class of a pairing of two vertices, a vacuum graph with two vertices. -/
abbrev graphTwo (p : Pairing 2) : Quotient (orbitRel (vertexPerm 2) (Pairing 2)) := Quotient.mk _ p

/-- **The vacuum graphs with two four-valent vertices** are exactly the two figure-eights, the dumbbell and the melon,
with `|Aut Γ| = 128, 16, 48` (`1/128 + 1/16 + 1/48 = 35/384`, Borinsky (3.1.8), p. 24): the three are distinct orbits
(they have `0`, `4`, `8` half-edges on edges between the vertices), and there is no other orbit, since their symmetry
factors already add up to the total `35/384` of `sum_inv_aut_two`. -/
theorem vacuum_graphs_two [Fintype (Quotient (orbitRel (vertexPerm 2) (Pairing 2)))] :
    (∀ Γ : Quotient (orbitRel (vertexPerm 2) (Pairing 2)),
      Γ = graphTwo figEights ∨ Γ = graphTwo dumbbell ∨ Γ = graphTwo melon) ∧
    graphTwo figEights ≠ graphTwo dumbbell ∧ graphTwo figEights ≠ graphTwo melon ∧
      graphTwo dumbbell ≠ graphTwo melon := by
  classical
  have hc : ∀ p q : Pairing 2, graphTwo p = graphTwo q → crossCount p = crossCount q := by
    intro p q h
    obtain ⟨g, hg⟩ := Quotient.exact h
    rw [← hg, crossCount_smul]
  have h1 : graphTwo figEights ≠ graphTwo dumbbell := fun h => absurd (hc _ _ h) (by decide)
  have h2 : graphTwo figEights ≠ graphTwo melon := fun h => absurd (hc _ _ h) (by decide)
  have h3 : graphTwo dumbbell ≠ graphTwo melon := fun h => absurd (hc _ _ h) (by decide)
  set f : Quotient (orbitRel (vertexPerm 2) (Pairing 2)) → ℚ := fun Γ => 1 / Nat.card (stabilizer (vertexPerm 2) Γ.out)
  have hout : ∀ p : Pairing 2, Nat.card (stabilizer (vertexPerm 2) (graphTwo p).out) =
      Nat.card (stabilizer (vertexPerm 2) p) := fun p => card_stabilizer_eq_of_rel (Quotient.mk_out p)
  have hS : ∑ Γ ∈ ({graphTwo figEights, graphTwo dumbbell, graphTwo melon} :
      Finset (Quotient (orbitRel (vertexPerm 2) (Pairing 2)))), f Γ = 35 / 384 := by
    rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3]), Finset.sum_singleton]
    simp only [f, hout, card_stabilizer_figEights, card_stabilizer_dumbbell, card_stabilizer_melon]
    norm_num
  have hpos : ∀ Γ, 0 < f Γ := fun Γ => by
    have : 0 < Nat.card (stabilizer (vertexPerm 2) Γ.out) := Nat.card_pos
    simp only [f]
    exact one_div_pos.2 (by exact_mod_cast this)
  have htot : ∑ Γ, f Γ = 35 / 384 := sum_inv_aut_two
  set S : Finset (Quotient (orbitRel (vertexPerm 2) (Pairing 2))) := {graphTwo figEights, graphTwo dumbbell, graphTwo melon}
  have hsplit := Finset.sum_sdiff (Finset.subset_univ S) (f := f)
  rw [htot, hS, add_eq_right] at hsplit
  have hemp : Finset.univ \ S = ∅ := by
    by_contra hne
    obtain ⟨Γ, hΓ⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => (hpos x).le).1 hsplit Γ hΓ
    exact (hpos Γ).ne' this
  refine ⟨fun Γ => ?_, h1, h2, h3⟩
  have hΓ : Γ ∈ S := Finset.sdiff_eq_empty_iff_subset.1 hemp (Finset.mem_univ Γ)
  simpa [S] using hΓ

end Lightlike.FieldTheory
