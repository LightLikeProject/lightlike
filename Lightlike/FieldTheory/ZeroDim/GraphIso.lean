import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Rat

/-!
# Labelled graphs, isomorphism classes and automorphisms

Borinsky, *Graphs in perturbation theory*, arXiv:1807.02046v1, §2.1, p. 10-11: a graph is a set `H` of half-edges, a
set `V` of vertices, an attachment map `ν : H → V` and an involution `ι` of `H` (Definitions 2.1.1-2.1.2); an
isomorphism `Γ → Γ'` is a pair of bijections `j_H : H → H'`, `j_V : V → V'` with `ν' ∘ j_H = j_V ∘ ν` and
`ι' ∘ j_H = j_H ∘ ι` (Definition 2.1.6), and an automorphism is an isomorphism `Γ → Γ` (Definition 2.1.7).

Here a labelled graph with `n` half-edges and `k` vertices is `LGraph n k` (`H = Fin n`, `V = Fin k`); the pairs
`(j_H, j_V) ∈ S_n × S_k` act by relabelling (`(σ, τ) • Γ = (τ ∘ ν ∘ σ⁻¹, σ ∘ ι ∘ σ⁻¹)`), so that `(σ, τ)` is an
isomorphism `Γ → (σ, τ) • Γ` (`relabel_isIso`); the isomorphism classes are the orbits, the automorphism group is the
stabilizer, and `card_orbit_mul_card_aut`: `|orbit Γ| · |Aut Γ| = n! k!`, i.e. `1/|Aut Γ| = |orbit Γ|/(n! k!)`.
-/

open Function MulAction

namespace Lightlike.FieldTheory.GraphAlg

/-- A **labelled graph** with half-edges `Fin n` and vertices `Fin k`: the attachment map and the involution of the
half-edges (edges are its 2-cycles, legs its fixed points). -/
@[ext]
structure LGraph (n k : ℕ) where
  /-- The attachment map `ν`. -/
  att : Fin n → Fin k
  /-- The involution `ι`. -/
  inv : Fin n → Fin n
  /-- `ι` is an involution. -/
  invol : Involutive inv

variable {n k : ℕ}

/-- `LGraph n k` as a subtype. -/
def equivSubtype : LGraph n k ≃ {p : (Fin n → Fin k) × (Fin n → Fin n) // Involutive p.2} where
  toFun Γ := ⟨(Γ.att, Γ.inv), Γ.invol⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite (LGraph n k) := Finite.of_equiv _ equivSubtype.symm

/-- A pair of bijections `(j_H, j_V)` is an **isomorphism** `Γ → Γ'` (Borinsky Definition 2.1.6). -/
def IsIso (Γ Γ' : LGraph n k) (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  Γ'.att ∘ σ = τ ∘ Γ.att ∧ Γ'.inv ∘ σ = σ ∘ Γ.inv

/-- The relabelling action of `S_n × S_k`: `(σ, τ) • Γ = (τ ∘ ν ∘ σ⁻¹, σ ∘ ι ∘ σ⁻¹)`. -/
instance : MulAction (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (LGraph n k) where
  smul g Γ := ⟨g.2 ∘ Γ.att ∘ g.1.symm, g.1 ∘ Γ.inv ∘ g.1.symm, fun h => by
    simp only [comp_apply, Equiv.symm_apply_apply, Γ.invol (g.1.symm h), Equiv.apply_symm_apply]⟩
  one_smul _ := by ext <;> rfl
  mul_smul _ _ _ := by ext <;> rfl

lemma smul_att (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) :
    (g • Γ).att = g.2 ∘ Γ.att ∘ g.1.symm := rfl

lemma smul_inv (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) :
    (g • Γ).inv = g.1 ∘ Γ.inv ∘ g.1.symm := rfl

/-- The relabelling by `(σ, τ)` is an isomorphism `Γ → (σ, τ) • Γ`. -/
lemma relabel_isIso (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) : IsIso Γ (g • Γ) g.1 g.2 := by
  constructor <;> funext h <;> simp [smul_att, smul_inv]

/-- **Isomorphic graphs are the same orbit**: `Γ'` is isomorphic to `Γ` iff it is a relabelling of `Γ`. -/
theorem isIso_iff_smul (Γ Γ' : LGraph n k) :
    (∃ σ τ, IsIso Γ Γ' σ τ) ↔ ∃ g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k), g • Γ = Γ' := by
  constructor
  · rintro ⟨σ, τ, h1, h2⟩
    refine ⟨(σ, τ), LGraph.ext (funext fun h => ?_) (funext fun h => ?_)⟩
    · show τ (Γ.att (σ.symm h)) = Γ'.att h
      have := congrFun h1 (σ.symm h); simp at this; exact this.symm
    · show σ (Γ.inv (σ.symm h)) = Γ'.inv h
      have := congrFun h2 (σ.symm h); simp at this; exact this.symm
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2, relabel_isIso g Γ⟩

/-- The automorphisms of `Γ` (Borinsky Definition 2.1.7) are the stabilizer of the relabelling action. -/
theorem mem_aut_iff (Γ : LGraph n k) (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) :
    g ∈ stabilizer (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ ↔ IsIso Γ Γ g.1 g.2 := by
  rw [mem_stabilizer_iff]
  constructor
  · intro h
    have := relabel_isIso g Γ
    rwa [h] at this
  · intro h
    refine LGraph.ext (funext fun x => ?_) (funext fun x => ?_)
    · show g.2 (Γ.att (g.1.symm x)) = Γ.att x
      have := congrFun h.1 (g.1.symm x); simp at this; exact this.symm
    · show g.1 (Γ.inv (g.1.symm x)) = Γ.inv x
      have := congrFun h.2 (g.1.symm x); simp at this; exact this.symm

/-- **Orbit-stabilizer for graphs**: `|orbit Γ| · |Aut Γ| = n! k!`. -/
theorem card_orbit_mul_card_aut (Γ : LGraph n k) :
    Nat.card (orbit (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) *
      Nat.card (stabilizer (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) = n.factorial * k.factorial := by
  rw [mul_comm, Nat.card_coe_set_eq, ← index_stabilizer, Subgroup.card_mul_index, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- `1/|Aut Γ| = |orbit Γ|/(n! k!)`: the symmetry factor is the number of labelled copies over `n! k!`. -/
theorem inv_card_aut (Γ : LGraph n k) :
    (1 : ℚ) / Nat.card (stabilizer (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) =
      Nat.card (orbit (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) / (n.factorial * k.factorial) := by
  have key : (Nat.card (orbit (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) : ℚ) *
      Nat.card (stabilizer (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) = n.factorial * k.factorial := by
    exact_mod_cast card_orbit_mul_card_aut Γ
  haveI : Nonempty (orbit (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) := ⟨⟨Γ, mem_orbit_self Γ⟩⟩
  have ho : (0 : ℚ) < Nat.card (orbit (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) := by
    exact_mod_cast Nat.card_pos
  have hs : (0 : ℚ) < Nat.card (stabilizer (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) Γ) := by
    exact_mod_cast Nat.card_pos
  rw [← key]
  first
    | (rw [div_mul_eq_div_div, div_self ho.ne'])
    | field_simp

end Lightlike.FieldTheory.GraphAlg
