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

end Lightlike.FieldTheory
