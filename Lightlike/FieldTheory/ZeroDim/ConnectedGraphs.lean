import Lightlike.FieldTheory.ZeroDim.Connected
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The connected vacuum graphs and their symmetry factors

A connected vacuum graph with `m` four-valent vertices is an orbit of the connected pairings (`ConnPairing m`) under
the vertex-preserving permutations `S₄ ≀ S_m`; connectedness is invariant under relabelling (`connOn_smul`), and the
class formula gives `∑_{Γ connected} 1/|Aut Γ| = c_m/(24^m m!)` (`sum_inv_aut_connected`), the coefficient of `xᵐ`
in `W` (`coeff_connectedSeries`), just as `∑_Γ 1/|Aut Γ| = a_m/(24^m m!)` is the coefficient of `xᵐ` in `Z`
(`coeff_vacuumSeries`). With `vacuumSeries_eq_exp` this is Borinsky's `X = e^{X_c}` (Theorem 2.4.1, p. 18) for the
vacuum graphs of the quartic theory, read through the number of vertices, and `logOf_vacuumSeries`,
`coeff_logOf_vacuumSeries` give its other form `X_c = log X`: the coefficients of `log Z` are the sums of `1/|Aut Γ|`
over the connected graphs.

Trust checks (`numConnected_one`, `numConnected_two`, `sum_inv_aut_connected_two`): `c₁ = 3` (the figure-eight),
`c₂ = 96`, and the connected graphs with two vertices have total symmetry factor `1/12 = 1/16 + 1/48`, so the
disconnected one (two figure-eights) has `35/384 - 1/12 = 1/128 = (1/8)²/2`.
-/

open Finset MulAction

noncomputable section

open scoped Classical

namespace Lightlike.FieldTheory

section Relabel

variable {V : Type*} [Fintype V] (σ : Equiv.Perm (V × Fin 4)) (π : Equiv.Perm V)
  (hσ : ∀ x, (σ x).1 = π x.1)
include hσ

lemma symm_fst_of_fst (h : V × Fin 4) : (σ.symm h).1 = π.symm h.1 := by
  have := hσ (σ.symm h)
  rw [Equiv.apply_symm_apply] at this
  rw [this, Equiv.symm_apply_apply]

lemma closed_conj (f : V × Fin 4 → V × Fin 4) (T : Finset V) :
    Closed (σ ∘ f ∘ σ.symm) T ↔ Closed f (T.map π.symm.toEmbedding) := by
  simp only [Closed, Function.comp_apply, mem_map_equiv, Equiv.symm_symm, hσ]
  constructor
  · intro hT a ha
    have := hT (σ a) (by rw [hσ]; exact ha)
    rwa [Equiv.symm_apply_apply] at this
  · intro hT h hh
    apply hT
    rw [symm_fst_of_fst σ π hσ, Equiv.apply_symm_apply]
    exact hh

/-- Relabelling the vertices does not change connectedness. -/
lemma connOn_conj (f : V × Fin 4 → V × Fin 4) : ConnOn (σ ∘ f ∘ σ.symm) univ ↔ ConnOn f univ := by
  have hmap : ∀ T : Finset V, (T.map π.toEmbedding).map π.symm.toEmbedding = T := fun T => by
    ext x; simp [mem_map_equiv]
  have hmap' : ∀ T : Finset V, (T.map π.symm.toEmbedding).map π.toEmbedding = T := fun T => by
    ext x; simp [mem_map_equiv]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun T _ hT => ?_⟩
    have hT' : Closed (σ ∘ f ∘ σ.symm) (T.map π.toEmbedding) := by
      rw [closed_conj σ π hσ, hmap]; exact hT
    rcases hc _ (subset_univ _) hT' with h | h
    · left; rw [← hmap T, h, map_empty]
    · right; rw [← hmap T, h, map_univ_equiv]
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun T _ hT => ?_⟩
    rw [closed_conj σ π hσ] at hT
    rcases hc _ (subset_univ _) hT with h | h
    · left; rw [← hmap' T, h, map_empty]
    · right; rw [← hmap' T, h, map_univ_equiv]

end Relabel

/-- The **connected pairings** of `m` four-valent vertices: the connected vacuum graphs as labelled objects. -/
def ConnPairing (m : ℕ) : Type := {f : Pairing m // ConnOn f.1 univ}

instance (m : ℕ) : Finite (ConnPairing m) := by unfold ConnPairing; infer_instance

lemma vertexPerm_fst {m : ℕ} (g : vertexPerm m) (x : Fin m × Fin 4) :
    (g.1 x).1 = (Classical.choose g.2) x.1 :=
  Classical.choose_spec g.2 x.1 x.2

/-- Connectedness is invariant under the vertex-preserving permutations. -/
lemma connOn_smul {m : ℕ} (g : vertexPerm m) (f : Pairing m) :
    ConnOn (g • f).1 univ ↔ ConnOn f.1 univ :=
  connOn_conj g.1 (Classical.choose g.2) (vertexPerm_fst g) f.1

/-- The vertex-preserving permutations act on the connected pairings. -/
instance (m : ℕ) : MulAction (vertexPerm m) (ConnPairing m) where
  smul g f := ⟨g • f.1, (connOn_smul g f.1).2 f.2⟩
  one_smul f := Subtype.ext (one_smul _ f.1)
  mul_smul g k f := Subtype.ext (mul_smul g k f.1)

/-- The automorphism group of a connected graph is its automorphism group as a graph. -/
lemma stabilizer_connPairing {m : ℕ} (f : ConnPairing m) :
    stabilizer (vertexPerm m) f = stabilizer (vertexPerm m) f.1 := by
  ext g
  simp only [mem_stabilizer_iff]
  exact Subtype.ext_iff

lemma card_connPairing (m : ℕ) : Nat.card (ConnPairing m) = numConnected m := by
  have e : ConnPairing m ≃ ↥(connPairOn (univ : Finset (Fin m))) :=
    { toFun := fun f => ⟨f.1.1, by
        rw [connPairOn, mem_filter, mem_pairOn]
        exact ⟨⟨f.1.2.1, fun h => by simp [f.1.2.2 h]⟩, f.2⟩⟩
      invFun := fun F => ⟨⟨F.1, (mem_pairOn.1 (mem_filter.1 F.2).1).1,
        fun h hh => ((mem_pairOn.1 (mem_filter.1 F.2).1).2 h).1 hh (mem_univ _)⟩, (mem_filter.1 F.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_finsetCard]
  rfl

/-- **The connected vacuum graphs with their symmetry factors**: summed over the connected graphs (orbits of
connected pairings) with `m` vertices, `∑ 1/|Aut Γ| = c_m/(24^m m!)`. -/
theorem sum_inv_aut_connected (m : ℕ)
    [Fintype (Quotient (orbitRel (vertexPerm m) (ConnPairing m)))] :
    ∑ Γ : Quotient (orbitRel (vertexPerm m) (ConnPairing m)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm m) Γ.out) =
      (numConnected m : ℚ) / (24 ^ m * m.factorial) := by
  rw [sum_inv_card_stabilizer, card_connPairing, card_vertexPerm]
  push_cast
  ring

open PowerSeries

/-- The coefficient of `xᵐ` in `Z` is the sum of `1/|Aut Γ|` over the vacuum graphs with `m` vertices. -/
theorem coeff_vacuumSeries (m : ℕ) [Fintype (Quotient (orbitRel (vertexPerm m) (Pairing m)))] :
    coeff m vacuumSeries = ∑ Γ : Quotient (orbitRel (vertexPerm m) (Pairing m)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm m) Γ.out) := by
  rw [sum_inv_aut, vacuumSeries, coeff_mk, numPairings_eq]

/-- The coefficient of `xᵐ` in `W` is the sum of `1/|Aut Γ|` over the connected vacuum graphs with `m` vertices. -/
theorem coeff_connectedSeries (m : ℕ) [Fintype (Quotient (orbitRel (vertexPerm m) (ConnPairing m)))] :
    coeff m connectedSeries = ∑ Γ : Quotient (orbitRel (vertexPerm m) (ConnPairing m)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm m) Γ.out) := by
  rw [sum_inv_aut_connected, connectedSeries, coeff_mk]

lemma constantCoeff_connectedSeries : constantCoeff connectedSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, connectedSeries, coeff_mk, numConnected_zero]; simp

/-- **`log Z = W`** (Borinsky, Theorem 2.4.1, eq. (2.4.7), p. 18: `X_c = log X`), with Mathlib's formal logarithm
`logOf f = log(1 + X) ∘ (f - 1)`. -/
theorem logOf_vacuumSeries : logOf vacuumSeries = connectedSeries := by
  have hW : HasSubst connectedSeries := HasSubst.of_constantCoeff_zero' constantCoeff_connectedSeries
  have he : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  have h1 : vacuumSeries - 1 = (exp ℚ - 1).subst connectedSeries := by
    rw [subst_sub hW, vacuumSeries_eq_exp]
    congr 1
    rw [← coe_substAlgHom hW, map_one]
  rw [logOf_eq, h1, ← subst_comp_subst_apply he hW, subst_log_exp_sub_one, subst_X hW]

/-- **`log Z` is the sum over the connected graphs**: the coefficient of `xᵐ` in `log Z` is the sum of `1/|Aut Γ|`
over the connected vacuum graphs with `m` vertices. -/
theorem coeff_logOf_vacuumSeries (m : ℕ) [Fintype (Quotient (orbitRel (vertexPerm m) (ConnPairing m)))] :
    coeff m (logOf vacuumSeries) = ∑ Γ : Quotient (orbitRel (vertexPerm m) (ConnPairing m)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm m) Γ.out) := by
  rw [logOf_vacuumSeries, coeff_connectedSeries]

/-- **Trust check**: the three pairings of one vertex are all connected (the figure-eight). -/
theorem numConnected_one : numConnected 1 = 3 := by
  have h := numPairings_succ 0
  simp only [zero_add, range_one, sum_singleton, Nat.choose_self, one_mul, Nat.sub_self,
    numPairings_zero, mul_one] at h
  rw [← h, numPairings_eq]
  rfl

/-- **Trust check**: `c₂ = 105 - 3 · 3 = 96` connected pairings of two vertices. -/
theorem numConnected_two : numConnected 2 = 96 := by
  have h := numPairings_succ 1
  norm_num [Finset.sum_range_succ, numConnected_one, numPairings_eq, Nat.doubleFactorial] at h
  omega

/-- **Trust check, order `g²`**: the connected vacuum graphs with two vertices (`1/16` and `1/48`) have total
symmetry factor `1/12`; the remaining `35/384 - 1/12 = 1/128` is the disconnected pair of figure-eights. -/
theorem sum_inv_aut_connected_two [Fintype (Quotient (orbitRel (vertexPerm 2) (ConnPairing 2)))] :
    ∑ Γ : Quotient (orbitRel (vertexPerm 2) (ConnPairing 2)),
      (1 : ℚ) / Nat.card (stabilizer (vertexPerm 2) Γ.out) = 1 / 12 := by
  rw [sum_inv_aut_connected, numConnected_two]
  norm_num [Nat.factorial]

end Lightlike.FieldTheory
