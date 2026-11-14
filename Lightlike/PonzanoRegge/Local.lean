module

public import Lightlike.PonzanoRegge.BiedenharnElliott

/-!
# Ponzano–Regge weights and the local 2-3 Pachner move

Spins are **doubled** (`J = 2j ∈ ℕ`), as in Physlib. A *colouring* assigns a doubled spin to
every finite set of vertices; only its values on edges (2-element sets) are ever used.

## Weights (Barrett–Naish-Guzman convention)

* edge `e`: `(2j+1)(-1)^{2j}` = `edgeW J = (J+1)(-1)^J`;
* triangle `uvw`: `(-1)^{j_uv + j_vw + j_wu}` = `triSign col u v w`;
* tetrahedron `p₀p₁p₂p₃`: its 6j symbol, `tetAmp col p`. The triads are the four faces and the
  columns pair opposite edges. It is built on Physlib's `sixJSymEdge`, which indexes the six spins
  by the edges of the *dual* tetrahedron (dual vertex `i` = face opposite `pᵢ`, so the dual edge
  `{i,k}` carries the spin of the opposite original edge, `dualCol`). Physlib's 24-fold
  tetrahedral symmetry (`sixJSymEdge_comp_map`) then makes `tetAmp` independent of how the four
  vertices are enumerated (`tetAmp_comp_perm`).

## Main result

`pachner23_local`: for five distinct vertices `A B C D E` and any colouring,

  `triSign(ABC) · {ABCD} · {ABCE} = Σ_x edgeW(x) · triSign(ADE) triSign(BDE) triSign(CDE) ·
     {ABDE} {BCDE} {CADE}`,

where on the right the new edge `DE` carries spin `x`, summed over its whole range (larger `x`
violate the triangle inequality in `ADE`, `pachner23_term_eq_zero`). **Hypothesis:**
`BiedenharnElliott` (stated in `BiedenharnElliott.lean`, proven for all spins as
`Lightlike.Pentagon.biedenharnElliott`; `Unconditional.lean` discharges the hypothesis). The dictionary
from the Biedenharn–Elliott letters to the edges is `p q r = AB BC CA`, `a d e = AD BD CD`,
`b c f = AE BE CE`, `x = DE`. Independent numerical check of this identity, without the
dictionary (SymPy, exact arithmetic): `scripts/pr23_check.py`.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A colouring by doubled spins. Only values on 2-element vertex sets (edges) matter. -/
abbrev Colouring (V : Type*) := Finset V → ℕ

/-- Edge weight `(2j+1)(-1)^{2j}`, in doubled units. -/
noncomputable def edgeW (J : ℕ) : ℝ := ((J : ℝ) + 1) * (-1) ^ J

/-- Triangle weight `(-1)^{j_uv + j_vw + j_wu}`, in doubled units: `(-1)` to the natural-number
quotient `(J_uv + J_vw + J_wu) / 2`, which rounds down for an odd doubled perimeter. The rounding
is never seen: in a tetrahedron with an odd-perimeter face the 6j symbol vanishes
(`tetAmp_eq_zero_of_odd`, from `sixJSym_eq_zero_of_odd`, in `Parity.lean`), so `weight` and
`amplitude` do not change if the triangle weight is replaced by any other value on odd-perimeter
triangles (`weightWith_eq_weight`, `amplitudeWith_eq_amplitude`). -/
def triSign (col : Colouring V) (u v w : V) : ℝ :=
  (-1) ^ ((col {u, v} + col {v, w} + col {w, u}) / 2)

/-- The dual-edge labelling of the tetrahedron `p`: dual edge `{i, k}` carries the spin of the
original edge opposite to it, spanned by the other two vertices. -/
def dualCol (col : Colouring V) (p : Fin 4 → V) : Sym2 (Fin 4) → ℕ :=
  Sym2.lift ⟨fun i k => col ((univ \ {i, k}).image p), fun i k => by dsimp only; rw [pair_comm]⟩

/-- The 6j symbol of the tetrahedron with vertices `p 0, p 1, p 2, p 3`. -/
noncomputable def tetAmp (col : Colouring V) (p : Fin 4 → V) : ℝ := sixJSymEdge (dualCol col p)

lemma image_compl_perm (σ : Equiv.Perm (Fin 4)) (i k : Fin 4) :
    (univ \ {i, k}).image σ = univ \ {σ i, σ k} := by
  ext m
  simp only [mem_image, mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [σ.injective.eq_iff] using hl
  · intro hm
    exact ⟨σ.symm m, by simpa [Equiv.symm_apply_eq] using hm, σ.apply_symm_apply m⟩

lemma dualCol_comp_perm (col : Colouring V) (p : Fin 4 → V) (σ : Equiv.Perm (Fin 4)) :
    dualCol col (p ∘ σ) = dualCol col p ∘ Sym2.map σ := by
  funext e
  induction e using Sym2.ind with
  | _ i k =>
    simp only [dualCol, Function.comp_apply, Sym2.map_mk, Sym2.lift_mk]
    rw [← image_compl_perm, image_image]

/-- **Independence of the enumeration.** Re-ordering the vertices does not change `tetAmp`
(Physlib's 24-fold tetrahedral symmetry of the 6j symbol). -/
theorem tetAmp_comp_perm (col : Colouring V) (p : Fin 4 → V) (σ : Equiv.Perm (Fin 4)) :
    tetAmp col (p ∘ σ) = tetAmp col p := by
  rw [tetAmp, dualCol_comp_perm, sixJSymEdge_comp_map, tetAmp]

/-- `tetAmp` in the standard `{j₁ j₂ j₃; j₄ j₅ j₆}` arrangement: top row = face `p₁p₂p₃`,
columns = opposite edges. -/
theorem tetAmp_eq (col : Colouring V) (p : Fin 4 → V) :
    tetAmp col p = sixJSym (col {p 2, p 3}) (col {p 1, p 3}) (col {p 1, p 2}) (col {p 0, p 1})
      (col {p 0, p 2}) (col {p 0, p 3}) := by
  have h : ∀ i k : Fin 4, ∀ l m : Fin 4, (univ \ {i, k} : Finset (Fin 4)) = {l, m} →
      dualCol col p s(i, k) = col {p l, p m} := by
    intro i k l m h
    simp only [dualCol, Sym2.lift_mk, h, image_insert, image_singleton]
  rw [tetAmp, sixJSymEdge, h 0 1 2 3 (by decide), h 0 2 1 3 (by decide), h 0 3 1 2 (by decide),
    h 2 3 0 1 (by decide), h 1 3 0 2 (by decide), h 1 2 0 3 (by decide)]

/-- `tetAmp` only depends on the colouring of the six edges of the tetrahedron. -/
lemma tetAmp_congr {col col' : Colouring V} {p : Fin 4 → V}
    (h : ∀ i k, i ≠ k → col {p i, p k} = col' {p i, p k}) : tetAmp col p = tetAmp col' p := by
  rw [tetAmp_eq, tetAmp_eq, h 2 3 (by decide), h 1 3 (by decide), h 1 2 (by decide),
    h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide)]

/-- Any two injective enumerations of the same four vertices give the same 6j symbol. -/
lemma tetAmp_reindex (col : Colouring V) {p q : Fin 4 → V} (hq : Function.Injective q)
    (h : ∀ i, ∃ k, q i = p k) : tetAmp col q = tetAmp col p := by
  choose σ hσ using h
  have hinj : Function.Injective σ := fun i j hij => hq (by rw [hσ, hσ, hij])
  have hbij := Finite.injective_iff_bijective.mp hinj
  rw [show q = p ∘ Equiv.ofBijective σ hbij from funext hσ, tetAmp_comp_perm]

omit [DecidableEq V] in
lemma injective_vec4 {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
    first | exact absurd h ‹_› | exact absurd h.symm ‹_›

/-- An edge with an endpoint outside `{D, E}` is not the edge `DE`. -/
lemma pair_ne_of_not_mem {u v D E : V} (hD : u ≠ D) (hE : u ≠ E) :
    ({u, v} : Finset V) ≠ {D, E} := by
  intro h
  have : u ∈ ({D, E} : Finset V) := h ▸ mem_insert_self u {v}
  simp only [mem_insert, mem_singleton] at this
  tauto

/-- `(-1)^m = (-1)^n` when `m ≡ n (mod 2)`. -/
lemma neg_one_pow_congr {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div n 2, pow_add, pow_add, pow_mul, pow_mul, h]
  simp

/-- The single instance of Biedenharn–Elliott that the 2-3 move needs for the colouring `col`
(letters: `a d e = AD BD CD`, `b c f = AE BE CE`, `p q r = AB BC CA`). -/
def BEAt (col : Colouring V) (A B C D E : V) : Prop :=
  beLHS (col {A, D}) (col {A, E}) (col {B, E}) (col {B, D}) (col {C, D}) (col {C, E})
      (col {A, B}) (col {B, C}) (col {C, A}) =
    beRHS (col {A, D}) (col {A, E}) (col {B, E}) (col {B, D}) (col {C, D}) (col {C, E})
      (col {A, B}) (col {B, C}) (col {C, A})

lemma beAt_of_biedenharnElliott (hBE : BiedenharnElliott) (col : Colouring V) (A B C D E : V) :
    BEAt col A B C D E := hBE _ _ _ _ _ _ _ _ _

/-- **The local 2-3 Pachner move**, assuming the instance `BEAt col A B C D E` of the
Biedenharn–Elliott identity (which follows from `BiedenharnElliott`, `beAt_of_biedenharnElliott`). -/
theorem pachner23_local (col : Colouring V) {A B C D E : V} (hBE : BEAt col A B C D E)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E) (hBC : B ≠ C) (hBD : B ≠ D)
    (hBE' : B ≠ E) (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) :
    triSign col A B C * (tetAmp col ![A, B, C, D] * tetAmp col ![A, B, C, E]) =
      ∑ x ∈ range (col {A, D} + col {A, E} + 1),
        edgeW x * (triSign (Function.update col {D, E} x) A D E *
          triSign (Function.update col {D, E} x) B D E *
          triSign (Function.update col {D, E} x) C D E) *
        (tetAmp (Function.update col {D, E} x) ![A, B, D, E] *
          tetAmp (Function.update col {D, E} x) ![B, C, D, E] *
          tetAmp (Function.update col {D, E} x) ![C, A, D, E]) := by
  have hu : ∀ (x : ℕ) {u : V} (v : V), u ≠ D → u ≠ E →
      Function.update col {D, E} x {u, v} = col {u, v} :=
    fun x u v h1 h2 => Function.update_of_ne (pair_ne_of_not_mem h1 h2) _ _
  have hx : ∀ x : ℕ, Function.update col {D, E} x {D, E} = x :=
    fun x => Function.update_self _ _ _
  -- the five 6j symbols in Biedenharn–Elliott's arrangement
  have t1 : tetAmp col ![A, B, C, D] = sixJSym (col {A, B}) (col {B, C}) (col {C, A})
      (col {C, D}) (col {A, D}) (col {B, D}) := by
    rw [← tetAmp_reindex col (q := ![D, C, A, B])
      (injective_vec4 hCD.symm hAD.symm hBD.symm hAC.symm hBC.symm hAB)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩]), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm C B, pair_comm D C, pair_comm D A, pair_comm D B]
  have t2 : tetAmp col ![A, B, C, E] = sixJSym (col {A, B}) (col {B, C}) (col {C, A})
      (col {C, E}) (col {A, E}) (col {B, E}) := by
    rw [← tetAmp_reindex col (q := ![E, C, A, B])
      (injective_vec4 hCE.symm hAE.symm hBE'.symm hAC.symm hBC.symm hAB)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩]), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm C B, pair_comm E C, pair_comm E A, pair_comm E B]
  have t3 : ∀ x, tetAmp (Function.update col {D, E} x) ![A, B, D, E] =
      sixJSym (col {A, D}) (col {A, E}) x (col {B, E}) (col {B, D}) (col {A, B}) := by
    intro x
    rw [← tetAmp_reindex _ (q := ![B, E, D, A])
      (injective_vec4 hBE' hBD hAB.symm hDE.symm hAE.symm hAD.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩]), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm D A, pair_comm E A, pair_comm E D, pair_comm B A, hx, hu x D hAD hAE,
      hu x E hAD hAE, hu x E hBD hBE', hu x D hBD hBE', hu x B hAD hAE]
  have t4 : ∀ x, tetAmp (Function.update col {D, E} x) ![B, C, D, E] =
      sixJSym (col {B, E}) (col {B, D}) x (col {C, D}) (col {C, E}) (col {B, C}) := by
    intro x
    rw [← tetAmp_reindex _ (q := ![C, D, E, B])
      (injective_vec4 hCD hCE hBC.symm hDE hBD.symm hBE'.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩]), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm E B, pair_comm D B, pair_comm C B, hx, hu x E hBD hBE', hu x D hBD hBE',
      hu x D hCD hCE, hu x E hCD hCE, hu x C hBD hBE']
  have t5 : ∀ x, tetAmp (Function.update col {D, E} x) ![C, A, D, E] =
      sixJSym (col {C, D}) (col {C, E}) x (col {A, E}) (col {A, D}) (col {C, A}) := by
    intro x
    rw [← tetAmp_reindex _ (q := ![A, E, D, C])
      (injective_vec4 hAE hAD hAC hDE.symm hCE.symm hCD.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩]), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm D C, pair_comm E C, pair_comm E D, pair_comm A C, hx, hu x D hCD hCE,
      hu x E hCD hCE, hu x E hAD hAE, hu x D hAD hAE, hu x A hCD hCE]
  have sA : ∀ x, triSign (Function.update col {D, E} x) A D E =
      (-1) ^ ((col {A, D} + x + col {A, E}) / 2) := by
    intro x; rw [triSign, pair_comm E A, hx, hu x D hAD hAE, hu x E hAD hAE]
  have sB : ∀ x, triSign (Function.update col {D, E} x) B D E =
      (-1) ^ ((col {B, D} + x + col {B, E}) / 2) := by
    intro x; rw [triSign, pair_comm E B, hx, hu x D hBD hBE', hu x E hBD hBE']
  have sC : ∀ x, triSign (Function.update col {D, E} x) C D E =
      (-1) ^ ((col {C, D} + x + col {C, E}) / 2) := by
    intro x; rw [triSign, pair_comm E C, hx, hu x D hCD hCE, hu x E hCD hCE]
  simp only [t1, t2, t3, t4, t5, sA, sB, sC]
  rw [triSign]
  -- name the nine fixed spins with Biedenharn–Elliott's letters
  unfold BEAt at hBE
  generalize col {A, D} = a at hBE ⊢
  generalize col {A, E} = b at hBE ⊢
  generalize col {B, E} = c at hBE ⊢
  generalize col {B, D} = d at hBE ⊢
  generalize col {C, D} = e at hBE ⊢
  generalize col {C, E} = f at hBE ⊢
  generalize col {A, B} = p at hBE ⊢
  generalize col {B, C} = q at hBE ⊢
  generalize col {C, A} = r at hBE ⊢
  have hbe := hBE
  simp only [beLHS, beRHS] at hbe
  rw [← hbe, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hz : sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r = 0
  · rw [hz]; ring
  have h3 := triads_of_sixJSym_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have h4 := triads_of_sixJSym_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have h5 := triads_of_sixJSym_ne_zero (right_ne_zero_of_mul hz)
  have hsign : (-1 : ℝ) ^ ((p + q + r) / 2) * (-1) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) =
      (-1) ^ x * ((-1) ^ ((a + x + b) / 2) * (-1) ^ ((d + x + c) / 2) *
        (-1) ^ ((e + x + f) / 2)) := by
    simp only [← pow_add]
    exact neg_one_pow_congr (by omega)
  rw [edgeW]
  linear_combination ((x : ℝ) + 1) *
    (sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r) * hsign

end Lightlike.PR
