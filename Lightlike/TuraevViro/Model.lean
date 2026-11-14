import Lightlike.PonzanoRegge.GaugeFixed
import Lightlike.TuraevViro.QNumber

/-!
# State sums from a 6j model on a finite set of colours

The Ponzano–Regge proofs of the 2-3 and 1-4 moves use only a few properties of the 6j symbol and
the edge dimension. This file abstracts them, so that the same arguments give the Turaev–Viro
invariant (quantum 6j symbols at a root of unity, `TuraevViro.lean`).

A `Model` has:
* colours `0, …, N - 1` (doubled spins);
* a 6j function `f` in the standard arrangement, with the three generating tetrahedral
  symmetries, vanishing unless all four triads are admissible (`ok`);
* a dimension `dim`; the edge weight is `dim J · (-1)^J`.

The identities the moves need are **hypotheses**, stated as `Prop`s:
* `M.BE`: Biedenharn–Elliott, summed over the colours (gives the 2-3 move);
* `M.Orth`: diagonal orthogonality (with `M.Count`, gives the 1-4 move);
* `M.Count`: the fusion count `Σ_{b adm} dim b = dim p · dim d`.

Main results:
* `Model.pachner23_local` and `Model.pachner14_local`: the local moves.
* `Model.Z_move23` and `Model.Z_move14`: the normalised state sum
  `Z K = W⁻ⁿ Σ_colourings weight`, with `n` the number of vertices and `W = Σ_d dim(d)²`, is
  invariant under both moves.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- A 6j model on the colours `0, …, N - 1`. -/
structure Model where
  /-- Number of colours. -/
  N : ℕ
  /-- The 6j symbol `{j₁ j₂ j₃; j₄ j₅ j₆}`; triads `(123)(156)(426)(453)`. -/
  f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  /-- The dimension of a colour. -/
  dim : ℕ → ℝ
  /-- Admissible triads. -/
  ok : ℕ → ℕ → ℕ → Prop
  okDec : ∀ a b c, Decidable (ok a b c)
  ok_tri : ∀ {a b c}, ok a b c → Tri a b c
  ok_swap12 : ∀ {a b c}, ok a b c → ok b a c
  ok_swap23 : ∀ {a b c}, ok a b c → ok a c b
  ok_lt : ∀ {a b c}, ok a b c → a < N
  f_ok : ∀ {j₁ j₂ j₃ j₄ j₅ j₆}, f j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0 →
    ok j₁ j₂ j₃ ∧ ok j₁ j₅ j₆ ∧ ok j₄ j₂ j₆ ∧ ok j₄ j₅ j₃
  swap12 : ∀ j₁ j₂ j₃ j₄ j₅ j₆, f j₂ j₁ j₃ j₅ j₄ j₆ = f j₁ j₂ j₃ j₄ j₅ j₆
  swap23 : ∀ j₁ j₂ j₃ j₄ j₅ j₆, f j₁ j₃ j₂ j₄ j₆ j₅ = f j₁ j₂ j₃ j₄ j₅ j₆
  flip12 : ∀ j₁ j₂ j₃ j₄ j₅ j₆, f j₄ j₅ j₃ j₁ j₂ j₆ = f j₁ j₂ j₃ j₄ j₅ j₆

attribute [instance] Model.okDec

namespace Model

variable (M : Model)

/-! ## Tetrahedral symmetry -/

/-- The 6j symbol indexed by the edges of the dual tetrahedron (as Physlib's `sixJSymEdge`). -/
noncomputable def edgeF (j : Sym2 (Fin 4) → ℕ) : ℝ :=
  M.f (j s(0, 1)) (j s(0, 2)) (j s(0, 3)) (j s(2, 3)) (j s(1, 3)) (j s(1, 2))

lemma edgeF_swap₁₂ (j : Sym2 (Fin 4) → ℕ) :
    M.edgeF (j ∘ Sym2.map (Equiv.swap 1 2)) = M.edgeF j := by
  simp only [edgeF, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 1) = s(0, 2) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 2) = s(0, 1) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 3) = s(0, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(2, 3) = s(1, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(1, 3) = s(2, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(1, 2) = s(1, 2) by decide]
  exact M.swap12 ..

lemma edgeF_swap₂₃ (j : Sym2 (Fin 4) → ℕ) :
    M.edgeF (j ∘ Sym2.map (Equiv.swap 2 3)) = M.edgeF j := by
  simp only [edgeF, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 1) = s(0, 1) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 2) = s(0, 3) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 3) = s(0, 2) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(2, 3) = s(2, 3) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(1, 3) = s(1, 2) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(1, 2) = s(1, 3) by decide]
  exact M.swap23 ..

lemma edgeF_flip (j : Sym2 (Fin 4) → ℕ) :
    M.edgeF (j ∘ Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) = M.edgeF j := by
  simp only [edgeF, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 1) = s(2, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 2) = s(1, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 3) = s(0, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(2, 3) = s(0, 1) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(1, 3) = s(0, 2) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(1, 2) = s(1, 2) by
      decide]
  exact M.flip12 ..

lemma edgeF_comp_map_mul {σ τ : Equiv.Perm (Fin 4)}
    (hσ : ∀ j, M.edgeF (j ∘ Sym2.map σ) = M.edgeF j)
    (hτ : ∀ j, M.edgeF (j ∘ Sym2.map τ) = M.edgeF j) (j : Sym2 (Fin 4) → ℕ) :
    M.edgeF (j ∘ Sym2.map (σ * τ : Equiv.Perm (Fin 4))) = M.edgeF j := by
  rw [Equiv.Perm.coe_mul, Sym2.map_comp, ← Function.comp_assoc, hτ, hσ]

/-- **Tetrahedral symmetry** from the three generators (Physlib's argument). -/
lemma edgeF_comp_map (σ : Equiv.Perm (Fin 4)) (j : Sym2 (Fin 4) → ℕ) :
    M.edgeF (j ∘ Sym2.map σ) = M.edgeF j := by
  have h12 := M.edgeF_swap₁₂
  have h23 := M.edgeF_swap₂₃
  have h03 : ∀ j, M.edgeF (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 3)) = M.edgeF j := by
    rw [show Equiv.swap (0 : Fin 4) 3 = Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 1 2 by decide]
    exact M.edgeF_comp_map_mul M.edgeF_flip h12
  have h13 : ∀ j, M.edgeF (j ∘ Sym2.map (Equiv.swap (1 : Fin 4) 3)) = M.edgeF j := by
    rw [show Equiv.swap (1 : Fin 4) 3 = Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 2 3 by decide]
    exact M.edgeF_comp_map_mul (M.edgeF_comp_map_mul h23 h12) h23
  have h02 : ∀ j, M.edgeF (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 2)) = M.edgeF j := by
    rw [show Equiv.swap (0 : Fin 4) 2 = Equiv.swap 2 3 * Equiv.swap 0 3 * Equiv.swap 2 3 by decide]
    exact M.edgeF_comp_map_mul (M.edgeF_comp_map_mul h23 h03) h23
  have h01 : ∀ j, M.edgeF (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 1)) = M.edgeF j := by
    rw [show Equiv.swap (0 : Fin 4) 1 = Equiv.swap 1 2 * Equiv.swap 0 2 * Equiv.swap 1 2 by decide]
    exact M.edgeF_comp_map_mul (M.edgeF_comp_map_mul h12 h02) h12
  have hswap : ∀ x y : Fin 4, x ≠ y →
      ∀ j, M.edgeF (j ∘ Sym2.map (Equiv.swap x y)) = M.edgeF j := by
    intro x y hxy
    have : Equiv.swap x y = Equiv.swap 0 1 ∨ Equiv.swap x y = Equiv.swap 0 2 ∨
        Equiv.swap x y = Equiv.swap 0 3 ∨ Equiv.swap x y = Equiv.swap 1 2 ∨
        Equiv.swap x y = Equiv.swap 1 3 ∨ Equiv.swap x y = Equiv.swap 2 3 := by
      revert x y; decide
    rcases this with h | h | h | h | h | h
    · rw [h]; exact h01
    · rw [h]; exact h02
    · rw [h]; exact h03
    · rw [h]; exact h12
    · rw [h]; exact h13
    · rw [h]; exact h23
  induction σ using Equiv.Perm.swap_induction_on generalizing j with
  | one => rw [Equiv.Perm.coe_one, Sym2.map_id]; rfl
  | swap_mul f x y hxy ih => exact M.edgeF_comp_map_mul (hswap x y hxy) ih j

/-! ## The 6j symbol of a tetrahedron -/

variable {V : Type*} [DecidableEq V]

/-- The 6j symbol of the tetrahedron `p 0, p 1, p 2, p 3` in the colouring `col`. -/
noncomputable def tetAmp (col : Colouring V) (p : Fin 4 → V) : ℝ := M.edgeF (dualCol col p)

theorem tetAmp_comp_perm (col : Colouring V) (p : Fin 4 → V) (σ : Equiv.Perm (Fin 4)) :
    M.tetAmp col (p ∘ σ) = M.tetAmp col p := by
  rw [tetAmp, dualCol_comp_perm, M.edgeF_comp_map, tetAmp]

theorem tetAmp_eq (col : Colouring V) (p : Fin 4 → V) :
    M.tetAmp col p = M.f (col {p 2, p 3}) (col {p 1, p 3}) (col {p 1, p 2}) (col {p 0, p 1})
      (col {p 0, p 2}) (col {p 0, p 3}) := by
  have h : ∀ i k : Fin 4, ∀ l m : Fin 4, (univ \ {i, k} : Finset (Fin 4)) = {l, m} →
      dualCol col p s(i, k) = col {p l, p m} := by
    intro i k l m h
    simp only [dualCol, Sym2.lift_mk, h, image_insert, image_singleton]
  rw [tetAmp, edgeF, h 0 1 2 3 (by decide), h 0 2 1 3 (by decide), h 0 3 1 2 (by decide),
    h 2 3 0 1 (by decide), h 1 3 0 2 (by decide), h 1 2 0 3 (by decide)]

lemma tetAmp_reindex (col : Colouring V) {p q : Fin 4 → V} (hq : Function.Injective q)
    (h : ∀ i, ∃ k, q i = p k) : M.tetAmp col q = M.tetAmp col p := by
  choose σ hσ using h
  have hinj : Function.Injective σ := fun i j hij => hq (by rw [hσ, hσ, hij])
  have hbij := Finite.injective_iff_bijective.mp hinj
  rw [show q = p ∘ Equiv.ofBijective σ hbij from funext hσ, M.tetAmp_comp_perm]

/-- A nonzero 6j symbol has admissible faces; first the face `p₁p₂p₃`. -/
lemma tetAmp_eq_zero_of_not_ok (col : Colouring V) (p : Fin 4 → V)
    (h : ¬ M.ok (col {p 2, p 3}) (col {p 1, p 3}) (col {p 1, p 2})) : M.tetAmp col p = 0 := by
  by_contra h0
  rw [M.tetAmp_eq] at h0
  exact h (M.f_ok h0).1

/-- Edge weight `dim J · (-1)^J`. -/
noncomputable def edgeW (J : ℕ) : ℝ := M.dim J * (-1) ^ J

/-! ## Biedenharn–Elliott and the local 2-3 move -/

/-- **Biedenharn–Elliott for the model**, summed over all colours. -/
def BE : Prop :=
  ∀ a b c d e f p q r : ℕ, ∑ x ∈ range M.N,
    (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * M.dim x *
      (M.f a b x c d p * M.f c d x e f q * M.f e f x b a r) =
    M.f p q r e a d * M.f p q r f b c

/-- **The local 2-3 move** for the model, assuming its Biedenharn–Elliott identity. -/
theorem pachner23_local (hBE : M.BE) (col : Colouring V) {A B C D E : V}
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E) (hBC : B ≠ C) (hBD : B ≠ D)
    (hBE' : B ≠ E) (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) :
    triSign col A B C * (M.tetAmp col ![A, B, C, D] * M.tetAmp col ![A, B, C, E]) =
      ∑ x ∈ range M.N,
        M.edgeW x * (triSign (Function.update col {D, E} x) A D E *
          triSign (Function.update col {D, E} x) B D E *
          triSign (Function.update col {D, E} x) C D E) *
        (M.tetAmp (Function.update col {D, E} x) ![A, B, D, E] *
          M.tetAmp (Function.update col {D, E} x) ![B, C, D, E] *
          M.tetAmp (Function.update col {D, E} x) ![C, A, D, E]) := by
  have hu : ∀ (x : ℕ) {u : V} (v : V), u ≠ D → u ≠ E →
      Function.update col {D, E} x {u, v} = col {u, v} :=
    fun x u v h1 h2 => Function.update_of_ne (pair_ne_of_not_mem h1 h2) _ _
  have hx : ∀ x : ℕ, Function.update col {D, E} x {D, E} = x :=
    fun x => Function.update_self _ _ _
  have t1 : M.tetAmp col ![A, B, C, D] = M.f (col {A, B}) (col {B, C}) (col {C, A})
      (col {C, D}) (col {A, D}) (col {B, D}) := by
    rw [← M.tetAmp_reindex col (q := ![D, C, A, B])
      (injective_vec4 hCD.symm hAD.symm hBD.symm hAC.symm hBC.symm hAB)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩]), M.tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm C B, pair_comm D C, pair_comm D A, pair_comm D B]
  have t2 : M.tetAmp col ![A, B, C, E] = M.f (col {A, B}) (col {B, C}) (col {C, A})
      (col {C, E}) (col {A, E}) (col {B, E}) := by
    rw [← M.tetAmp_reindex col (q := ![E, C, A, B])
      (injective_vec4 hCE.symm hAE.symm hBE'.symm hAC.symm hBC.symm hAB)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩]), M.tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm C B, pair_comm E C, pair_comm E A, pair_comm E B]
  have t3 : ∀ x, M.tetAmp (Function.update col {D, E} x) ![A, B, D, E] =
      M.f (col {A, D}) (col {A, E}) x (col {B, E}) (col {B, D}) (col {A, B}) := by
    intro x
    rw [← M.tetAmp_reindex _ (q := ![B, E, D, A])
      (injective_vec4 hBE' hBD hAB.symm hDE.symm hAE.symm hAD.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩]), M.tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm D A, pair_comm E A, pair_comm E D, pair_comm B A, hx, hu x D hAD hAE,
      hu x E hAD hAE, hu x E hBD hBE', hu x D hBD hBE', hu x B hAD hAE]
  have t4 : ∀ x, M.tetAmp (Function.update col {D, E} x) ![B, C, D, E] =
      M.f (col {B, E}) (col {B, D}) x (col {C, D}) (col {C, E}) (col {B, C}) := by
    intro x
    rw [← M.tetAmp_reindex _ (q := ![C, D, E, B])
      (injective_vec4 hCD hCE hBC.symm hDE hBD.symm hBE'.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩]), M.tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pair_comm E B, pair_comm D B, pair_comm C B, hx, hu x E hBD hBE', hu x D hBD hBE',
      hu x D hCD hCE, hu x E hCD hCE, hu x C hBD hBE']
  have t5 : ∀ x, M.tetAmp (Function.update col {D, E} x) ![C, A, D, E] =
      M.f (col {C, D}) (col {C, E}) x (col {A, E}) (col {A, D}) (col {C, A}) := by
    intro x
    rw [← M.tetAmp_reindex _ (q := ![A, E, D, C])
      (injective_vec4 hAE hAD hAC hDE.symm hCE.symm hCD.symm)
      (by intro i; fin_cases i; exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩, ⟨0, rfl⟩]), M.tetAmp_eq]
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
  generalize col {A, D} = a
  generalize col {A, E} = b
  generalize col {B, E} = c
  generalize col {B, D} = d
  generalize col {C, D} = e
  generalize col {C, E} = f
  generalize col {A, B} = p
  generalize col {B, C} = q
  generalize col {C, A} = r
  rw [← hBE a b c d e f p q r, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hz : M.f a b x c d p * M.f c d x e f q * M.f e f x b a r = 0
  · rw [hz]; ring
  have h3 := M.f_ok (left_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have h4 := M.f_ok (right_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have h5 := M.f_ok (right_ne_zero_of_mul hz)
  have T1 := M.ok_tri h3.1
  have T2 := M.ok_tri h3.2.1
  have T3 := M.ok_tri h3.2.2.1
  have T4 := M.ok_tri h4.1
  have T5 := M.ok_tri h4.2.1
  have T6 := M.ok_tri h5.1
  have T7 := M.ok_tri h5.2.2.2
  unfold Tri at T1 T2 T3 T4 T5 T6 T7
  have hsign : (-1 : ℝ) ^ ((p + q + r) / 2) * (-1) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) =
      (-1) ^ x * ((-1) ^ ((a + x + b) / 2) * (-1) ^ ((d + x + c) / 2) *
        (-1) ^ ((e + x + f) / 2)) := by
    simp only [← pow_add]
    exact neg_one_pow_congr (by omega)
  rw [edgeW]
  linear_combination M.dim x * (M.f a b x c d p * M.f c d x e f q * M.f e f x b a r) * hsign

/-! ## Weights of complexes and the 2-3 move -/

/-- The 6j symbol of a tetrahedron given as a vertex set (any enumeration). -/
noncomputable def tetW (col : Colouring V) (t : Finset V) : ℝ :=
  if h : #t = 4 then M.tetAmp col (fun i => ((t.equivFinOfCardEq h).symm i : V)) else 0

lemma tetW_eq_tetAmp (col : Colouring V) {t : Finset V} (ht : #t = 4) {p : Fin 4 → V}
    (hp : Function.Injective p) (hpt : ∀ i, p i ∈ t) : M.tetW col t = M.tetAmp col p := by
  rw [tetW, dite_eq_left_of_eq_true (eq_true ht)]
  exact (M.tetAmp_reindex col hp fun i =>
    ⟨t.equivFinOfCardEq ht ⟨p i, hpt i⟩, by simp⟩).symm

lemma tetAmp_congr {col col' : Colouring V} {p : Fin 4 → V}
    (h : ∀ i k, i ≠ k → col {p i, p k} = col' {p i, p k}) : M.tetAmp col p = M.tetAmp col' p := by
  rw [M.tetAmp_eq, M.tetAmp_eq, h 2 3 (by decide), h 1 3 (by decide), h 1 2 (by decide),
    h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide)]

lemma tetW_congr {col col' : Colouring V} {t : Finset V}
    (h : ∀ e ⊆ t, #e = 2 → col e = col' e) : M.tetW col t = M.tetW col' t := by
  unfold tetW
  split_ifs with ht
  · refine M.tetAmp_congr fun i k hik => h _ ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact coe_mem _
    · rw [card_pair]
      intro heq
      exact hik ((t.equivFinOfCardEq ht).symm.injective (Subtype.ext heq))
  · rfl

/-- The weight of a coloured complex in the model. -/
noncomputable def weight (K : Complex3 V) (col : Colouring V) : ℝ :=
  (∏ e ∈ K.edges, M.edgeW (col e)) * (∏ f ∈ K.tris, triW col f) * ∏ t ∈ K.tets, M.tetW col t

/-- **The 2-3 move on a complex** (model version of `Lightlike.PR.weight_move23`). -/
theorem weight_move23 (hBE : M.BE) (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (col : Colouring V) :
    M.weight K col = ∑ x ∈ range M.N, M.weight (move23 K h) (Function.update col {D, E} x) := by
  set rest := (K.tets.erase {A, B, C, D}).erase {A, B, C, E} with hrest
  have hT12 : ({A, B, C, D} : Finset V) ≠ {A, B, C, E} := fun h' => by
    have : D ∈ ({A, B, C, E} : Finset V) := h' ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAD h''.symm; exact h.hBD h''.symm;
      exact h.hCD h''.symm; exact h.hDE h'']
  have hagree : ∀ x, ∀ t ∈ K.tets, ∀ e ⊆ t, #e = 2 →
      col e = Function.update col {D, E} x e := by
    intro x t ht e het he
    rw [Function.update_of_ne]
    rintro rfl
    exact h.fresh t ht het
  have hDE_notin : ({D, E} : Finset V) ∉ K.edges := by
    rw [Complex3.mem_edges]; rintro ⟨t, ht, hst, -⟩; exact h.fresh t ht hst
  have hABC : ({A, B, C} : Finset V) ∈ K.tris :=
    Complex3.mem_tris.mpr ⟨_, h.mem₁, by small_subset, card_three h.hAB h.hAC h.hBC⟩
  have hnew : ∀ u, ({u, D, E} : Finset V) ∉ K.tris.erase {A, B, C} :=
    fun u hu => not_mem_tris_of_fresh K h.fresh u (mem_of_mem_erase hu)
  have hne3 : ∀ {u v : V}, u ≠ v → u ≠ D → u ≠ E → ({u, D, E} : Finset V) ≠ {v, D, E} := by
    intro u v huv huD huE h'
    have : u ∈ ({v, D, E} : Finset V) := h' ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hfreshT : ∀ {u v : V}, ({u, v, D, E} : Finset V) ∉ rest := fun hmem =>
    h.fresh _ (mem_of_mem_erase (mem_of_mem_erase hmem)) (by small_subset)
  have hK : M.weight K col = (∏ e ∈ K.edges, M.edgeW (col e)) *
      (triW col {A, B, C} * ∏ f ∈ K.tris.erase {A, B, C}, triW col f) *
      (M.tetW col {A, B, C, D} * (M.tetW col {A, B, C, E} * ∏ t ∈ rest, M.tetW col t)) := by
    rw [hrest, weight, mul_prod_erase _ _ hABC,
      mul_prod_erase _ _ (mem_erase.mpr ⟨hT12.symm, h.mem₂⟩), mul_prod_erase _ _ h.mem₁]
  have hK' : ∀ x, M.weight (move23 K h) (Function.update col {D, E} x) =
      (M.edgeW x * (triW (Function.update col {D, E} x) {A, D, E} *
        triW (Function.update col {D, E} x) {B, D, E} *
        triW (Function.update col {D, E} x) {C, D, E}) *
      (M.tetW (Function.update col {D, E} x) {A, B, D, E} *
        M.tetW (Function.update col {D, E} x) {B, C, D, E} *
        M.tetW (Function.update col {D, E} x) {C, A, D, E})) *
      ((∏ e ∈ K.edges, M.edgeW (col e)) * (∏ f ∈ K.tris.erase {A, B, C}, triW col f) *
        ∏ t ∈ rest, M.tetW col t) := by
    intro x
    have he : ∏ e ∈ K.edges, M.edgeW (Function.update col {D, E} x e) =
        ∏ e ∈ K.edges, M.edgeW (col e) := by
      refine prod_congr rfl fun e he => ?_
      obtain ⟨t, ht, het, hc⟩ := Complex3.mem_edges.mp he
      rw [hagree x t ht e het hc]
    have hf : ∏ f ∈ K.tris.erase {A, B, C}, triW (Function.update col {D, E} x) f =
        ∏ f ∈ K.tris.erase {A, B, C}, triW col f := by
      refine prod_congr rfl fun f hf => ?_
      obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp (mem_of_mem_erase hf)
      exact (triW_congr fun e hef hc => hagree x t ht e (hef.trans hft) hc).symm
    have ht : ∏ t ∈ rest, M.tetW (Function.update col {D, E} x) t =
        ∏ t ∈ rest, M.tetW col t := by
      refine prod_congr rfl fun t ht => ?_
      exact (M.tetW_congr fun e het hc =>
        hagree x t (mem_of_mem_erase (mem_of_mem_erase ht)) e het hc).symm
    have hdisj : Disjoint ({{A, B, D, E}, {B, C, D, E}, {C, A, D, E}} : Finset (Finset V)) rest := by
      rw [disjoint_left]
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact hfreshT
    have h34 : ({A, B, D, E} : Finset V) ∉ ({{B, C, D, E}, {C, A, D, E}} : Finset (Finset V)) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have : A ∈ ({B, C, D, E} : Finset V) := h' ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAB h''; exact h.hAC h'';
          exact h.hAD h''; exact h.hAE h'']
      · have : B ∈ ({C, A, D, E} : Finset V) := h' ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h'' | h'' <;> [exact h.hBC h''; exact h.hAB h''.symm;
          exact h.hBD h''; exact h.hBE h'']
    have h45 : ({B, C, D, E} : Finset V) ≠ {C, A, D, E} := fun h' => by
      have : B ∈ ({C, A, D, E} : Finset V) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h'' | h'' | h'' | h'' <;> [exact h.hBC h''; exact h.hAB h''.symm;
        exact h.hBD h''; exact h.hBE h'']
    rw [weight, edges_move23, tris_move23, prod_insert hDE_notin, he,
      prod_insert (by
        simp only [mem_insert, not_or]
        exact ⟨hne3 h.hAB h.hAD h.hAE, hne3 h.hAC h.hAD h.hAE, hnew A⟩),
      prod_insert (by
        simp only [mem_insert, not_or]
        exact ⟨hne3 h.hBC h.hBD h.hBE, hnew B⟩),
      prod_insert (hnew C), hf]
    simp only [move23]
    rw [prod_union hdisj, prod_insert h34, prod_pair h45, ht, Function.update_self]
    ring
  have hloc := M.pachner23_local hBE col h.hAB h.hAC h.hAD h.hAE h.hBC h.hBD h.hBE h.hCD h.hCE
    h.hDE
  rw [← triW_three col h.hAB h.hAC h.hBC,
    ← M.tetW_eq_tetAmp col (card_four h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD)
      (injective_vec4 h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD) (by intro i; fin_cases i <;> simp),
    ← M.tetW_eq_tetAmp col (card_four h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE)
      (injective_vec4 h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE) (by intro i; fin_cases i <;> simp)]
    at hloc
  have hterm : ∀ x, M.edgeW x * (triSign (Function.update col {D, E} x) A D E *
        triSign (Function.update col {D, E} x) B D E *
        triSign (Function.update col {D, E} x) C D E) *
      (M.tetAmp (Function.update col {D, E} x) ![A, B, D, E] *
        M.tetAmp (Function.update col {D, E} x) ![B, C, D, E] *
        M.tetAmp (Function.update col {D, E} x) ![C, A, D, E]) =
      M.edgeW x * (triW (Function.update col {D, E} x) {A, D, E} *
        triW (Function.update col {D, E} x) {B, D, E} *
        triW (Function.update col {D, E} x) {C, D, E}) *
      (M.tetW (Function.update col {D, E} x) {A, B, D, E} *
        M.tetW (Function.update col {D, E} x) {B, C, D, E} *
        M.tetW (Function.update col {D, E} x) {C, A, D, E}) := by
    intro x
    rw [triW_three _ h.hAD h.hAE h.hDE, triW_three _ h.hBD h.hBE h.hDE,
      triW_three _ h.hCD h.hCE h.hDE,
      M.tetW_eq_tetAmp _ (card_four h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE)
        (injective_vec4 h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE) (by intro i; fin_cases i <;> simp),
      M.tetW_eq_tetAmp _ (card_four h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE)
        (injective_vec4 h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE) (by intro i; fin_cases i <;> simp),
      M.tetW_eq_tetAmp _ (card_four h.hAC.symm h.hCD h.hCE h.hAD h.hAE h.hDE)
        (injective_vec4 h.hAC.symm h.hCD h.hCE h.hAD h.hAE h.hDE)
        (by intro i; fin_cases i <;> simp)]
  simp only [hterm] at hloc
  simp only [hK']
  rw [← sum_mul, ← hloc, hK]
  ring

/-! ## The normalised state sum -/

/-- The vertices of a complex. -/
def vertices (K : Complex3 V) : Finset V := K.tets.biUnion id

/-- The vertex normalisation `W = Σ_d dim(d)²`. -/
noncomputable def W : ℝ := ∑ d ∈ range M.N, M.dim d ^ 2

/-- **The normalised state sum** `Z K = W^{-#vertices} Σ_colourings weight`. -/
noncomputable def Z (K : Complex3 V) : ℝ :=
  M.W⁻¹ ^ #(vertices K) *
    ∑ σ ∈ K.edges.pi (fun _ => range M.N), M.weight K (extS K.edges σ)

lemma vertices_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    vertices (move23 K h) = vertices K := by
  ext v
  simp only [vertices, mem_biUnion, id, move23, mem_union, mem_erase, mem_insert, mem_singleton]
  have m1 : ∀ {w}, w = A ∨ w = B ∨ w = C ∨ w = D → ∃ t ∈ K.tets, w ∈ t := fun hw =>
    ⟨_, h.mem₁, by rcases hw with rfl | rfl | rfl | rfl <;> simp⟩
  have m2 : ∃ t ∈ K.tets, E ∈ t := ⟨_, h.mem₂, by simp⟩
  constructor
  · rintro ⟨t, (rfl | rfl | rfl) | ⟨-, -, ht⟩, hv⟩
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with hv | hv | hv | hv
      exacts [m1 (Or.inl hv), m1 (Or.inr (Or.inl hv)), m1 (Or.inr (Or.inr (Or.inr hv))), hv ▸ m2]
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with hv | hv | hv | hv
      exacts [m1 (Or.inr (Or.inl hv)), m1 (Or.inr (Or.inr (Or.inl hv))),
        m1 (Or.inr (Or.inr (Or.inr hv))), hv ▸ m2]
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with hv | hv | hv | hv
      exacts [m1 (Or.inr (Or.inr (Or.inl hv))), m1 (Or.inl hv),
        m1 (Or.inr (Or.inr (Or.inr hv))), hv ▸ m2]
    · exact ⟨t, ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    have hA : ∃ t, ((t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}) ∨
        ¬t = {A, B, C, E} ∧ ¬t = {A, B, C, D} ∧ t ∈ K.tets) ∧ A ∈ t :=
      ⟨_, Or.inl (Or.inl rfl), by simp⟩
    have hB : ∃ t, ((t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}) ∨
        ¬t = {A, B, C, E} ∧ ¬t = {A, B, C, D} ∧ t ∈ K.tets) ∧ B ∈ t :=
      ⟨_, Or.inl (Or.inl rfl), by simp⟩
    have hC : ∃ t, ((t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}) ∨
        ¬t = {A, B, C, E} ∧ ¬t = {A, B, C, D} ∧ t ∈ K.tets) ∧ C ∈ t :=
      ⟨_, Or.inl (Or.inr (Or.inl rfl)), by simp⟩
    have hD : ∃ t, ((t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}) ∨
        ¬t = {A, B, C, E} ∧ ¬t = {A, B, C, D} ∧ t ∈ K.tets) ∧ D ∈ t :=
      ⟨_, Or.inl (Or.inl rfl), by simp⟩
    have hE : ∃ t, ((t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}) ∨
        ¬t = {A, B, C, E} ∧ ¬t = {A, B, C, D} ∧ t ∈ K.tets) ∧ E ∈ t :=
      ⟨_, Or.inl (Or.inl rfl), by simp⟩
    by_cases h1 : t = {A, B, C, D}
    · subst h1
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hA, hB, hC, hD]
    by_cases h2 : t = {A, B, C, E}
    · subst h2
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hA, hB, hC, hE]
    exact ⟨t, Or.inr ⟨h2, h1, ht⟩, hv⟩

/-- **The normalised state sum is invariant under the 2-3 move**, given Biedenharn–Elliott. -/
theorem Z_move23 (hBE : M.BE) (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    M.Z (move23 K h) = M.Z K := by
  have hDE_notin : ({D, E} : Finset V) ∉ K.edges := by
    rw [Complex3.mem_edges]; rintro ⟨t, ht, hst, -⟩; exact h.fresh t ht hst
  rw [Z, Z, vertices_move23, edges_move23, sum_pi_insert hDE_notin]
  congr 1
  exact sum_congr rfl fun σ _ => (M.weight_move23 hBE K h _).symm

/-! ## Orthogonality, the fusion count and the local 1-4 move -/

/-- Diagonal orthogonality for the model. -/
def Orth : Prop :=
  ∀ B A E F q : ℕ, ∑ x ∈ range M.N, M.dim x * (M.f B A x E F q) ^ 2 =
    if M.ok A E q ∧ M.ok B q F then 1 / M.dim q else 0

/-- The fusion count `Σ_{b adm} dim b = dim p · dim d`. -/
def Count : Prop :=
  ∀ p d : ℕ, p < M.N → d < M.N →
    ∑ b ∈ range M.N, (if M.ok p b d then M.dim b else 0) = M.dim p * M.dim d

lemma ok_perm {a b c : ℕ} (h : M.ok a b c) :
    M.ok a c b ∧ M.ok b a c ∧ M.ok b c a ∧ M.ok c a b ∧ M.ok c b a :=
  ⟨M.ok_swap23 h, M.ok_swap12 h, M.ok_swap23 (M.ok_swap12 h), M.ok_swap12 (M.ok_swap23 h),
    M.ok_swap23 (M.ok_swap12 (M.ok_swap23 h))⟩

/-- The local weight of the four new tetrahedra of a 1-4 move (model version of `term14`). -/
noncomputable def term14 (col : Colouring V) (A B C D E : V) (a b c : ℕ) : ℝ :=
  (M.edgeW b * M.edgeW c * M.edgeW (col {D, E}) *
      (triSign (upd14 col A B C E a b c) B C E * triSign (upd14 col A B C E a b c) B D E *
        triSign (upd14 col A B C E a b c) C D E) *
      M.tetAmp (upd14 col A B C E a b c) ![B, C, D, E]) *
    (M.edgeW a * (triSign (upd14 col A B C E a b c) B A E *
        triSign (upd14 col A B C E a b c) C A E * triSign (upd14 col A B C E a b c) D A E) *
      (M.tetAmp (upd14 col A B C E a b c) ![B, C, A, E] *
        M.tetAmp (upd14 col A B C E a b c) ![C, D, A, E] *
        M.tetAmp (upd14 col A B C E a b c) ![D, B, A, E]))

/-- **The local 1-4 move for the model**: with the colour `d < N` of `DE` fixed, the four new
tetrahedra summed over the colours of `AE, BE, CE` give `dim(d)² · {ABCD}`. -/
theorem pachner14_local (hBEid : M.BE) (hOrth : M.Orth) (hCount : M.Count)
    (hdim : ∀ J, J < M.N → M.dim J ≠ 0) (col : Colouring V) {A B C D E : V} (hAB : A ≠ B)
    (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E) (hBC : B ≠ C) (hBD : B ≠ D) (hBE' : B ≠ E)
    (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) (hd : col {D, E} < M.N) :
    ∑ a ∈ range M.N, ∑ b ∈ range M.N, ∑ c ∈ range M.N, M.term14 col A B C D E a b c =
      M.dim (col {D, E}) ^ 2 * M.tetAmp col ![A, B, C, D] := by
  have hBE := hBE'
  have hqBCDE : ∀ (κ : Colouring V), M.tetAmp κ ![B, C, D, E] = M.tetAmp κ ![D, E, C, B] :=
    fun κ => (M.tetAmp_reindex κ (injective_vec4 hDE hCD.symm hBD.symm hCE.symm hBE.symm
      hBC.symm) (by intro i; fin_cases i; exacts [⟨2, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨0, rfl⟩])).symm
  have hS : ∀ a b c, M.tetAmp (upd14 col A B C E a b c) ![B, C, D, E] =
      M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
    intro a b c
    rw [hqBCDE, M.tetAmp_eq]
    ev14
  have hS' : ∀ b c, M.tetAmp (Function.update (Function.update col {B, E} b) {C, E} c)
      ![B, C, D, E] = M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
    intro b c
    rw [hqBCDE, M.tetAmp_eq]
    ev14
  have hABCD : ∀ b c, M.tetAmp (Function.update (Function.update col {B, E} b) {C, E} c)
      ![B, C, D, A] = M.tetAmp col ![A, B, C, D] := by
    intro b c
    rw [← M.tetAmp_reindex _ (q := ![A, B, C, D]) (injective_vec4 hAB hAC hAD hBC hBD hCD)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]),
      M.tetAmp_eq, M.tetAmp_eq (col := col)]
    ev14
  have hstep : ∀ b c, ∑ a ∈ range M.N, M.term14 col A B C D E a b c =
      M.dim b * M.dim c * M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
        (M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 := by
    intro b c
    have hG : ∀ a, M.edgeW b * M.edgeW c * M.edgeW (col {D, E}) *
        (triSign (upd14 col A B C E a b c) B C E * triSign (upd14 col A B C E a b c) B D E *
          triSign (upd14 col A B C E a b c) C D E) *
        M.tetAmp (upd14 col A B C E a b c) ![B, C, D, E] =
        M.edgeW b * M.edgeW c * M.edgeW (col {D, E}) *
          ((-1 : ℝ) ^ ((col {B, C} + c + b) / 2) * (-1) ^ ((col {B, D} + col {D, E} + b) / 2) *
            (-1) ^ ((col {C, D} + col {D, E} + c) / 2)) *
          M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
      intro a
      rw [hS]
      simp only [triSign]
      ev14
    have h23 := M.pachner23_local hBEid (Function.update (Function.update col {B, E} b) {C, E} c)
      hBC hBD hAB.symm hBE hCD hAC.symm hCE hAD.symm hDE hAE
    have hH : ∑ a ∈ range M.N,
        M.edgeW a * (triSign (upd14 col A B C E a b c) B A E *
          triSign (upd14 col A B C E a b c) C A E * triSign (upd14 col A B C E a b c) D A E) *
        (M.tetAmp (upd14 col A B C E a b c) ![B, C, A, E] *
          M.tetAmp (upd14 col A B C E a b c) ![C, D, A, E] *
          M.tetAmp (upd14 col A B C E a b c) ![D, B, A, E]) =
        (-1 : ℝ) ^ ((col {B, C} + col {C, D} + col {B, D}) / 2) * (M.tetAmp col ![A, B, C, D] *
          M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) := by
      refine h23.symm.trans ?_
      rw [hS', hABCD]
      simp only [triSign]
      ev14
    rw [sum_congr rfl fun a _ => by rw [term14, hG a], ← mul_sum, hH]
    by_cases hS0 : M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) = 0
    · rw [hS0]; ring
    obtain ⟨O1, O2, O3, O4⟩ := M.f_ok hS0
    have T1 := M.ok_tri O1
    have T2 := M.ok_tri O2
    have T3 := M.ok_tri O3
    have T4 := M.ok_tri O4
    have hsgn : (-1 : ℝ) ^ b * (-1) ^ c * (-1) ^ col {D, E} *
        ((-1) ^ ((col {B, C} + c + b) / 2) * (-1) ^ ((col {B, D} + col {D, E} + b) / 2) *
          (-1) ^ ((col {C, D} + col {D, E} + c) / 2)) *
        (-1) ^ ((col {B, C} + col {C, D} + col {B, D}) / 2) = 1 := by
      simp only [← pow_add]
      exact Even.neg_one_pow (Nat.even_iff.mpr (by unfold Tri at *; omega))
    unfold edgeW
    linear_combination M.dim b * M.dim c * M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
      (M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 * hsgn
  rw [sum_comm, sum_congr rfl fun b _ => sum_comm,
    sum_congr rfl fun b _ => sum_congr rfl fun c _ => hstep b c]
  have hrow : ∀ b : ℕ, ∑ c ∈ range M.N,
      M.dim b * M.dim c * M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
        (M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 =
      M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
        (if M.ok (col {B, C}) (col {B, D}) (col {C, D}) then
          (if M.ok (col {B, D}) b (col {D, E}) then M.dim b / M.dim (col {B, D}) else 0)
        else 0) := by
    intro b
    have : ∀ c : ℕ, M.dim b * M.dim c * M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
        (M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 =
        M.dim b * M.dim (col {D, E}) * M.tetAmp col ![A, B, C, D] *
        (M.dim c * (M.f (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2) :=
      fun c => by ring
    rw [sum_congr rfl fun c _ => this c, ← mul_sum, hOrth]
    by_cases h1 : M.ok (col {B, C}) (col {B, D}) (col {C, D})
    · by_cases h2 : M.ok b (col {D, E}) (col {B, D})
      · have h2' : M.ok (col {B, D}) b (col {D, E}) := (M.ok_perm h2).2.2.2.1
        rw [ite_eq_left ⟨h2, h1⟩, ite_eq_left h1, ite_eq_left h2']
        ring
      · have h2' : ¬ M.ok (col {B, D}) b (col {D, E}) := fun h => h2 (M.ok_perm h).2.2.1
        rw [ite_eq_right (fun h => h2 h.1), ite_eq_left h1, ite_eq_right h2']
        ring
    · rw [ite_eq_right (fun h => h1 h.2), ite_eq_right h1]
      ring
  rw [sum_congr rfl fun b _ => hrow b, ← mul_sum]
  by_cases h1 : M.ok (col {B, C}) (col {B, D}) (col {C, D})
  · have hBDN : col {B, D} < M.N := M.ok_lt (M.ok_perm h1).2.1
    simp only [ite_eq_left h1]
    have hc := hCount (col {B, D}) (col {D, E}) hBDN hd
    have hsplit : ∑ b ∈ range M.N,
        (if M.ok (col {B, D}) b (col {D, E}) then M.dim b / M.dim (col {B, D}) else 0) =
        (∑ b ∈ range M.N, (if M.ok (col {B, D}) b (col {D, E}) then M.dim b else 0)) /
          M.dim (col {B, D}) := by
      rw [sum_div]
      exact sum_congr rfl fun b _ => by split_ifs <;> simp
    rw [hsplit, hc]
    have := hdim _ hBDN
    field_simp
  · have hT0 : M.tetAmp col ![A, B, C, D] = 0 :=
      M.tetAmp_eq_zero_of_not_ok _ _ (by
        ev14
        exact fun h => h1 (M.ok_perm h).2.2.2.2)
    rw [hT0]
    ring

/-! ## The 1-4 move on complexes and the invariance of `Z` -/

/-- The weight after a 1-4 move factorises (model version of `weight_move14_eq`). -/
theorem weight_move14_eq (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    (col : Colouring V) (a b c d : ℕ) :
    M.weight (move14 K h) (upd14 (Function.update col {D, E} d) A B C E a b c) =
      ((∏ e ∈ K.edges, M.edgeW (col e)) * (∏ f ∈ K.tris, triW col f) *
        ∏ t ∈ K.tets.erase {A, B, C, D}, M.tetW col t) *
      M.term14 (Function.update col {D, E} d) A B C D E a b c := by
  have hAB := h.hAB; have hAC := h.hAC; have hAD := h.hAD; have hAE := h.hAE
  have hBC := h.hBC; have hBD := h.hBD; have hBE := h.hBE; have hCD := h.hCD
  have hCE := h.hCE; have hDE := h.hDE
  have hoff : ∀ e : Finset V, E ∉ e →
      upd14 (Function.update col {D, E} d) A B C E a b c e = col e := by
    intro e he
    have hne : ∀ X : V, e ≠ {X, E} := fun X h' => he (h' ▸ by simp)
    simp only [upd14]
    rw [Function.update_of_ne (hne A), Function.update_of_ne (hne C),
      Function.update_of_ne (hne B), Function.update_of_ne (hne D)]
  have hEt : ∀ t ∈ K.tets, ∀ e ⊆ t, E ∉ e := fun t ht e he hE => h.fresh t ht (he hE)
  have hdE : Disjoint K.edges {{A, E}, {B, E}, {C, E}, {D, E}} := by
    rw [disjoint_left]
    intro e he hnew
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl <;> exact hEt t ht _ hst (by simp)
  have hdT : Disjoint K.tris {{A, B, E}, {A, C, E}, {A, D, E}, {B, C, E}, {B, D, E}, {C, D, E}} := by
    rw [disjoint_left]
    intro f hf hnew
    obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp hf
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hEt t ht _ hft (by simp)
  have hdK : Disjoint ({{A, B, C, E}, {A, B, D, E}, {A, C, D, E}, {B, C, D, E}} : Finset (Finset V))
      (K.tets.erase {A, B, C, D}) := by
    rw [disjoint_left]
    intro t hnew ht
    have := h.fresh t (mem_of_mem_erase ht)
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl <;> exact this (by simp)
  rw [Model.weight, edges_move14, tris_move14, prod_union hdE, prod_union hdT,
    show (move14 K h).tets = _ ∪ _ from rfl, prod_union hdK]
  have p1 : ∏ e ∈ K.edges, M.edgeW (upd14 (Function.update col {D, E} d) A B C E a b c e) =
      ∏ e ∈ K.edges, M.edgeW (col e) := prod_congr rfl fun e he => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
    rw [hoff e (hEt t ht e hst)]
  have p2 : ∏ f ∈ K.tris, triW (upd14 (Function.update col {D, E} d) A B C E a b c) f =
      ∏ f ∈ K.tris, triW col f := prod_congr rfl fun f hf => by
    obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp hf
    exact triW_congr fun e he _ => hoff e (hEt t ht e (he.trans hft))
  have p3 : ∏ t ∈ K.tets.erase {A, B, C, D},
      M.tetW (upd14 (Function.update col {D, E} d) A B C E a b c) t =
      ∏ t ∈ K.tets.erase {A, B, C, D}, M.tetW col t := prod_congr rfl fun t ht =>
    M.tetW_congr fun e he _ => hoff e (hEt t (mem_of_mem_erase ht) e he)
  rw [p1, p2, p3]
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_singleton]
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_insert (by notmem14), prod_insert (by notmem14), prod_singleton]
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_singleton]
  have vA : upd14 (Function.update col {D, E} d) A B C E a b c {A, E} = a := by ev14
  have vB : upd14 (Function.update col {D, E} d) A B C E a b c {B, E} = b := by ev14
  have vC : upd14 (Function.update col {D, E} d) A B C E a b c {C, E} = c := by ev14
  have vD : upd14 (Function.update col {D, E} d) A B C E a b c {D, E} = d := by ev14
  rw [vA, vB, vC, vD, triW_three _ hAB hAE hBE, triW_three _ hAC hAE hCE, triW_three _ hAD hAE hDE,
    triW_three _ hBC hBE hCE, triW_three _ hBD hBE hDE, triW_three _ hCD hCE hDE,
    M.tetW_eq_tetAmp _ (card_four hAB hAC hAE hBC hBE hCE) (p := ![B, C, A, E])
      (injective_vec4 hBC hAB.symm hBE hAC.symm hCE hAE) (fun i => by fin_cases i <;> simp),
    M.tetW_eq_tetAmp _ (card_four hAB hAD hAE hBD hBE hDE) (p := ![D, B, A, E])
      (injective_vec4 hBD.symm hAD.symm hDE hAB.symm hBE hAE) (fun i => by fin_cases i <;> simp),
    M.tetW_eq_tetAmp _ (card_four hAC hAD hAE hCD hCE hDE) (p := ![C, D, A, E])
      (injective_vec4 hCD hAC.symm hCE hAD.symm hDE hAE) (fun i => by fin_cases i <;> simp),
    M.tetW_eq_tetAmp _ (card_four hBC hBD hBE hCD hCE hDE) (p := ![B, C, D, E])
      (injective_vec4 hBC hBD hBE hCD hCE hDE) (fun i => by fin_cases i <;> simp)]
  rw [Model.term14, Function.update_self, triSign_swap _ B A E, triSign_swap _ C A E,
    triSign_swap _ D A E]
  ring

/-- **The weight under the 1-4 move** (model version): for a colour `d < N` of `DE`, summing over
the colours of `AE, BE, CE` gives `dim(d)²` times the old weight. -/
theorem weight_move14 (hBEid : M.BE) (hOrth : M.Orth) (hCount : M.Count)
    (hdim : ∀ J, J < M.N → M.dim J ≠ 0) (K : Complex3 V) {A B C D E : V}
    (h : IsMove14 K A B C D E) (col : Colouring V) {d : ℕ} (hd : d < M.N) :
    ∑ a ∈ range M.N, ∑ b ∈ range M.N, ∑ c ∈ range M.N,
      M.weight (move14 K h) (upd14 (Function.update col {D, E} d) A B C E a b c) =
      M.dim d ^ 2 * M.weight K col := by
  have hAB := h.hAB; have hAC := h.hAC; have hAD := h.hAD; have hAE := h.hAE
  have hBC := h.hBC; have hBD := h.hBD; have hBE := h.hBE; have hCD := h.hCD
  have hCE := h.hCE; have hDE := h.hDE
  have hloc := M.pachner14_local hBEid hOrth hCount hdim (Function.update col {D, E} d)
    hAB hAC hAD hAE hBC hBD hBE hCD hCE hDE (by rw [Function.update_self]; exact hd)
  have e4 : M.tetAmp (Function.update col {D, E} d) ![A, B, C, D] =
      M.tetAmp col ![A, B, C, D] := by
    rw [M.tetAmp_eq, M.tetAmp_eq (col := col)]
    ev14
  rw [Function.update_self, e4] at hloc
  simp only [M.weight_move14_eq, ← mul_sum]
  rw [hloc, Model.weight, ← mul_prod_erase _ _ h.mem,
    M.tetW_eq_tetAmp _ (card_four hAB hAC hAD hBC hBD hCD) (p := ![A, B, C, D])
      (injective_vec4 hAB hAC hAD hBC hBD hCD) (fun i => by fin_cases i <;> simp)]
  ring

lemma vertices_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    vertices (move14 K h) = insert E (vertices K) := by
  have m1 : ∀ {w}, w = A ∨ w = B ∨ w = C ∨ w = D → w ∈ vertices K := fun hw =>
    mem_biUnion.mpr ⟨_, h.mem, by rcases hw with rfl | rfl | rfl | rfl <;> simp⟩
  ext v
  constructor
  · intro hv
    obtain ⟨t, ht, hvt⟩ := mem_biUnion.mp hv
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      by_cases hvE : v = E
      · exact hvE ▸ mem_insert_self _ _
      refine mem_insert_of_mem (m1 ?_)
      rcases ht with rfl | rfl | rfl | rfl <;> simp only [id, mem_insert, mem_singleton] at hvt <;>
        tauto
    · exact mem_insert_of_mem (mem_biUnion.mpr ⟨t, mem_of_mem_erase ht, hvt⟩)
  · intro hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_biUnion.mpr ⟨{A, B, C, v}, mem_union_left _ (by simp), by simp⟩
    obtain ⟨t, ht, hvt⟩ := mem_biUnion.mp hv
    by_cases h1 : t = {A, B, C, D}
    · subst h1
      simp only [id, mem_insert, mem_singleton] at hvt
      rcases hvt with rfl | rfl | rfl | rfl
      · exact mem_biUnion.mpr ⟨{v, B, C, E}, mem_union_left _ (by simp), by simp⟩
      · exact mem_biUnion.mpr ⟨{A, v, C, E}, mem_union_left _ (by simp), by simp⟩
      · exact mem_biUnion.mpr ⟨{A, B, v, E}, mem_union_left _ (by simp), by simp⟩
      · exact mem_biUnion.mpr ⟨{A, B, v, E}, mem_union_left _ (by simp), by simp⟩
    · exact mem_biUnion.mpr ⟨t, mem_union_right _ (mem_erase.mpr ⟨h1, ht⟩), hvt⟩

lemma W_pos (hN : 0 < M.N) (hdim : ∀ J, J < M.N → M.dim J ≠ 0) : 0 < M.W :=
  sum_pos' (fun d _ => sq_nonneg _) ⟨0, mem_range.mpr hN, by
    have := hdim 0 hN; positivity⟩

/-- **The normalised state sum is invariant under the 1-4 move**, given Biedenharn–Elliott,
orthogonality and the fusion count: the new vertex's factor `W⁻¹` cancels the sum
`Σ_d dim(d)² = W` over the colour of `DE`. -/
theorem Z_move14 (hBEid : M.BE) (hOrth : M.Orth) (hCount : M.Count)
    (hdim : ∀ J, J < M.N → M.dim J ≠ 0) (hN : 0 < M.N) (K : Complex3 V) {A B C D E : V}
    (h : IsMove14 K A B C D E) : M.Z (move14 K h) = M.Z K := by
  have hK := not_mem_edges_of_fresh K h.fresh
  have hW := (M.W_pos hN hdim).ne'
  have hEv : E ∉ vertices K := fun hv => by
    obtain ⟨t, ht, hvt⟩ := mem_biUnion.mp hv
    exact h.fresh t ht hvt
  have hedges : (move14 K h).edges =
      insert {A, E} (insert {C, E} (insert {B, E} (insert {D, E} K.edges))) := by
    rw [edges_move14]
    ext s
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  have h1 : ({A, E} : Finset V) ∉ insert {C, E} (insert {B, E} (insert {D, E} K.edges)) := by
    simp only [mem_insert, not_or]
    exact ⟨by simp [pair_eq_pair_iff', h.hAC, h.hCE.symm],
      by simp [pair_eq_pair_iff', h.hAB, h.hBE.symm],
      by simp [pair_eq_pair_iff', h.hAD, h.hDE.symm], hK A⟩
  have h2 : ({C, E} : Finset V) ∉ insert {B, E} (insert {D, E} K.edges) := by
    simp only [mem_insert, not_or]
    exact ⟨by simp [pair_eq_pair_iff', h.hBC.symm, h.hBE.symm],
      by simp [pair_eq_pair_iff', h.hCD, h.hDE.symm], hK C⟩
  have h3 : ({B, E} : Finset V) ∉ insert {D, E} K.edges := by
    simp only [mem_insert, not_or]
    exact ⟨by simp [pair_eq_pair_iff', h.hBD, h.hDE.symm], hK B⟩
  have hsum : ∑ σ ∈ (move14 K h).edges.pi (fun _ => range M.N),
      M.weight (move14 K h) (extS (move14 K h).edges σ) =
      M.W * ∑ σ ∈ K.edges.pi (fun _ => range M.N), M.weight K (extS K.edges σ) := by
    calc ∑ σ ∈ (move14 K h).edges.pi (fun _ => range M.N),
          M.weight (move14 K h) (extS (move14 K h).edges σ)
        = ∑ σ ∈ (insert {A, E} (insert {C, E} (insert {B, E} (insert {D, E} K.edges)))).pi
              (fun _ => range M.N), M.weight (move14 K h)
              (extS (insert {A, E} (insert {C, E} (insert {B, E} (insert {D, E} K.edges)))) σ) := by
          rw [hedges]
      _ = ∑ σ ∈ (insert {C, E} (insert {B, E} (insert {D, E} K.edges))).pi (fun _ => range M.N),
            ∑ a ∈ range M.N, M.weight (move14 K h) (Function.update
              (extS (insert {C, E} (insert {B, E} (insert {D, E} K.edges))) σ) {A, E} a) :=
          sum_pi_insert h1 _ _
      _ = ∑ σ ∈ (insert {B, E} (insert {D, E} K.edges)).pi (fun _ => range M.N),
            ∑ c ∈ range M.N, ∑ a ∈ range M.N, M.weight (move14 K h) (Function.update
              (Function.update (extS (insert {B, E} (insert {D, E} K.edges)) σ) {C, E} c)
              {A, E} a) :=
          sum_pi_insert h2 _ (fun col => ∑ a ∈ range M.N,
            M.weight (move14 K h) (Function.update col {A, E} a))
      _ = ∑ σ ∈ (insert {D, E} K.edges).pi (fun _ => range M.N),
            ∑ b ∈ range M.N, ∑ c ∈ range M.N, ∑ a ∈ range M.N, M.weight (move14 K h)
              (Function.update (Function.update (Function.update
                (extS (insert {D, E} K.edges) σ) {B, E} b) {C, E} c) {A, E} a) :=
          sum_pi_insert h3 _ (fun col => ∑ c ∈ range M.N, ∑ a ∈ range M.N,
            M.weight (move14 K h) (Function.update (Function.update col {C, E} c) {A, E} a))
      _ = ∑ σ ∈ K.edges.pi (fun _ => range M.N), ∑ d ∈ range M.N,
            ∑ b ∈ range M.N, ∑ c ∈ range M.N, ∑ a ∈ range M.N, M.weight (move14 K h)
              (upd14 (Function.update (extS K.edges σ) {D, E} d) A B C E a b c) :=
          sum_pi_insert (hK D) _ (fun col => ∑ b ∈ range M.N, ∑ c ∈ range M.N,
            ∑ a ∈ range M.N, M.weight (move14 K h)
              (Function.update (Function.update (Function.update col {B, E} b) {C, E} c)
                {A, E} a))
      _ = ∑ σ ∈ K.edges.pi (fun _ => range M.N), ∑ d ∈ range M.N,
            M.dim d ^ 2 * M.weight K (extS K.edges σ) := by
          refine sum_congr rfl fun σ _ => sum_congr rfl fun d hd => ?_
          rw [← M.weight_move14 hBEid hOrth hCount hdim K h _ (mem_range.mp hd)]
          exact (sum_congr rfl fun b _ => sum_comm).trans sum_comm
      _ = M.W * ∑ σ ∈ K.edges.pi (fun _ => range M.N), M.weight K (extS K.edges σ) := by
          rw [mul_sum]
          exact sum_congr rfl fun σ _ => by rw [← sum_mul, W]
  rw [Z, Z, hsum, vertices_move14, card_insert_of_notMem hEv, pow_succ]
  field_simp

end Model




end Lightlike.TV
