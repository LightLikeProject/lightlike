import Mathlib
import Lightlike.Regge.Conv3.JetCurvature
import Lightlike.Geometry.HeatKernel.PartialJets

/-!
# The scalar curvature in the invariants of the 2-jet of the metric

At a point, with `H = g⁻¹`, `D_{abc} = ∂_a g_{bc}` and `E_{abcd} = ∂_a ∂_b g_{cd}`, every full contraction of the jet that is
linear in `E` or quadratic in `D` is a combination of seven invariants: `jetA1`, `jetA2` (linear in `E`) and `jetQ1` … `jetQ5`
(quadratic in `D`). This file proves `scalarCurvature_eq_jetInv`:
`R = -A₁ + A₂ + ¾ Q₁ - ¼ Q₂ + Q₃ - Q₄ - ½ Q₅` for a coordinate metric of any signature.

The tool is a reindexing of nested sums over coordinate indices: `sum_nest4`, `sum_nest6` turn a nested sum into one sum
over `Fin k → Fin n`, `sum_reindex` reindexes it by a permutation of the positions, and with the entries of the symmetric
arrays read at `(min, max)` (`symm_minmax`) each monomial of the expanded curvature is identified with its invariant.

Numerical evidence (not proof): the decomposition, checked in exact rational arithmetic against the library's Christoffel
and Riemann conventions for random 2-jets in dimensions 3 and 4 (10/10 each).
-/

open Finset

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- A sum over `Fin (k + 1) → α` splits off its first coordinate. -/
lemma sum_fin_succ_pi {α : Type*} [Fintype α] {k : ℕ} (F : (Fin (k + 1) → α) → ℝ) :
    ∑ x, F x = ∑ a, ∑ y : Fin k → α, F (Fin.cons a y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm

/-- **A four-fold nested sum as one sum** over `Fin 4 → Fin n`. -/
lemma sum_nest4 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ x : Fin 4 → Fin n, F (x 0) (x 1) (x 2) (x 3) := by
  simp only [sum_fin_succ_pi, Fin.cons_zero]
  simp
  rfl

/-- **A six-fold nested sum as one sum** over `Fin 6 → Fin n`. -/
lemma sum_nest6 (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f =
      ∑ x : Fin 6 → Fin n, F (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  simp only [sum_fin_succ_pi, Fin.cons_zero]
  simp
  rfl

/-- **Reindexing by a permutation of the positions.** -/
lemma sum_reindex {k : ℕ} (F G : (Fin k → Fin n) → ℝ) (π : Equiv.Perm (Fin k)) (h : ∀ x, F (x ∘ π) = G x) :
    ∑ x, F x = ∑ x, G x := by
  rw [← Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl (Fin n))) F G]
  intro x
  rw [show (Equiv.arrowCongr π (Equiv.refl (Fin n))) x = x ∘ π.symm from rfl, ← h]
  congr 1
  funext i
  simp

/-- A symmetric array read at `(min i j, max i j)`. -/
lemma symm_minmax {β : Type*} {A : Fin n → Fin n → β} (hA : ∀ i j, A i j = A j i) (i j : Fin n) :
    A i j = A (min i j) (max i j) := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, hA]

/-- The jet invariant `H^{ad} tr(D_a H D_d H)`. -/
def jetQ1 (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * D (x 0) (x 2) (x 3) * H (x 3) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 2)

/-- The jet invariant `H^{ad} v_a v_d` with `v_a = H^{bc} D_{abc}`. -/
def jetQ2 (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * D (x 0) (x 2) (x 3) * H (x 4) (x 5) * D (x 1) (x 4) (x 5)

/-- The jet invariant `H^{cd} w_c v_d` with `w_c = H^{ab} D_{abc}`. -/
def jetQ3 (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * D (x 2) (x 3) (x 0) * H (x 4) (x 5) * D (x 1) (x 4) (x 5)

/-- The jet invariant `H^{cf} w_c w_f`. -/
def jetQ4 (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * D (x 2) (x 3) (x 0) * H (x 4) (x 5) * D (x 4) (x 5) (x 1)

/-- The jet invariant `D_{abc} D_{def} H^{ae} H^{bd} H^{cf}`. -/
def jetQ5 (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 6 → Fin n, D (x 0) (x 1) (x 2) * D (x 3) (x 4) (x 5) * H (x 0) (x 4) * H (x 1) (x 3) * H (x 2) (x 5)

/-- The jet invariant `H^{ab} H^{cd} E_{abcd}`. -/
def jetA1 (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 0) (x 1) (x 2) (x 3)

/-- The jet invariant `H^{ac} H^{bd} E_{abcd}`. -/
def jetA2 (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin 4 → Fin n, H (x 0) (x 2) * H (x 1) (x 3) * E (x 0) (x 1) (x 2) (x 3)

/-- The quadratic part of the scalar-curvature integrand of `scalarCurvature_jet`, at the summation indices
`σ ν ρ l a b`. -/
def rQuad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (s v r l a b : Fin n) : ℝ :=
  -(1 / 2) * (H s v * (H r a * D r a b * H b l) * (D v l s + D s l v - D l v s)) +
    1 / 2 * (H s v * (H r a * D v a b * H b l) * (D r l s + D s l r - D l r s)) +
    1 / 4 * (H s v * (H r a * (D r a l + D l a r - D a r l)) * (H l b * (D v b s + D s b v - D b v s))) -
    1 / 4 * (H s v * (H r a * (D v a l + D l a v - D a v l)) * (H l b * (D r b s + D s b r - D b r s)))

/-- The linear part of the scalar-curvature integrand of `scalarCurvature_jet`, at the summation indices `σ ν ρ l`. -/
def rLin (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (s v r l : Fin n) : ℝ :=
  1 / 2 * (H s v * H r l * (E r v l s + E r s l v - E r l v s)) -
    1 / 2 * (H s v * H r l * (E v r l s + E v s l r - E v l r s))

/-- **The quadratic part of the scalar curvature in the jet invariants.** -/
theorem sum_rQuad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hD : ∀ a b c, D a b c = D a c b) :
    ∑ x : Fin 6 → Fin n, rQuad H D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) =
      3 / 4 * jetQ1 H D - 1 / 4 * jetQ2 H D + jetQ3 H D - jetQ4 H D - 1 / 2 * jetQ5 H D := by
  have hHs : H = fun i j => H (min i j) (max i j) := funext fun i => funext fun j => symm_minmax hH i j
  have hDs : D = fun a b c => D a (min b c) (max b c) :=
    funext fun a => funext fun b => funext fun c => symm_minmax (A := D a) (hD a) b c
  have e : ∀ x : Fin 6 → Fin n, rQuad H D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 1) (x 3) (x 0)) + (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 0) (x 3) (x 1)) + (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 3) (x 1) (x 0)) + (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 2) (x 3) (x 0)) + (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 0) (x 3) (x 2)) + (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 3) (x 2) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 1) (x 5) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 1)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 5) (x 1) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 1) (x 5) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 0) (x 5) (x 1)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 5) (x 1) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 1) (x 5) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 1)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 5) (x 1) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 2) (x 5) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 2)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 5) (x 2) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 2) (x 5) (x 0)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 0) (x 5) (x 2)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 5) (x 2) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 2) (x 5) (x 0)) + (1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 2)) + (-1 / 4 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 5) (x 2) (x 0)) := by
    intro x; unfold rQuad; ring
  rw [Finset.sum_congr rfl fun x _ => e x]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 1) (x 3) (x 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 0, 5, 1], ![3, 5, 1, 0, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h1 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 0) (x 3) (x 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 0, 5, 1], ![3, 5, 0, 1, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h2 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 5) * H (x 5) (x 3) * D (x 3) (x 1) (x 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 2, 1, 3, 0], ![5, 3, 2, 4, 0, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h3 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 2) (x 3) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 2, 4, 5], ![2, 0, 3, 1, 4, 5], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h4 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 0) (x 3) (x 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 3, 5, 4], ![0, 1, 2, 3, 5, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h5 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 5) * H (x 5) (x 3) * D (x 3) (x 2) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 2, 0, 5, 4], ![3, 0, 2, 1, 5, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h6 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 1) (x 5) (x 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 1, 5, 0], ![5, 3, 1, 0, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h7 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 1, 5, 0], ![5, 3, 0, 1, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h8 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 2) (x 4) (x 3) * H (x 3) (x 5) * D (x 5) (x 1) (x 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 2, 0, 3, 1], ![3, 5, 2, 4, 0, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h9 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 1) (x 5) (x 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 1, 5, 0], ![5, 3, 1, 0, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h10 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 0) (x 5) (x 1) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 1, 5, 0], ![5, 3, 0, 1, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h11 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 2) * H (x 3) (x 5) * D (x 5) (x 1) (x 0) = jetQ2 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 1, 5, 0], ![5, 3, 0, 1, 2, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h12 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 1) (x 5) (x 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 1, 4, 0], ![5, 3, 1, 0, 4, 2], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h13 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 1, 4, 0], ![5, 3, 0, 1, 4, 2], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h14 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 2) (x 3) * H (x 3) (x 5) * D (x 5) (x 1) (x 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 3, 0, 2, 1], ![3, 5, 4, 2, 0, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h15 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 2) (x 5) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 5, 4, 2], ![2, 0, 5, 1, 4, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h16 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 4, 5, 3], ![0, 1, 2, 5, 3, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h17 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 1) (x 4) (x 3) * H (x 3) (x 5) * D (x 5) (x 2) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 2, 4, 5, 0], ![5, 0, 2, 1, 3, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h18 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 2) (x 5) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 3, 4, 1], ![2, 5, 0, 3, 4, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h19 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 0) (x 5) (x 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 2, 3, 5, 1], ![0, 5, 2, 3, 1, 4], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h20 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 3) (x 4) (x 1) * H (x 3) (x 5) * D (x 5) (x 2) (x 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 1, 4, 0], ![5, 3, 0, 2, 4, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h21 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 2) (x 5) (x 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 4, 1, 3], ![2, 4, 0, 5, 3, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h22 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 0) (x 5) (x 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 5, 3, 2], ![0, 2, 5, 4, 1, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  have h23 : ∑ x : Fin 6 → Fin n, H (x 0) (x 1) * H (x 2) (x 4) * D (x 4) (x 1) (x 3) * H (x 3) (x 5) * D (x 5) (x 2) (x 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 4, 3, 0], ![5, 2, 0, 4, 3, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hDs]
    simp only [min_comm, max_comm]
    try ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
  ring

/-- **The linear part of the scalar curvature in the jet invariants.** -/
theorem sum_rLin (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ x : Fin 4 → Fin n, rLin H E (x 0) (x 1) (x 2) (x 3) = -jetA1 H E + jetA2 H E := by
  have hHs : H = fun i j => H (min i j) (max i j) := funext fun i => funext fun j => symm_minmax hH i j
  have hEs : E = fun a b c d => E (min a b) (max a b) (min c d) (max c d) := by
    funext a b c d
    rw [symm_minmax (A := fun a b => E a b c d) (fun a b => hE1 a b c d) a b,
      symm_minmax (A := E (min a b) (max a b)) (hE2 _ _) c d]
  have e : ∀ x : Fin 4 → Fin n, rLin H E (x 0) (x 1) (x 2) (x 3) = (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 1) (x 3) (x 0)) + (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 0) (x 3) (x 1)) + (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 3) (x 1) (x 0)) + (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 2) (x 3) (x 0)) + (-1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 0) (x 3) (x 2)) + (1 / 2 : ℝ) * (H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 3) (x 2) (x 0)) := by
    intro x; unfold rLin; ring
  rw [Finset.sum_congr rfl fun x _ => e x]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 1) (x 3) (x 0) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
  have h1 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 0) (x 3) (x 1) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
  have h2 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 2) (x 3) (x 1) (x 0) = jetA1 H E := by
    refine sum_reindex _ _ ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
    try ring
  have h3 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 2) (x 3) (x 0) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
  have h4 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 0) (x 3) (x 2) = jetA1 H E := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 3], ![0, 1, 2, 3], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
  have h5 : ∑ x : Fin 4 → Fin n, H (x 0) (x 1) * H (x 2) (x 3) * E (x 1) (x 3) (x 2) (x 0) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩ fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [hHs, hEs]
    simp only [min_comm, max_comm]
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- The Christoffel symbol `Γ^ρ_{μl}` of a jet `(H, D)`: `½ Σₖ H^{ρk} (D_{μkl} + D_{lkμ} - D_{kμl})`. -/
def chrJ (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (ρ μ l : Fin n) : ℝ :=
  1 / 2 * ∑ k, H ρ k * (D μ k l + D l k μ - D k μ l)

/-- The derivative `∂_μ Γ^ρ_{νσ}` of the Christoffel symbols of a jet `(H, D, E)`, as in `Regge.Conv3.dChr`. -/
def dChrJ (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ)
    (μ ρ ν σ : Fin n) : ℝ :=
  1 / 2 * ∑ l, ((-∑ i, ∑ r, H ρ i * D μ i r * H r l) * (D ν l σ + D σ l ν - D l ν σ) +
    H ρ l * (E μ ν l σ + E μ σ l ν - E μ l ν σ))

/-- The scalar curvature of a jet `(H, D, E)`, as in `Regge.Conv3.scalarCurvature_jet`. -/
def scalJ' (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, H σ ν * ∑ ρ, (dChrJ H D E ρ ρ ν σ - dChrJ H D E ν ρ ρ σ +
    ∑ l, (chrJ H D ρ ρ l * chrJ H D l ν σ - chrJ H D ρ ν l * chrJ H D l ρ σ))

/-- A product of two Christoffel symbols as a double sum. -/
lemma mul_chrJ (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (c : ℝ) (ρ μ l l' μ' σ : Fin n) :
    c * (chrJ H D ρ μ l * chrJ H D l' μ' σ) = ∑ a, ∑ b, c / 4 * (H ρ a * (D μ a l + D l a μ - D a μ l)) *
      (H l' b * (D μ' b σ + D σ b μ' - D b μ' σ)) := by
  unfold chrJ
  rw [show ∀ X Y : ℝ, c * (1 / 2 * X * (1 / 2 * Y)) = c / 4 * (X * Y) from fun _ _ => by ring,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The quadratic part of a derivative of the Christoffel symbols as a double sum. -/
lemma mul_dChrJ_quad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (c : ℝ) (μ ρ ν σ l : Fin n) :
    c * ((-∑ i, ∑ r, H ρ i * D μ i r * H r l) * (D ν l σ + D σ l ν - D l ν σ)) =
      ∑ a, ∑ b, -c * (H ρ a * D μ a b * H b l) * (D ν l σ + D σ l ν - D l ν σ) := by
  simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

/-- **The scalar curvature of a jet is the sum of the linear and the quadratic integrands.** -/
theorem scalJ'_eq_sum (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (E : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scalJ' H D E = ∑ x : Fin 4 → Fin n, rLin H E (x 0) (x 1) (x 2) (x 3) +
      ∑ x : Fin 6 → Fin n, rQuad H D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  rw [← sum_nest4, ← sum_nest6]
  simp only [← Finset.sum_add_distrib]
  unfold scalJ'
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold dChrJ
  have e1 : ∀ F : Fin n → ℝ, H s v * (1 / 2 * ∑ l, F l) = ∑ l, H s v * (1 / 2) * F l := fun F => by
    rw [← mul_assoc, Finset.mul_sum]
  rw [show ∀ x y z w : ℝ, w * (x - y + z) = w * x - w * y + w * z from fun _ _ _ _ => by ring,
    e1, e1, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have q1 := mul_dChrJ_quad H D (H s v * (1 / 2)) r r v s l
  have q2 := mul_dChrJ_quad H D (H s v * (1 / 2)) v r r s l
  have q3 := mul_chrJ H D (H s v) r r l l v s
  have q4 := mul_chrJ H D (H s v) r v l l r s
  have hq : ∑ a, ∑ b, rQuad H D s v r l a b =
      (∑ a, ∑ b, -(H s v * (1 / 2)) * (H r a * D r a b * H b l) * (D v l s + D s l v - D l v s)) -
      (∑ a, ∑ b, -(H s v * (1 / 2)) * (H r a * D v a b * H b l) * (D r l s + D s l r - D l r s)) +
      (∑ a, ∑ b, H s v / 4 * (H r a * (D r a l + D l a r - D a r l)) * (H l b * (D v b s + D s b v - D b v s))) -
      (∑ a, ∑ b, H s v / 4 * (H r a * (D v a l + D l a v - D a v l)) * (H l b * (D r b s + D s b r - D b r s))) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    unfold rQuad
    ring
  rw [hq]
  unfold rLin
  linear_combination q1 - q2 + q3 - q4

/-- **The scalar curvature in the jet invariants** (L-R): at a point `m` of a coordinate metric of any signature, with
`H = g(m)⁻¹`, `D_{abc} = ∂_a g_{bc}(m)` and `E_{abcd} = ∂_a ∂_b g_{cd}(m)`,
`R = -A₁ + A₂ + ¾ Q₁ - ¼ Q₂ + Q₃ - Q₄ - ½ Q₅`. -/
theorem scalarCurvature_eq_jetInv {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) :
    scalarCurvature g m =
      -jetA1 (fun i j => (g m)⁻¹ i j) (fun a b c d => pd a (fun y => pd b (fun z => g z c d) y) m) +
        jetA2 (fun i j => (g m)⁻¹ i j) (fun a b c d => pd a (fun y => pd b (fun z => g z c d) y) m) +
        3 / 4 * jetQ1 (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m) -
        1 / 4 * jetQ2 (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m) +
        jetQ3 (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m) -
        jetQ4 (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m) -
        1 / 2 * jetQ5 (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m) := by
  have hU := hg.isOpen
  have hgs : ∀ y ∈ U, ∀ b c, g y b c = g y c b := fun y hy b c => by
    have := congrFun (congrFun (hg.symm y hy) c) b
    rwa [Matrix.transpose_apply] at this
  have hH : ∀ i j, (g m)⁻¹ i j = (g m)⁻¹ j i := fun i j => by
    have hsymi : ((g m)⁻¹).transpose = (g m)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm m hm]
    have := congrFun (congrFun hsymi j) i
    rwa [Matrix.transpose_apply] at this
  have hD : ∀ a b c, pd a (fun y => g y b c) m = pd a (fun y => g y c b) m := fun a b c =>
    pd_congr_on hU hm (fun y hy => hgs y hy b c) a
  have hE1 : ∀ a b c d, pd a (fun y => pd b (fun z => g z c d) y) m = pd b (fun y => pd a (fun z => g z c d) y) m :=
    fun a b c d => pd_pd_comm (hg.smooth c d) hU hm a b
  have hE2 : ∀ a b c d, pd a (fun y => pd b (fun z => g z c d) y) m = pd a (fun y => pd b (fun z => g z d c) y) m :=
    fun a b c d => pd_congr_on hU hm (fun y hy => pd_congr_on hU hy (fun z hz => hgs z hz c d) b) a
  rw [Regge.Conv3.scalarCurvature_jet hg hm]
  change scalJ' (fun i j => (g m)⁻¹ i j) (fun a b c => pd a (fun y => g y b c) m)
    (fun a b c d => pd a (fun y => pd b (fun z => g z c d) y) m) = _
  rw [scalJ'_eq_sum, sum_rLin _ _ hH hE1 hE2, sum_rQuad _ _ hH hD]
  ring

end Lightlike
