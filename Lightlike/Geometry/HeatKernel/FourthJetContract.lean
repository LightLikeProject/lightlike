import Mathlib
import Lightlike.Geometry.HeatKernel.JetInvariants

/-!
# The contracted order-four eikonal identity in the jet invariants

Pure algebra over a jet `(H, D, E)` with the symmetries of `g⁻¹`, `∂g`, `∂∂g`, a third-order array `T` given by the third
derivatives of the world function (`T_{xyz} = D_{xyz} + D_{yzx} + D_{zxy}`, `thirdJet`) and a symmetric fourth-order array
`S4`. If the 58 terms of the order-four eikonal identity (`eikonal_fourth`) hold at every index, the full contraction
`T4 = H^{ab} H^{cd} S4_{abcd}` is `4/3 A₁ + 8/3 A₂ - Q₁ - 1/6 Q₂ + 2/3 Q₃ - 2/3 Q₄ + 2/3 Q₅` (`sum_T4_alg`). Each term
of the identity, contracted with `H^{ab} H^{cd}`, is identified with its invariants by reindexing (`contr_*`, generated).

Numerical evidence (not proof): the value of `T4`, checked in exact rational arithmetic from the eikonal equation solved
to degree four, for random 2-jets in dimensions 3 and 4.
-/

open Finset

noncomputable section

namespace Lightlike

variable {n : ℕ}

-- The generated per-monomial proofs end with a uniform `first | done | ring`; some monomials close earlier.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- A symmetric matrix of functions read at `(min, max)`. -/
lemma symm_fun2 {H : Fin n → Fin n → ℝ} (hH : ∀ i j, H i j = H j i) : H = fun i j => H (min i j) (max i j) :=
  funext fun i => funext fun j => symm_minmax hH i j

/-- An array symmetric in its last two slots read at `(min, max)` there. -/
lemma symm_fun3 {D : Fin n → Fin n → Fin n → ℝ} (hD : ∀ a b c, D a b c = D a c b) :
    D = fun a b c => D a (min b c) (max b c) :=
  funext fun a => funext fun b => funext fun c => symm_minmax (A := D a) (hD a) b c

/-- An array symmetric in its first and in its last two slots read at `(min, max)` in both pairs. -/
lemma symm_fun4 {E : Fin n → Fin n → Fin n → Fin n → ℝ} (hE1 : ∀ a b c d, E a b c d = E b a c d)
    (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    E = fun a b c d => E (min a b) (max a b) (min c d) (max c d) := by
  funext a b c d
  rw [symm_minmax (A := fun a b => E a b c d) (fun a b => hE1 a b c d) a b,
    symm_minmax (A := E (min a b) (max a b)) (hE2 _ _) c d]

/-- A constant factor out of a four-fold sum. -/
lemma sum4_mul_const (X Y : Fin n → Fin n → Fin n → Fin n → ℝ) (k : ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, X a b c d * (k * Y a b c d) = k * ∑ a, ∑ b, ∑ c, ∑ d, X a b c d * Y a b c d := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

set_option hygiene false in
/-- Evaluate a reindexed monomial and normalize the symmetric arrays `H`, `D`. -/
local macro "jet_normD" : tactic => `(tactic| (
  simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue]
  all_goals rw [hHs, hDs]
  all_goals simp only [min_comm, max_comm]
  all_goals ring))

set_option hygiene false in
/-- Evaluate a reindexed monomial and normalize the symmetric arrays `H`, `E`. -/
local macro "jet_normE" : tactic => `(tactic| (
  simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue]
  all_goals rw [hHs, hEs]
  all_goals simp only [min_comm, max_comm]
  all_goals ring))

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_acbd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a c i * H i j * D b j d) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a c i * H i j * D b j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a c i * H i j * D b j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a c i * H i j * D b j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 2) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 4, 3], ![0, 1, 2, 5, 4, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_bcad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b c i * H i j * D a j d) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b c i * H i j * D a j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b c i * H i j * D a j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b c i * H i j * D a j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 2) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 2, 5], ![0, 1, 4, 3, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_abcd (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a b c d = (1 : ℝ) * jetA1 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a b c d)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 2) (y 3) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 2) (y 3)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 2) (y 3) = jetA1 H E := rfl
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_adbc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a d i * H i j * D b j c) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a d i * H i j * D b j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a d i * H i j * D b j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a d i * H i j * D b j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 3) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 5, 2], ![0, 1, 5, 3, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_bdac (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b d i * H i j * D a j c) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b d i * H i j * D a j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b d i * H i j * D a j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b d i * H i j * D a j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 3) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_abdc (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a b d c = (1 : ℝ) * jetA1 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a b d c)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 3) (y 2) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 3) (y 2)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 1) (y 3) (y 2) = jetA1 H E := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 3], ![0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_abcd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a b i * H i j * D c j d) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a b i * H i j * D c j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a b i * H i j * D c j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a b i * H i j * D c j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 1) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 3) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cbad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c b i * H i j * D a j d) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c b i * H i j * D a j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c b i * H i j * D a j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c b i * H i j * D a j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 1) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 2, 5], ![0, 3, 4, 2, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_acbd (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a c b d = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a c b d)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 1) (y 3) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 1) (y 3)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 1) (y 3) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_adcb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a d i * H i j * D c j b) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a d i * H i j * D c j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a d i * H i j * D c j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a d i * H i j * D c j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 3) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 5, 2], ![0, 3, 5, 2, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cdab (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c d i * H i j * D a j b) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c d i * H i j * D a j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c d i * H i j * D a j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c d i * H i j * D a j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 3) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_acdb (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a c d b = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a c d b)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 3) (y 1) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 3) (y 1)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 2) (y 3) (y 1) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_abdc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a b i * H i j * D d j c) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a b i * H i j * D d j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a b i * H i j * D d j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a b i * H i j * D d j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 1) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 1, 0], ![5, 4, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dbac (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d b i * H i j * D a j c) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d b i * H i j * D a j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d b i * H i j * D a j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d b i * H i j * D a j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 1) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 2, 5], ![0, 2, 4, 3, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_adbc (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a d b c = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a d b c)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 1) (y 2) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 1) (y 2)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 1) (y 2) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_acdb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a c i * H i j * D d j b) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D a c i * H i j * D d j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D a c i * H i j * D d j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D a c i * H i j * D d j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 2) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 5, 2], ![0, 2, 5, 3, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dcab (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d c i * H i j * D a j b) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d c i * H i j * D a j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d c i * H i j * D a j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d c i * H i j * D a j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 2) (y 5) * H (y 5) (y 4) * D (y 0) (y 4) (y 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 0, 1], ![4, 5, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_adcb (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E a d c b = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E a d c b)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 2) (y 1) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 2) (y 1)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 0) (y 3) (y 2) (y 1) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_bcad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b c x * ∑ i, H x i * D a i d) = (1 : ℝ) * jetQ1 H D + (2 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b c x * ∑ i, H x i * D a i d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D b c x * H x i * D a i d) + (1 : ℝ) * (H a b * H c d * D c x b * H x i * D a i d) + (1 : ℝ) * (H a b * H c d * D x b c * H x i * D a i d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D b c x * H x i * D a i d) + (1 : ℝ) * (H a b * H c d * D c x b * H x i * D a i d) + (1 : ℝ) * (H a b * H c d * D x b c * H x i * D a i d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 2) (y 4) * H (y 4) (y 5) * D (y 0) (y 5) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 5, 2], ![0, 1, 5, 3, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 4) (y 1) * H (y 4) (y 5) * D (y 0) (y 5) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 5, 2], ![0, 3, 5, 2, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 1) (y 2) * H (y 4) (y 5) * D (y 0) (y 5) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 5, 2, 3, 1], ![0, 5, 3, 4, 1, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_bdac (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b d x * ∑ i, H x i * D a i c) = (1 : ℝ) * jetQ1 H D + (2 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b d x * ∑ i, H x i * D a i c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D b d x * H x i * D a i c) + (1 : ℝ) * (H a b * H c d * D d x b * H x i * D a i c) + (1 : ℝ) * (H a b * H c d * D x b d * H x i * D a i c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D b d x * H x i * D a i c) + (1 : ℝ) * (H a b * H c d * D d x b * H x i * D a i c) + (1 : ℝ) * (H a b * H c d * D x b d * H x i * D a i c))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 3) (y 4) * H (y 4) (y 5) * D (y 0) (y 5) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 4, 3], ![0, 1, 2, 5, 4, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 1) * H (y 4) (y 5) * D (y 0) (y 5) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 5, 2], ![0, 2, 5, 3, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 1) (y 3) * H (y 4) (y 5) * D (y 0) (y 5) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 2, 5, 3, 1], ![0, 5, 2, 4, 1, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_cdab (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T c d x * ∑ i, H x i * D a i b) = (2 : ℝ) * jetQ4 H D + (1 : ℝ) * jetQ3 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T c d x * ∑ i, H x i * D a i b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D c d x * H x i * D a i b) + (1 : ℝ) * (H a b * H c d * D d x c * H x i * D a i b) + (1 : ℝ) * (H a b * H c d * D x c d * H x i * D a i b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D c d x * H x i * D a i b) + (1 : ℝ) * (H a b * H c d * D d x c * H x i * D a i b) + (1 : ℝ) * (H a b * H c d * D x c d * H x i * D a i b))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 3) (y 4) * H (y 4) (y 5) * D (y 0) (y 5) (y 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 2) * H (y 4) (y 5) * D (y 0) (y 5) (y 1) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 1, 0], ![5, 4, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 5) (y 1) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_bacd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b a i * H i j * D c j d) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b a i * H i j * D c j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b a i * H i j * D c j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b a i * H i j * D c j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 0) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 3) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cabd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c a i * H i j * D b j d) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c a i * H i j * D b j d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c a i * H i j * D b j d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c a i * H i j * D b j d))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 0) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 5, 2], ![2, 0, 5, 1, 3, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_bcad (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E b c a d = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E b c a d)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 0) (y 3) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 0) (y 3)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 0) (y 3) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_bdca (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b d i * H i j * D c j a) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b d i * H i j * D c j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b d i * H i j * D c j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b d i * H i j * D c j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 3) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 2, 5], ![2, 0, 4, 1, 3, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cdba (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c d i * H i j * D b j a) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c d i * H i j * D b j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c d i * H i j * D b j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c d i * H i j * D b j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 3) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 0, 1], ![4, 5, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_bcda (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E b c d a = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E b c d a)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 3) (y 0) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 3) (y 0)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 2) (y 3) (y 0) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_badc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b a i * H i j * D d j c) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b a i * H i j * D d j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b a i * H i j * D d j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b a i * H i j * D d j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 0) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 1, 0], ![5, 4, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dabc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d a i * H i j * D b j c) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d a i * H i j * D b j c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d a i * H i j * D b j c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d a i * H i j * D b j c))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 0) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 5, 2], ![3, 0, 5, 1, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_bdac (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E b d a c = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E b d a c)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 0) (y 2) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 0) (y 2)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 0) (y 2) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_bcda (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b c i * H i j * D d j a) = (1 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D b c i * H i j * D d j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D b c i * H i j * D d j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D b c i * H i j * D d j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 2) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 2, 5], ![3, 0, 4, 1, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dcba (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d c i * H i j * D b j a) = (1 : ℝ) * jetQ4 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d c i * H i j * D b j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d c i * H i j * D b j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d c i * H i j * D b j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 2) (y 5) * H (y 5) (y 4) * D (y 1) (y 4) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 0, 1], ![4, 5, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_bdca (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E b d c a = (1 : ℝ) * jetA2 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E b d c a)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 2) (y 0) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 2) (y 0)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 1) (y 3) (y 2) (y 0) = jetA2 H E := by
    refine sum_reindex _ _ ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_acbd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a c x * ∑ i, H x i * D b i d) = (1 : ℝ) * jetQ1 H D + (2 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a c x * ∑ i, H x i * D b i d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a c x * H x i * D b i d) + (1 : ℝ) * (H a b * H c d * D c x a * H x i * D b i d) + (1 : ℝ) * (H a b * H c d * D x a c * H x i * D b i d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a c x * H x i * D b i d) + (1 : ℝ) * (H a b * H c d * D c x a * H x i * D b i d) + (1 : ℝ) * (H a b * H c d * D x a c * H x i * D b i d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 2) (y 4) * H (y 4) (y 5) * D (y 1) (y 5) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 4) (y 0) * H (y 4) (y 5) * D (y 1) (y 5) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 2, 5], ![2, 0, 4, 1, 3, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 2) * H (y 4) (y 5) * D (y 1) (y 5) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 2, 5, 0, 4], ![4, 0, 2, 1, 5, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_adbc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a d x * ∑ i, H x i * D b i c) = (1 : ℝ) * jetQ1 H D + (2 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a d x * ∑ i, H x i * D b i c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a d x * H x i * D b i c) + (1 : ℝ) * (H a b * H c d * D d x a * H x i * D b i c) + (1 : ℝ) * (H a b * H c d * D x a d * H x i * D b i c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a d x * H x i * D b i c) + (1 : ℝ) * (H a b * H c d * D d x a * H x i * D b i c) + (1 : ℝ) * (H a b * H c d * D x a d * H x i * D b i c))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 3) (y 4) * H (y 4) (y 5) * D (y 1) (y 5) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 2, 5], ![0, 1, 4, 3, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 0) * H (y 4) (y 5) * D (y 1) (y 5) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 2, 5], ![3, 0, 4, 1, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 3) * H (y 4) (y 5) * D (y 1) (y 5) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 5, 2, 0, 4], ![4, 0, 3, 1, 5, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_cdba (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T c d x * ∑ i, H x i * D b i a) = (2 : ℝ) * jetQ4 H D + (1 : ℝ) * jetQ3 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T c d x * ∑ i, H x i * D b i a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D c d x * H x i * D b i a) + (1 : ℝ) * (H a b * H c d * D d x c * H x i * D b i a) + (1 : ℝ) * (H a b * H c d * D x c d * H x i * D b i a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D c d x * H x i * D b i a) + (1 : ℝ) * (H a b * H c d * D d x c * H x i * D b i a) + (1 : ℝ) * (H a b * H c d * D x c d * H x i * D b i a))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 3) (y 4) * H (y 4) (y 5) * D (y 1) (y 5) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 2) * H (y 4) (y 5) * D (y 1) (y 5) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 1, 0], ![5, 4, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 5) (y 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cadb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c a i * H i j * D d j b) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c a i * H i j * D d j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c a i * H i j * D d j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c a i * H i j * D d j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 0) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 4, 3], ![2, 3, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dacb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d a i * H i j * D c j b) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d a i * H i j * D c j b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d a i * H i j * D c j b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d a i * H i j * D c j b))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 0) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 4, 3], ![3, 2, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_cdab (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E c d a b = (1 : ℝ) * jetA1 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E c d a b)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 0) (y 1) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 0) (y 1)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 0) (y 1) = jetA1 H E := by
    refine sum_reindex _ _ ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_cbda (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c b i * H i j * D d j a) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D c b i * H i j * D d j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D c b i * H i j * D d j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D c b i * H i j * D d j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 1) (y 5) * H (y 5) (y 4) * D (y 3) (y 4) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 3, 4], ![3, 2, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_alp_dbca (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d b i * H i j * D c j a) = (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ j, ∑ i, D d b i * H i j * D c j a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, ∑ i, ((1 : ℝ) * (H a b * H c d * D d b i * H i j * D c j a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, sum_nest6 (fun a b c d j i => (1 : ℝ) * (H a b * H c d * D d b i * H i j * D c j a))]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 1) (y 5) * H (y 5) (y 4) * D (y 2) (y 4) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 3, 4], ![2, 3, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_E_cdba (H : Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hE1 : ∀ a b c d, E a b c d = E b a c d) (hE2 : ∀ a b c d, E a b c d = E a b d c) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * E c d b a = (1 : ℝ) * jetA1 H E := by
  have hHs := symm_fun2 hH
  have hEs := symm_fun4 hE1 hE2
  rw [sum_nest4 (fun a b c d => H a b * H c d * E c d b a)]
  have e : ∀ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 1) (y 0) = (1 : ℝ) * (H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 1) (y 0)) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y]
  simp only [← Finset.mul_sum]
  have h0 : ∑ y : Fin 4 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * E (y 2) (y 3) (y 1) (y 0) = jetA1 H E := by
    refine sum_reindex _ _ ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normE
  rw [h0]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_abcd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a b x * ∑ i, H x i * D c i d) = (2 : ℝ) * jetQ4 H D + (1 : ℝ) * jetQ3 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a b x * ∑ i, H x i * D c i d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a b x * H x i * D c i d) + (1 : ℝ) * (H a b * H c d * D b x a * H x i * D c i d) + (1 : ℝ) * (H a b * H c d * D x a b * H x i * D c i d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a b x * H x i * D c i d) + (1 : ℝ) * (H a b * H c d * D b x a * H x i * D c i d) + (1 : ℝ) * (H a b * H c d * D x a b * H x i * D c i d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 1) (y 4) * H (y 4) (y 5) * D (y 2) (y 5) (y 3) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 4) (y 0) * H (y 4) (y 5) * D (y 2) (y 5) (y 3) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 0, 1], ![4, 5, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 1) * H (y 4) (y 5) * D (y 2) (y 5) (y 3) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 2, 3, 1, 0], ![5, 4, 2, 3, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_adcb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a d x * ∑ i, H x i * D c i b) = (2 : ℝ) * jetQ5 H D + (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a d x * ∑ i, H x i * D c i b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a d x * H x i * D c i b) + (1 : ℝ) * (H a b * H c d * D d x a * H x i * D c i b) + (1 : ℝ) * (H a b * H c d * D x a d * H x i * D c i b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a d x * H x i * D c i b) + (1 : ℝ) * (H a b * H c d * D d x a * H x i * D c i b) + (1 : ℝ) * (H a b * H c d * D x a d * H x i * D c i b))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 3) (y 4) * H (y 4) (y 5) * D (y 2) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 2, 5], ![0, 3, 4, 2, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 0) * H (y 4) (y 5) * D (y 2) (y 5) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 3, 4], ![3, 2, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 3) * H (y 4) (y 5) * D (y 2) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 1, 0, 4], ![4, 3, 0, 2, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_bdca (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b d x * ∑ i, H x i * D c i a) = (2 : ℝ) * jetQ5 H D + (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b d x * ∑ i, H x i * D c i a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D b d x * H x i * D c i a) + (1 : ℝ) * (H a b * H c d * D d x b * H x i * D c i a) + (1 : ℝ) * (H a b * H c d * D x b d * H x i * D c i a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D b d x * H x i * D c i a) + (1 : ℝ) * (H a b * H c d * D d x b * H x i * D c i a) + (1 : ℝ) * (H a b * H c d * D x b d * H x i * D c i a))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 3) (y 4) * H (y 4) (y 5) * D (y 2) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 5, 2], ![2, 0, 5, 1, 3, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 3) (y 4) (y 1) * H (y 4) (y 5) * D (y 2) (y 5) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 4, 3], ![2, 3, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 1) (y 3) * H (y 4) (y 5) * D (y 2) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 4, 3, 1], ![2, 5, 0, 4, 3, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_abdc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a b x * ∑ i, H x i * D d i c) = (2 : ℝ) * jetQ4 H D + (1 : ℝ) * jetQ3 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a b x * ∑ i, H x i * D d i c) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a b x * H x i * D d i c) + (1 : ℝ) * (H a b * H c d * D b x a * H x i * D d i c) + (1 : ℝ) * (H a b * H c d * D x a b * H x i * D d i c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a b x * H x i * D d i c) + (1 : ℝ) * (H a b * H c d * D b x a * H x i * D d i c) + (1 : ℝ) * (H a b * H c d * D x a b * H x i * D d i c))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 1) (y 4) * H (y 4) (y 5) * D (y 3) (y 5) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 0, 1], ![4, 5, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 4) (y 0) * H (y 4) (y 5) * D (y 3) (y 5) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 0, 1], ![4, 5, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 1) * H (y 4) (y 5) * D (y 3) (y 5) (y 2) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 3, 2, 1, 0], ![5, 4, 3, 2, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_acdb (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a c x * ∑ i, H x i * D d i b) = (2 : ℝ) * jetQ5 H D + (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T a c x * ∑ i, H x i * D d i b) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D a c x * H x i * D d i b) + (1 : ℝ) * (H a b * H c d * D c x a * H x i * D d i b) + (1 : ℝ) * (H a b * H c d * D x a c * H x i * D d i b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D a c x * H x i * D d i b) + (1 : ℝ) * (H a b * H c d * D c x a * H x i * D d i b) + (1 : ℝ) * (H a b * H c d * D x a c * H x i * D d i b))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 0) (y 2) (y 4) * H (y 4) (y 5) * D (y 3) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 2, 5], ![0, 2, 4, 3, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 4) (y 0) * H (y 4) (y 5) * D (y 3) (y 5) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 3, 4], ![2, 3, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 0) (y 2) * H (y 4) (y 5) * D (y 3) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 3, 0, 4], ![4, 2, 0, 3, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_bet_bcda (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b c x * ∑ i, H x i * D d i a) = (2 : ℝ) * jetQ5 H D + (1 : ℝ) * jetQ1 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, T b c x * ∑ i, H x i * D d i a) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ i, ((1 : ℝ) * (H a b * H c d * D b c x * H x i * D d i a) + (1 : ℝ) * (H a b * H c d * D c x b * H x i * D d i a) + (1 : ℝ) * (H a b * H c d * D x b c * H x i * D d i a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x i => (1 : ℝ) * (H a b * H c d * D b c x * H x i * D d i a) + (1 : ℝ) * (H a b * H c d * D c x b * H x i * D d i a) + (1 : ℝ) * (H a b * H c d * D x b c * H x i * D d i a))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 1) (y 2) (y 4) * H (y 4) (y 5) * D (y 3) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 5, 2], ![3, 0, 5, 1, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 2) (y 4) (y 1) * H (y 4) (y 5) * D (y 3) (y 5) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 4, 3], ![3, 2, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * D (y 4) (y 1) (y 2) * H (y 4) (y 5) * D (y 3) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 4, 0, 3, 1], ![3, 5, 0, 4, 2, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_abcd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a b x * T c d y)) = (4 : ℝ) * jetQ4 H D + (4 : ℝ) * jetQ3 H D + (1 : ℝ) * jetQ2 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a b x * T c d y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D a b x * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D a b x * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D a b x * D y c d) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D y c d) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D y c d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D a b x * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D a b x * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D a b x * D y c d) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D b x a * D y c d) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D c d y) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D d y c) + (1 : ℝ) * (H a b * H c d * H x y * D x a b * D y c d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 1) (y 4) * D (y 2) (y 3) (y 5) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 1) (y 4) * D (y 3) (y 5) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 0, 1], ![4, 5, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 1) (y 4) * D (y 5) (y 2) (y 3) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 4) (y 0) * D (y 2) (y 3) (y 5) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 0, 1], ![4, 5, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 4) (y 0) * D (y 3) (y 5) (y 2) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 0, 1], ![4, 5, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 4) (y 0) * D (y 5) (y 2) (y 3) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 0, 1], ![4, 5, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 1) * D (y 2) (y 3) (y 5) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 2, 3, 1, 0], ![5, 4, 2, 3, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 1) * D (y 3) (y 5) (y 2) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 3, 2, 1, 0], ![5, 4, 3, 2, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 1) * D (y 5) (y 2) (y 3) = jetQ2 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_acbd (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a c x * T b d y)) = (3 : ℝ) * jetQ1 H D + (6 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a c x * T b d y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D a c x * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D a c x * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D a c x * D y b d) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D y b d) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D y b d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D a c x * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D a c x * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D a c x * D y b d) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D c x a * D y b d) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D b d y) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D d y b) + (1 : ℝ) * (H a b * H c d * H x y * D x a c * D y b d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 2) (y 4) * D (y 1) (y 3) (y 5) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 2) (y 4) * D (y 3) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 2, 5], ![0, 2, 4, 3, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 2) (y 4) * D (y 5) (y 1) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 2, 5, 1, 3], ![0, 4, 2, 5, 1, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 0) * D (y 1) (y 3) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 2, 5], ![2, 0, 4, 1, 3, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 0) * D (y 3) (y 5) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 3, 4], ![2, 3, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 0) * D (y 5) (y 1) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 4, 1, 3], ![2, 4, 0, 5, 3, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 2) * D (y 1) (y 3) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 2, 5, 0, 4], ![4, 0, 2, 1, 5, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 2) * D (y 3) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 3, 0, 4], ![4, 2, 0, 3, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 2) * D (y 5) (y 1) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 4, 0, 1], ![4, 5, 0, 2, 3, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_adbc (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a d x * T b c y)) = (3 : ℝ) * jetQ1 H D + (6 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T a d x * T b c y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D a d x * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D a d x * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D a d x * D y b c) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D y b c) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D y b c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D a d x * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D a d x * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D a d x * D y b c) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D d x a * D y b c) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D b c y) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D c y b) + (1 : ℝ) * (H a b * H c d * H x y * D x a d * D y b c))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 3) (y 4) * D (y 1) (y 2) (y 5) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 2, 5], ![0, 1, 4, 3, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 3) (y 4) * D (y 2) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 2, 5], ![0, 3, 4, 2, 1, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 0) (y 3) (y 4) * D (y 5) (y 1) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 5, 2, 1, 3], ![0, 4, 3, 5, 1, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 0) * D (y 1) (y 2) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 2, 5], ![3, 0, 4, 1, 2, 5], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 0) * D (y 2) (y 5) (y 1) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 3, 4], ![3, 2, 0, 4, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 0) * D (y 5) (y 1) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 4, 0, 1, 3], ![3, 4, 0, 5, 2, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 3) * D (y 1) (y 2) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 5, 2, 0, 4], ![4, 0, 3, 1, 5, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 3) * D (y 2) (y 5) (y 1) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 1, 0, 4], ![4, 3, 0, 2, 5, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 0) (y 3) * D (y 5) (y 1) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 4, 3, 0, 1], ![4, 5, 0, 3, 2, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_bcad (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T b c x * T a d y)) = (3 : ℝ) * jetQ1 H D + (6 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T b c x * T a d y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D b c x * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D b c x * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D b c x * D y a d) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D y a d) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D y a d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D b c x * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D b c x * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D b c x * D y a d) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D c x b * D y a d) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D a d y) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D d y a) + (1 : ℝ) * (H a b * H c d * H x y * D x b c * D y a d))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 2) (y 4) * D (y 0) (y 3) (y 5) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 4, 3, 5, 2], ![0, 1, 5, 3, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 2) (y 4) * D (y 3) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 4, 0, 5, 2], ![3, 0, 5, 1, 2, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 2) (y 4) * D (y 5) (y 0) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 5, 2, 4, 0], ![5, 0, 3, 1, 4, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 1) * D (y 0) (y 3) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 3, 1, 5, 2], ![0, 3, 5, 2, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 1) * D (y 3) (y 5) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 0, 4, 3], ![3, 2, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 4) (y 1) * D (y 5) (y 0) (y 3) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 1, 4, 0], ![5, 3, 0, 2, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 2) * D (y 0) (y 3) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 5, 2, 3, 1], ![0, 5, 3, 4, 1, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 2) * D (y 3) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 4, 0, 3, 1], ![3, 5, 0, 4, 2, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 2) * D (y 5) (y 0) (y 3) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 4, 3, 1, 0], ![5, 4, 0, 3, 2, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_bdac (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T b d x * T a c y)) = (3 : ℝ) * jetQ1 H D + (6 : ℝ) * jetQ5 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T b d x * T a c y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D b d x * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D b d x * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D b d x * D y a c) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D y a c) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D y a c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D b d x * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D b d x * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D b d x * D y a c) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D d x b * D y a c) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D a c y) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D c y a) + (1 : ℝ) * (H a b * H c d * H x y * D x b d * D y a c))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 3) (y 4) * D (y 0) (y 2) (y 5) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![0, 1, 2, 5, 4, 3], ![0, 1, 2, 5, 4, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 3) (y 4) * D (y 2) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 0, 4, 5, 2], ![2, 0, 5, 1, 3, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 1) (y 3) (y 4) * D (y 5) (y 0) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![1, 3, 2, 5, 4, 0], ![5, 0, 2, 1, 4, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 1) * D (y 0) (y 2) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 1, 3, 5, 2], ![0, 2, 5, 3, 1, 4], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 1) * D (y 2) (y 5) (y 0) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 1, 4, 3], ![2, 3, 0, 5, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 1) * D (y 5) (y 0) (y 2) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 1, 3, 4, 0], ![5, 2, 0, 3, 4, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 3) * D (y 0) (y 2) (y 5) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![0, 4, 2, 5, 3, 1], ![0, 5, 2, 4, 1, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 3) * D (y 2) (y 5) (y 0) = jetQ5 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 0, 4, 3, 1], ![2, 5, 0, 4, 3, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 1) (y 3) * D (y 5) (y 0) (y 2) = jetQ1 H D := by
    refine sum_reindex _ _ ⟨![2, 5, 3, 4, 1, 0], ![5, 4, 0, 2, 3, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring

/-- A term of the contracted order-four eikonal identity in the jet invariants. -/
lemma contr_gam_cdab (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hD : ∀ a b c, D a b c = D a c b) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T c d x * T a b y)) = (4 : ℝ) * jetQ4 H D + (4 : ℝ) * jetQ3 H D + (1 : ℝ) * jetQ2 H D := by
  have hHs := symm_fun2 hH
  have hDs := symm_fun3 hD
  have e1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (∑ x, ∑ y, H x y * (T c d x * T a b y)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ y, ((1 : ℝ) * (H a b * H c d * H x y * D c d x * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D c d x * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D c d x * D y a b) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D y a b) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D y a b)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]; ring
  rw [e1, sum_nest6 (fun a b c d x y => (1 : ℝ) * (H a b * H c d * H x y * D c d x * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D c d x * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D c d x * D y a b) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D d x c * D y a b) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D a b y) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D b y a) + (1 : ℝ) * (H a b * H c d * H x y * D x c d * D y a b))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 3) (y 4) * D (y 0) (y 1) (y 5) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h1 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 3) (y 4) * D (y 1) (y 5) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h2 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 2) (y 3) (y 4) * D (y 5) (y 0) (y 1) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h3 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 2) * D (y 0) (y 1) (y 5) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 5, 4, 1, 0], ![5, 4, 0, 1, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h4 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 2) * D (y 1) (y 5) (y 0) = jetQ4 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 5, 4, 1, 0], ![5, 4, 1, 0, 3, 2], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h5 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 3) (y 4) (y 2) * D (y 5) (y 0) (y 1) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![4, 5, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h6 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 2) (y 3) * D (y 0) (y 1) (y 5) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h7 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 2) (y 3) * D (y 1) (y 5) (y 0) = jetQ3 H D := by
    refine sum_reindex _ _ ⟨![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  have h8 : ∑ y : Fin 6 → Fin n, H (y 0) (y 1) * H (y 2) (y 3) * H (y 4) (y 5) * D (y 4) (y 2) (y 3) * D (y 5) (y 0) (y 1) = jetQ2 H D := by
    refine sum_reindex _ _ ⟨![2, 3, 4, 5, 1, 0], ![5, 4, 0, 1, 2, 3], by decide, by decide⟩ fun y => ?_
    jet_normD
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  first | done | ring


set_option maxHeartbeats 2800000 in
/-- **The full contraction of the fourth jet of the world function** (algebraic form): if the order-four eikonal identity
holds at every index, `H^{ab} H^{cd} S4_{abcd} = 4/3 A₁ + 8/3 A₂ - Q₁ - 1/6 Q₂ + 2/3 Q₃ - 2/3 Q₄ + 2/3 Q₅`. -/
theorem sum_T4_alg (H : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ) (E : Fin n → Fin n → Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → Fin n → ℝ) (S4 : Fin n → Fin n → Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (hD : ∀ a b c, D a b c = D a c b) (hE1 : ∀ a b c d, E a b c d = E b a c d)
    (hE2 : ∀ a b c d, E a b c d = E a b d c) (hT : ∀ x y z, T x y z = D x y z + D y z x + D z x y)
    (hS1 : ∀ a b c d, S4 a b c d = S4 b a c d) (hS2 : ∀ a b c d, S4 a b c d = S4 a c b d)
    (hS3 : ∀ a b c d, S4 a b c d = S4 a b d c)
    (hrel : ∀ a b c d, (4 : ℝ) * (∑ j, ∑ i, D a c i * H i j * D b j d) + (4 : ℝ) * (∑ j, ∑ i, D b c i * H i j * D a j d) + (-4 : ℝ) * (E a b c d) + (4 : ℝ) * (∑ j, ∑ i, D a d i * H i j * D b j c) + (4 : ℝ) * (∑ j, ∑ i, D b d i * H i j * D a j c) + (-4 : ℝ) * (E a b d c) + (4 : ℝ) * (∑ j, ∑ i, D a b i * H i j * D c j d) + (4 : ℝ) * (∑ j, ∑ i, D c b i * H i j * D a j d) + (-4 : ℝ) * (E a c b d) + (4 : ℝ) * (∑ j, ∑ i, D a d i * H i j * D c j b) + (4 : ℝ) * (∑ j, ∑ i, D c d i * H i j * D a j b) + (-4 : ℝ) * (E a c d b) + (4 : ℝ) * (∑ j, ∑ i, D a b i * H i j * D d j c) + (4 : ℝ) * (∑ j, ∑ i, D d b i * H i j * D a j c) + (-4 : ℝ) * (E a d b c) + (4 : ℝ) * (∑ j, ∑ i, D a c i * H i j * D d j b) + (4 : ℝ) * (∑ j, ∑ i, D d c i * H i j * D a j b) + (-4 : ℝ) * (E a d c b) + (-4 : ℝ) * (∑ x, T b c x * ∑ i, H x i * D a i d) + (-4 : ℝ) * (∑ x, T b d x * ∑ i, H x i * D a i c) + (-4 : ℝ) * (∑ x, T c d x * ∑ i, H x i * D a i b) + (4 : ℝ) * (∑ j, ∑ i, D b a i * H i j * D c j d) + (4 : ℝ) * (∑ j, ∑ i, D c a i * H i j * D b j d) + (-4 : ℝ) * (E b c a d) + (4 : ℝ) * (∑ j, ∑ i, D b d i * H i j * D c j a) + (4 : ℝ) * (∑ j, ∑ i, D c d i * H i j * D b j a) + (-4 : ℝ) * (E b c d a) + (4 : ℝ) * (∑ j, ∑ i, D b a i * H i j * D d j c) + (4 : ℝ) * (∑ j, ∑ i, D d a i * H i j * D b j c) + (-4 : ℝ) * (E b d a c) + (4 : ℝ) * (∑ j, ∑ i, D b c i * H i j * D d j a) + (4 : ℝ) * (∑ j, ∑ i, D d c i * H i j * D b j a) + (-4 : ℝ) * (E b d c a) + (-4 : ℝ) * (∑ x, T a c x * ∑ i, H x i * D b i d) + (-4 : ℝ) * (∑ x, T a d x * ∑ i, H x i * D b i c) + (-4 : ℝ) * (∑ x, T c d x * ∑ i, H x i * D b i a) + (4 : ℝ) * (∑ j, ∑ i, D c a i * H i j * D d j b) + (4 : ℝ) * (∑ j, ∑ i, D d a i * H i j * D c j b) + (-4 : ℝ) * (E c d a b) + (4 : ℝ) * (∑ j, ∑ i, D c b i * H i j * D d j a) + (4 : ℝ) * (∑ j, ∑ i, D d b i * H i j * D c j a) + (-4 : ℝ) * (E c d b a) + (-4 : ℝ) * (∑ x, T a b x * ∑ i, H x i * D c i d) + (-4 : ℝ) * (∑ x, T a d x * ∑ i, H x i * D c i b) + (-4 : ℝ) * (∑ x, T b d x * ∑ i, H x i * D c i a) + (-4 : ℝ) * (∑ x, T a b x * ∑ i, H x i * D d i c) + (-4 : ℝ) * (∑ x, T a c x * ∑ i, H x i * D d i b) + (-4 : ℝ) * (∑ x, T b c x * ∑ i, H x i * D d i a) + (4 : ℝ) * (S4 a b c d) + (4 : ℝ) * (S4 a b d c) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a b x * T c d y)) + (4 : ℝ) * (S4 a c d b) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a c x * T b d y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a d x * T b c y)) + (4 : ℝ) * (S4 b c d a) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T b c x * T a d y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T b d x * T a c y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T c d x * T a b y)) = 4 * S4 a b c d) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a b c d =
      4 / 3 * jetA1 H E + 8 / 3 * jetA2 H E - jetQ1 H D - 1 / 6 * jetQ2 H D + 2 / 3 * jetQ3 H D -
        2 / 3 * jetQ4 H D + 2 / 3 * jetQ5 H D := by
  have cs1 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a b d c =
      ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a b c d :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [hS3 a b d c]
  have cs2 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a c d b =
      ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a b c d :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [hS3 a c d b, hS2 a c b d]
  have cs3 : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 b c d a =
      ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * S4 a b c d :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [hS3 b c d a, hS2 b c a d, hS1 b a c d]
  have hc : ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * ((4 : ℝ) * (∑ j, ∑ i, D a c i * H i j * D b j d) + (4 : ℝ) * (∑ j, ∑ i, D b c i * H i j * D a j d) + (-4 : ℝ) * (E a b c d) + (4 : ℝ) * (∑ j, ∑ i, D a d i * H i j * D b j c) + (4 : ℝ) * (∑ j, ∑ i, D b d i * H i j * D a j c) + (-4 : ℝ) * (E a b d c) + (4 : ℝ) * (∑ j, ∑ i, D a b i * H i j * D c j d) + (4 : ℝ) * (∑ j, ∑ i, D c b i * H i j * D a j d) + (-4 : ℝ) * (E a c b d) + (4 : ℝ) * (∑ j, ∑ i, D a d i * H i j * D c j b) + (4 : ℝ) * (∑ j, ∑ i, D c d i * H i j * D a j b) + (-4 : ℝ) * (E a c d b) + (4 : ℝ) * (∑ j, ∑ i, D a b i * H i j * D d j c) + (4 : ℝ) * (∑ j, ∑ i, D d b i * H i j * D a j c) + (-4 : ℝ) * (E a d b c) + (4 : ℝ) * (∑ j, ∑ i, D a c i * H i j * D d j b) + (4 : ℝ) * (∑ j, ∑ i, D d c i * H i j * D a j b) + (-4 : ℝ) * (E a d c b) + (-4 : ℝ) * (∑ x, T b c x * ∑ i, H x i * D a i d) + (-4 : ℝ) * (∑ x, T b d x * ∑ i, H x i * D a i c) + (-4 : ℝ) * (∑ x, T c d x * ∑ i, H x i * D a i b) + (4 : ℝ) * (∑ j, ∑ i, D b a i * H i j * D c j d) + (4 : ℝ) * (∑ j, ∑ i, D c a i * H i j * D b j d) + (-4 : ℝ) * (E b c a d) + (4 : ℝ) * (∑ j, ∑ i, D b d i * H i j * D c j a) + (4 : ℝ) * (∑ j, ∑ i, D c d i * H i j * D b j a) + (-4 : ℝ) * (E b c d a) + (4 : ℝ) * (∑ j, ∑ i, D b a i * H i j * D d j c) + (4 : ℝ) * (∑ j, ∑ i, D d a i * H i j * D b j c) + (-4 : ℝ) * (E b d a c) + (4 : ℝ) * (∑ j, ∑ i, D b c i * H i j * D d j a) + (4 : ℝ) * (∑ j, ∑ i, D d c i * H i j * D b j a) + (-4 : ℝ) * (E b d c a) + (-4 : ℝ) * (∑ x, T a c x * ∑ i, H x i * D b i d) + (-4 : ℝ) * (∑ x, T a d x * ∑ i, H x i * D b i c) + (-4 : ℝ) * (∑ x, T c d x * ∑ i, H x i * D b i a) + (4 : ℝ) * (∑ j, ∑ i, D c a i * H i j * D d j b) + (4 : ℝ) * (∑ j, ∑ i, D d a i * H i j * D c j b) + (-4 : ℝ) * (E c d a b) + (4 : ℝ) * (∑ j, ∑ i, D c b i * H i j * D d j a) + (4 : ℝ) * (∑ j, ∑ i, D d b i * H i j * D c j a) + (-4 : ℝ) * (E c d b a) + (-4 : ℝ) * (∑ x, T a b x * ∑ i, H x i * D c i d) + (-4 : ℝ) * (∑ x, T a d x * ∑ i, H x i * D c i b) + (-4 : ℝ) * (∑ x, T b d x * ∑ i, H x i * D c i a) + (-4 : ℝ) * (∑ x, T a b x * ∑ i, H x i * D d i c) + (-4 : ℝ) * (∑ x, T a c x * ∑ i, H x i * D d i b) + (-4 : ℝ) * (∑ x, T b c x * ∑ i, H x i * D d i a) + (4 : ℝ) * (S4 a b c d) + (4 : ℝ) * (S4 a b d c) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a b x * T c d y)) + (4 : ℝ) * (S4 a c d b) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a c x * T b d y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T a d x * T b c y)) + (4 : ℝ) * (S4 b c d a) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T b c x * T a d y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T b d x * T a c y)) + (1 : ℝ) * (∑ x, ∑ y, H x y * (T c d x * T a b y))) =
      ∑ a, ∑ b, ∑ c, ∑ d, H a b * H c d * (4 * S4 a b c d) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [hrel]
  simp (config := { maxSteps := 4000000 }) only [mul_add, Finset.sum_add_distrib, sum4_mul_const] at hc
  rw [cs1, cs2, cs3] at hc
  rw [contr_alp_acbd H D hH hD, contr_alp_bcad H D hH hD, contr_E_abcd H E hH hE1 hE2, contr_alp_adbc H D hH hD, contr_alp_bdac H D hH hD, contr_E_abdc H E hH hE1 hE2, contr_alp_abcd H D hH hD, contr_alp_cbad H D hH hD, contr_E_acbd H E hH hE1 hE2, contr_alp_adcb H D hH hD, contr_alp_cdab H D hH hD, contr_E_acdb H E hH hE1 hE2, contr_alp_abdc H D hH hD, contr_alp_dbac H D hH hD, contr_E_adbc H E hH hE1 hE2, contr_alp_acdb H D hH hD, contr_alp_dcab H D hH hD, contr_E_adcb H E hH hE1 hE2, contr_bet_bcad H D T hH hD hT, contr_bet_bdac H D T hH hD hT, contr_bet_cdab H D T hH hD hT, contr_alp_bacd H D hH hD, contr_alp_cabd H D hH hD, contr_E_bcad H E hH hE1 hE2, contr_alp_bdca H D hH hD, contr_alp_cdba H D hH hD, contr_E_bcda H E hH hE1 hE2, contr_alp_badc H D hH hD, contr_alp_dabc H D hH hD, contr_E_bdac H E hH hE1 hE2, contr_alp_bcda H D hH hD, contr_alp_dcba H D hH hD, contr_E_bdca H E hH hE1 hE2, contr_bet_acbd H D T hH hD hT, contr_bet_adbc H D T hH hD hT, contr_bet_cdba H D T hH hD hT, contr_alp_cadb H D hH hD, contr_alp_dacb H D hH hD, contr_E_cdab H E hH hE1 hE2, contr_alp_cbda H D hH hD, contr_alp_dbca H D hH hD, contr_E_cdba H E hH hE1 hE2, contr_bet_abcd H D T hH hD hT, contr_bet_adcb H D T hH hD hT, contr_bet_bdca H D T hH hD hT, contr_bet_abdc H D T hH hD hT, contr_bet_acdb H D T hH hD hT, contr_bet_bcda H D T hH hD hT, contr_gam_abcd H D T hH hD hT, contr_gam_acbd H D T hH hD hT, contr_gam_adbc H D T hH hD hT, contr_gam_bcad H D T hH hD hT, contr_gam_bdac H D T hH hD hT, contr_gam_cdab H D T hH hD hT] at hc
  linear_combination hc / 12

end Lightlike
