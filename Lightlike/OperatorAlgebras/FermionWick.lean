import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module

/-!
# Wick's theorem for fermionic fields on a vacuum, for every number of fields

Let `E` be a complex vector space, `Ψ ∈ E` and `ℓ : E → ℂ` linear. A **split field** is `φ = A + B` with `A Ψ = 0`
(annihilation part) and `ℓ ∘ B = 0` (creation part). If every `A` anticommutes with every `φ` of a given list up to a scalar,
`A_x φ_y + φ_y A_x = pair x y`, then the vacuum expectation value of a product of fields is given by the Pfaffian-type
recursion (`wick`): `ℓ(φ₁ ⋯ φₙ Ψ) = ℓ(Ψ) · wick [φ₁, …, φₙ]`, with

`wick [] = 1`, `wick (x :: l) = Σ_i (-1)^i pair x lᵢ · wick (l without lᵢ)`.

This is proved for lists of every length (`expect_prod`). Odd `n` gives `0`. For the CAR fields of a Bogoliubov vacuum the
hypotheses are instances (`CARWick.lean`).
-/

open Finset

namespace Lightlike.OperatorAlgebras

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- A split field `φ = A + B`. -/
structure SplitField (E : Type u) [AddCommGroup E] [Module ℂ E] where
  /-- The annihilation part. -/
  A : Module.End ℂ E
  /-- The creation part. -/
  B : Module.End ℂ E

/-- The field `A + B`. -/
def SplitField.φ (x : SplitField E) : Module.End ℂ E := x.A + x.B

/-- **The Wick (Pfaffian) recursion** for a pairing function. -/
noncomputable def wick (pair : SplitField E → SplitField E → ℂ) : List (SplitField E) → ℂ
  | [] => 1
  | x :: l => ∑ i : Fin l.length, (-1) ^ (i : ℕ) * pair x (l.get i) * wick pair (l.eraseIdx i)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons, List.length_eraseIdx]
  have := i.2
  split_ifs <;> omega

/-- The product of the fields of a list. -/
def fieldProd (l : List (SplitField E)) : Module.End ℂ E := (l.map SplitField.φ).prod

lemma fieldProd_nil : fieldProd ([] : List (SplitField E)) = 1 := by simp [fieldProd]

lemma fieldProd_cons (y : SplitField E) (l : List (SplitField E)) : fieldProd (y :: l) = y.φ * fieldProd l := by
  simp [fieldProd]

/-- **Passing an annihilation part through a product of fields**: with `A Ψ = 0` and `A φ + φ A = pair` a scalar,
`A (φ₁ ⋯ φₙ Ψ) = Σ_i (-1)^i pair(A, φᵢ) φ₁ ⋯ φ̂ᵢ ⋯ φₙ Ψ`. -/
theorem A_pass (Ψ : E) (pair : SplitField E → SplitField E → ℂ) (x : SplitField E) (hx : x.A Ψ = 0) :
    ∀ l : List (SplitField E), (∀ y ∈ l, x.A * y.φ + y.φ * x.A = pair x y • 1) →
      x.A (fieldProd l Ψ) = ∑ i : Fin l.length, ((-1 : ℂ) ^ (i : ℕ) * pair x (l.get i)) • fieldProd (l.eraseIdx i) Ψ := by
  intro l
  induction l with
  | nil => intro _; simp [fieldProd_nil, hx]
  | cons y l ih =>
    intro h
    have hy := h y (by simp)
    have ih' := ih (fun z hz => h z (by simp [hz]))
    rw [fieldProd_cons]
    erw [Fin.sum_univ_succ]
    have e : x.A (y.φ (fieldProd l Ψ)) = pair x y • fieldProd l Ψ - y.φ (x.A (fieldProd l Ψ)) := by
      have := congrArg (fun T : Module.End ℂ E => T (fieldProd l Ψ)) hy
      simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [eq_sub_iff_add_eq]; exact this
    show x.A (y.φ (fieldProd l Ψ)) = _
    rw [e, ih', map_sum]
    simp only [List.length_cons, Fin.val_zero, pow_zero, one_mul, List.get_cons_zero, List.eraseIdx_cons_zero,
      Fin.val_succ, List.get_cons_succ, List.eraseIdx_cons_succ, fieldProd_cons, map_smul, Module.End.mul_apply]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    have hget : (y :: l).get i.succ = l.get i := rfl
    rw [hget, pow_succ]
    module

/-- **Wick's theorem for every number of fields**: for split fields `φ₁, …, φₙ` with `Aᵢ Ψ = 0`, `ℓ ∘ Bᵢ = 0` and
`Aᵢ φⱼ + φⱼ Aᵢ = pair(i, j)` scalar, `ℓ(φ₁ ⋯ φₙ Ψ) = ℓ(Ψ) · wick pair [φ₁, …, φₙ]`. -/
theorem expect_prod (Ψ : E) (ℓ : E →ₗ[ℂ] ℂ) (pair : SplitField E → SplitField E → ℂ) :
    ∀ n : ℕ, ∀ l : List (SplitField E), l.length = n →
      (∀ x ∈ l, x.A Ψ = 0) → (∀ x ∈ l, ∀ v, ℓ (x.B v) = 0) →
      (∀ x ∈ l, ∀ y ∈ l, x.A * y.φ + y.φ * x.A = pair x y • 1) →
      ℓ (fieldProd l Ψ) = ℓ Ψ * wick pair l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl hA hB hP
    cases l with
    | nil => simp [fieldProd_nil, wick]
    | cons x l =>
      have hx := hA x (by simp)
      have hpass := A_pass Ψ pair x hx l (fun y hy => hP x (by simp) y (by simp [hy]))
      have h1 : ℓ (fieldProd (x :: l) Ψ) = ℓ (x.A (fieldProd l Ψ)) := by
        rw [fieldProd_cons]
        show ℓ ((x.A + x.B) (fieldProd l Ψ)) = _
        rw [LinearMap.add_apply, map_add, hB x (by simp), add_zero]
      rw [h1, hpass, map_sum, wick]
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [map_smul]
      have hlen : (l.eraseIdx i).length < n := by
        rw [List.length_eraseIdx]; simp at hl; have := i.2; split_ifs <;> omega
      have hsub : ∀ z ∈ l.eraseIdx i, z ∈ x :: l := fun z hz => List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hz)
      rw [ih _ hlen (l.eraseIdx i) rfl (fun z hz => hA z (hsub z hz)) (fun z hz => hB z (hsub z hz))
        (fun z hz w hw => hP z (hsub z hz) w (hsub w hw))]
      simp only [smul_eq_mul]
      ring

/-- `wick` of one field is `0` (odd number of fields). -/
lemma wick_single (pair : SplitField E → SplitField E → ℂ) (x : SplitField E) : wick pair [x] = 0 := by
  simp [wick]

/-- `wick` of two fields is their pairing. -/
lemma wick_pair (pair : SplitField E → SplitField E → ℂ) (x y : SplitField E) : wick pair [x, y] = pair x y := by
  simp [wick, Fin.sum_univ_succ, wick_single]

end Lightlike.OperatorAlgebras
