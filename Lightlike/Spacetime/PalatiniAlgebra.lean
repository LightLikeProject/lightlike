import Mathlib

/-!
# The algebra of the Palatini identity (GE15, stage S2, algebraic part)

For a symmetric array `G` (the inverse metric), symmetric `Γ^ρ_{σν}` (the Christoffel symbols), `δ^ρ_{σν}` (their variation)
and `dd μ ρ ν σ` (the derivative `∂_μ δΓ^ρ_{νσ}`), the contraction of the linearised Ricci tensor, written with the
derivatives of `δΓ` and the products `δΓ · Γ`, equals the divergence term
`∂_ρ W^ρ + Γ^κ_{κρ} W^ρ`, `W^ρ = G^{σν} δΓ^ρ_{σν} - G^{ρσ} δΓ^κ_{κσ}`, where `∂_ρ G^{σν} = -Γ^σ_{ρα} G^{αν} - Γ^ν_{ρα} G^{σα}`
(`palatini_alg_nd`, the part without derivatives of `δΓ`; `palatini_dd`, the part with them). Pure finite sums; no analysis.

**Limits.** This is the algebraic core only: the variation formula for the curvature in terms of `δΓ`, the identities
`∂_ρ G^{σν} = ...` and `∂_ρ √|g| = √|g| Γ^κ_{κρ}` for an actual metric, and the integral statement are later stages.
-/

open Finset

namespace Lightlike

variable {n : ℕ}

theorem sum4_eq (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [Fintype.sum_prod_type]

section
variable (G : Fin n → Fin n → ℝ) (Γ δ : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ r a b, Γ r a b = Γ r b a) (hδ : ∀ r a b, δ r a b = δ r b a)
include hG hΓ hδ

theorem palatini_T3 :
    ∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (δ ρ ν κ * Γ κ ρ σ) =
      ∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ σ ρ α * G α ν * δ ρ σ ν := by
  rw [sum4_eq, sum4_eq]
  refine Fintype.sum_equiv
    ⟨fun x => (x.2.2.1, x.2.2.2, x.2.1, x.1), fun y => (y.2.2.2, y.2.2.1, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun x => ?_
  obtain ⟨σ, ν, ρ, κ⟩ := x
  simp only [Equiv.coe_fn_mk]
  rw [hδ ρ ν κ]; ring

theorem palatini_T4 :
    ∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (Γ ρ ν κ * δ κ ρ σ) =
      ∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ σ ρ α * G α ν * δ ρ σ ν := by
  rw [sum4_eq, sum4_eq]
  -- LHS (σ, ν, ρ, κ); term G σ ν Γ ρ ν κ δ κ ρ σ ; RHS (ρ', σ', ν', α') = (κ, ρ, σ, ν): Γ σ' ρ' α' = Γ ρ κ ν
  refine Fintype.sum_equiv
    ⟨fun x => (x.2.2.2, x.2.2.1, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.2.1, y.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun x => ?_
  obtain ⟨σ, ν, ρ, κ⟩ := x
  simp only [Equiv.coe_fn_mk]
  rw [hΓ ρ ν κ, hG ν σ]; ring

theorem palatini_Q'' :
    ∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ ν ρ α * G σ α * δ ρ σ ν =
      ∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ σ ρ α * G α ν * δ ρ σ ν := by
  rw [sum4_eq, sum4_eq]
  refine Fintype.sum_equiv
    ⟨fun x => (x.1, x.2.2.1, x.2.1, x.2.2.2), fun y => (y.1, y.2.2.1, y.2.1, y.2.2.2), fun _ => rfl, fun _ => rfl⟩
    _ _ fun x => ?_
  obtain ⟨ρ, σ, ν, α⟩ := x
  simp only [Equiv.coe_fn_mk]
  rw [hδ ρ σ ν, hG σ α, hG α σ]


theorem palatini_E1 :
    ∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (δ ρ ρ κ * Γ κ ν σ) =
      ∑ ρ, ∑ σ, ∑ l, ∑ α, Γ σ ρ α * G ρ α * δ l l σ := by
  rw [sum4_eq, sum4_eq]
  refine Fintype.sum_equiv
    ⟨fun x => (x.2.1, x.2.2.2, x.2.2.1, x.1), fun y => (y.2.2.2, y.1, y.2.2.1, y.2.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun x => ?_
  obtain ⟨σ, ν, ρ, κ⟩ := x
  simp only [Equiv.coe_fn_mk]
  rw [hG ν σ]; ring

theorem palatini_E2 :
    ∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (Γ ρ ρ κ * δ κ ν σ) =
      ∑ ρ, ∑ l, ∑ σ, ∑ ν, Γ l l ρ * G σ ν * δ ρ σ ν := by
  rw [sum4_eq, sum4_eq]
  refine Fintype.sum_equiv
    ⟨fun x => (x.2.2.2, x.2.2.1, x.2.1, x.1), fun y => (y.2.2.2, y.2.2.1, y.2.1, y.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun x => ?_
  obtain ⟨σ, ν, ρ, κ⟩ := x
  simp only [Equiv.coe_fn_mk]
  rw [hG ν σ]; ring


/-- **The algebraic core of the Palatini identity**, the part without derivatives of `δΓ`. -/
theorem palatini_alg_nd :
    ∑ σ, ∑ ν, G σ ν * ∑ ρ, ∑ κ, (δ ρ ρ κ * Γ κ ν σ + Γ ρ ρ κ * δ κ ν σ - δ ρ ν κ * Γ κ ρ σ - Γ ρ ν κ * δ κ ρ σ) =
      (∑ ρ, ∑ σ, ∑ ν, (-(∑ α, (Γ σ ρ α * G α ν + Γ ν ρ α * G σ α))) * δ ρ σ ν) +
      (-(∑ ρ, ∑ σ, (-(∑ α, (Γ ρ ρ α * G α σ + Γ σ ρ α * G ρ α))) * ∑ κ, δ κ κ σ)) +
      ∑ ρ, (∑ κ, Γ κ κ ρ) * ((∑ σ, ∑ ν, G σ ν * δ ρ σ ν) - ∑ σ, G ρ σ * ∑ κ, δ κ κ σ) := by
  have e1 := palatini_E1 G Γ δ hG hΓ hδ
  have e2 := palatini_E2 G Γ δ hG hΓ hδ
  have t3 := palatini_T3 G Γ δ hG hΓ hδ
  have t4 := palatini_T4 G Γ δ hG hΓ hδ
  have q2 := palatini_Q'' G Γ δ hG hΓ hδ
  -- the left side
  have hL : ∑ σ, ∑ ν, G σ ν * ∑ ρ, ∑ κ, (δ ρ ρ κ * Γ κ ν σ + Γ ρ ρ κ * δ κ ν σ - δ ρ ν κ * Γ κ ρ σ - Γ ρ ν κ * δ κ ρ σ) =
      (∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (δ ρ ρ κ * Γ κ ν σ)) + (∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (Γ ρ ρ κ * δ κ ν σ)) -
        (∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (δ ρ ν κ * Γ κ ρ σ)) - (∑ σ, ∑ ν, ∑ ρ, ∑ κ, G σ ν * (Γ ρ ν κ * δ κ ρ σ)) := by
    simp only [Finset.mul_sum, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the first term on the right
  have hA : (∑ ρ, ∑ σ, ∑ ν, (-(∑ α, (Γ σ ρ α * G α ν + Γ ν ρ α * G σ α))) * δ ρ σ ν) =
      -(∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ σ ρ α * G α ν * δ ρ σ ν) - (∑ ρ, ∑ σ, ∑ ν, ∑ α, Γ ν ρ α * G σ α * δ ρ σ ν) := by
    simp only [neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  -- the second term
  have hB : (-(∑ ρ, ∑ σ, (-(∑ α, (Γ ρ ρ α * G α σ + Γ σ ρ α * G ρ α))) * ∑ κ, δ κ κ σ)) =
      (∑ ρ, ∑ σ, ∑ l, ∑ α, Γ ρ ρ α * G α σ * δ l l σ) + (∑ ρ, ∑ σ, ∑ l, ∑ α, Γ σ ρ α * G ρ α * δ l l σ) := by
    simp only [neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
    ring
  -- the third term
  have hC : (∑ ρ, (∑ κ, Γ κ κ ρ) * ((∑ σ, ∑ ν, G σ ν * δ ρ σ ν) - ∑ σ, G ρ σ * ∑ κ, δ κ κ σ)) =
      (∑ ρ, ∑ l, ∑ σ, ∑ ν, Γ l l ρ * G σ ν * δ ρ σ ν) - (∑ ρ, ∑ l, ∑ σ, ∑ l', Γ l l ρ * G ρ σ * δ l' l' σ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_sub, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      ring
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l' _ => by ring
  -- the cancellation `B1 = ∑ Γt V`
  have hBC : (∑ ρ, ∑ σ, ∑ l, ∑ α, Γ ρ ρ α * G α σ * δ l l σ) = (∑ ρ, ∑ l, ∑ σ, ∑ l', Γ l l ρ * G ρ σ * δ l' l' σ) := by
    rw [sum4_eq, sum4_eq]
    refine Fintype.sum_equiv
      ⟨fun x => (x.2.2.2, x.1, x.2.1, x.2.2.1), fun y => (y.2.1, y.2.2.1, y.2.2.2, y.1), fun _ => rfl, fun _ => rfl⟩
      _ _ fun x => ?_
    obtain ⟨ρ, σ, α, l⟩ := x
    simp only [Equiv.coe_fn_mk]
  rw [hL, hA, hB, hC]
  rw [e1, e2, t3, t4, q2, hBC]
  ring


end

theorem sum3_eq (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ x : Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2 := by
  simp only [Fintype.sum_prod_type]

/-- The part of the Palatini identity with derivatives of `δΓ`. -/
theorem palatini_dd (G : Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a) (dd : Fin n → Fin n → Fin n → Fin n → ℝ) (hdd : ∀ m r a b, dd m r a b = dd m r b a) :
    ∑ σ, ∑ ν, G σ ν * (∑ ρ, dd ρ ρ ν σ - ∑ ρ, dd ν ρ ρ σ) =
      ∑ ρ, ((∑ σ, ∑ ν, G σ ν * dd ρ ρ σ ν) - ∑ σ, G ρ σ * ∑ κ, dd ρ κ κ σ) := by
  have h1 : ∑ σ, ∑ ν, G σ ν * ∑ ρ, dd ρ ρ ν σ = ∑ ρ, ∑ σ, ∑ ν, G σ ν * dd ρ ρ σ ν := by
    simp only [Finset.mul_sum]
    rw [sum3_eq, sum3_eq]
    refine Fintype.sum_equiv
      ⟨fun x => (x.2.2, x.1, x.2.1), fun y => (y.2.1, y.2.2, y.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    obtain ⟨σ, ν, ρ⟩ := x
    simp only [Equiv.coe_fn_mk]
    rw [hdd ρ ρ ν σ]
  have h2 : ∑ σ, ∑ ν, G σ ν * ∑ ρ, dd ν ρ ρ σ = ∑ ρ, ∑ σ, G ρ σ * ∑ κ, dd ρ κ κ σ := by
    simp only [Finset.mul_sum]
    rw [sum3_eq, sum3_eq]
    refine Fintype.sum_equiv
      ⟨fun x => (x.2.1, x.1, x.2.2), fun y => (y.2.1, y.1, y.2.2), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    obtain ⟨σ, ν, ρ⟩ := x
    simp only [Equiv.coe_fn_mk]
    rw [hG σ ν]
  have : ∀ σ ν, G σ ν * (∑ ρ, dd ρ ρ ν σ - ∑ ρ, dd ν ρ ρ σ) =
      G σ ν * ∑ ρ, dd ρ ρ ν σ - G σ ν * ∑ ρ, dd ν ρ ρ σ := fun σ ν => mul_sub _ _ _
  simp only [this, Finset.sum_sub_distrib]
  rw [h1, h2]


end Lightlike
