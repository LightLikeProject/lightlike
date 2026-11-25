import Lightlike.OperatorAlgebras.CARQuasiFree
import Lightlike.OperatorAlgebras.FermionWick

/-!
# Wick's theorem for the CAR fields of a Bogoliubov vacuum

For a CAR representation `φ` on `E`, a Bogoliubov transformation `(α, β)` and a vector `Ψ` killed by all the transformed
annihilation operators `bᵢ` (`CARQuasiFree.lean`), the fields `x = Σ uᵢ bᵢ + Σ vᵢ bᵢ*` (linear in the transformed operators,
hence in `a, c`) are split fields: the annihilation part `Σ uᵢ bᵢ` kills `Ψ`, the creation part is killed by `⟪Ψ, ·⟫`, and
the anticommutator of an annihilation part with a field is the scalar `Σ uᵢ vᵢ'` (`carField_anticomm`).
`car_wick` is then Wick's theorem for every number `n` of such fields in the vacuum state `⟪Ψ, · Ψ⟫`:
`⟪Ψ, x₁ ⋯ xₙ Ψ⟫ = ⟪Ψ, Ψ⟫ · wick [x₁, …, xₙ]`; `car_wick_two` is the two-point function, the `n = 2` check (`Σ uᵢ vᵢ'`).
-/

open scoped InnerProductSpace
open Finset Matrix

namespace Lightlike.OperatorAlgebras

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- A ring homomorphism maps CAR pairs to CAR pairs. -/
lemma IsCARPairs.map {A B : Type*} [Ring A] [Ring B] (f : A →+* B) {a c : Fin n → A} (h : IsCARPairs a c) :
    IsCARPairs (fun i => f (a i)) (fun i => f (c i)) where
  ac i j := by
    have := congrArg f (h.ac i j)
    simpa [map_add, map_mul, apply_ite f] using this
  aa i j := by
    have := congrArg f (h.aa i j)
    simpa [map_add, map_mul] using this
  cc i j := by
    have := congrArg f (h.cc i j)
    simpa [map_add, map_mul] using this

section Instance

variable {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (α β : Matrix (Fin n) (Fin n) ℂ)
  (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0)

/-- The transformed annihilation operators as linear maps. -/
noncomputable def bOp (i : Fin n) : Module.End ℂ E :=
  ContinuousLinearMap.toLinearMapRingHom (bogAnn α β (carAnnihilation φ) (carCreation φ) i)

/-- The transformed creation operators as linear maps. -/
noncomputable def bsOp (i : Fin n) : Module.End ℂ E :=
  ContinuousLinearMap.toLinearMapRingHom (bogCre α β (carAnnihilation φ) (carCreation φ) i)

include h h1 h2 in
/-- The CAR relations for the transformed operators, in `Module.End ℂ E`. -/
lemma bOp_pairs : IsCARPairs (bOp (φ := φ) α β) (bsOp (φ := φ) α β) :=
  (isCARPairs_bog h.isCARPairs α β h1 h2).map ContinuousLinearMap.toLinearMapRingHom

/-- The field with coefficients `(u, v)`: `Σ uᵢ bᵢ + Σ vᵢ bᵢ*`, as a split field. -/
noncomputable def carField (c : (Fin n → ℂ) × (Fin n → ℂ)) : SplitField E where
  A := ∑ i, c.1 i • bOp (φ := φ) α β i
  B := ∑ i, c.2 i • bsOp (φ := φ) α β i

include h h1 h2 in
/-- **The anticommutator of the annihilation part with a field is the scalar** `Σ uᵢ vᵢ'`. -/
lemma carField_anticomm (c d : (Fin n → ℂ) × (Fin n → ℂ)) :
    (carField (φ := φ) α β c).A * (carField (φ := φ) α β d).φ + (carField (φ := φ) α β d).φ * (carField (φ := φ) α β c).A =
      (∑ i, c.1 i * d.2 i) • (1 : Module.End ℂ E) := by
  have hp := bOp_pairs h α β h1 h2
  unfold SplitField.φ carField
  simp only
  have e : ∀ x y z : Module.End ℂ E, x * (y + z) + (y + z) * x = (x * y + y * x) + (x * z + z * x) := by
    intro x y z; noncomm_ring
  rw [e, anticomm_lincomb_zero _ _ _ _ (fun j l => hp.aa j l),
    anticomm_lincomb_delta _ _ _ _ (fun j l => hp.ac j l), zero_add]

/-- The pairing of two split fields: the scalar of their anticommutator, if there is one. -/
noncomputable def pairOf (x y : SplitField E) : ℂ :=
  haveI := Classical.propDecidable (∃ c : ℂ, x.A * y.φ + y.φ * x.A = c • (1 : Module.End ℂ E))
  if h : ∃ c : ℂ, x.A * y.φ + y.φ * x.A = c • (1 : Module.End ℂ E) then h.choose else 0

lemma pairOf_spec {x y : SplitField E} {c : ℂ} (h : x.A * y.φ + y.φ * x.A = c • (1 : Module.End ℂ E)) :
    x.A * y.φ + y.φ * x.A = pairOf x y • (1 : Module.End ℂ E) := by
  unfold pairOf
  rw [dif_pos ⟨c, h⟩]
  exact (Classical.choose_spec (⟨c, h⟩ : ∃ c : ℂ, x.A * y.φ + y.φ * x.A = c • (1 : Module.End ℂ E)))

variable {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0)

include h h1 h2 hΨ in
/-- **Wick's theorem for the CAR fields of a Bogoliubov vacuum, for every number of fields**:
`⟪Ψ, x₁ ⋯ xₙ Ψ⟫ = ⟪Ψ, Ψ⟫ · wick [x₁, …, xₙ]` for fields `xᵢ = Σ uᵢⱼ bⱼ + Σ vᵢⱼ bⱼ*`. -/
theorem car_wick (L : List ((Fin n → ℂ) × (Fin n → ℂ))) :
    ⟪Ψ, fieldProd (L.map (carField (φ := φ) α β)) Ψ⟫_ℂ =
      ⟪Ψ, Ψ⟫_ℂ * wick pairOf (L.map (carField (φ := φ) α β)) := by
  have key := expect_prod Ψ (innerSL ℂ Ψ).toLinearMap pairOf (L.map (carField (φ := φ) α β)).length
    (L.map (carField (φ := φ) α β)) rfl ?_ ?_ ?_
  · simpa using key
  · intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    show (∑ i, c.1 i • bOp (φ := φ) α β i) Ψ = 0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : bOp (φ := φ) α β i Ψ = 0 := hΨ i
    rw [this, smul_zero]
  · intro x hx v
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    show ⟪Ψ, (∑ i, c.2 i • bsOp (φ := φ) α β i) v⟫_ℂ = 0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ⟪Ψ, bsOp (φ := φ) α β i v⟫_ℂ = ⟪bOp (φ := φ) α β i Ψ, v⟫_ℂ := (bog_adj h α β i Ψ v).symm
    rw [this, show bOp (φ := φ) α β i Ψ = 0 from hΨ i]
    simp
  · intro x hx y hy
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hy
    exact pairOf_spec (carField_anticomm h α β h1 h2 c d)

include h h1 h2 hΨ in
/-- **The two-point function** from `car_wick` (the `n = 2` check): `⟪Ψ, x y Ψ⟫ = ⟪Ψ, Ψ⟫ Σ uᵢ vᵢ'`, for `Ψ ≠ 0`. -/
theorem car_wick_two (hΨ0 : Ψ ≠ 0) (c d : (Fin n → ℂ) × (Fin n → ℂ)) :
    ⟪Ψ, (carField (φ := φ) α β c).φ ((carField (φ := φ) α β d).φ Ψ)⟫_ℂ = ⟪Ψ, Ψ⟫_ℂ * ∑ i, c.1 i * d.2 i := by
  have hw := car_wick h α β h1 h2 hΨ [c, d]
  simp only [List.map_cons, List.map_nil, fieldProd, List.prod_cons, List.prod_nil, mul_one, wick_pair] at hw
  have hsp := pairOf_spec (carField_anticomm h α β h1 h2 c d)
  rw [carField_anticomm h α β h1 h2 c d] at hsp
  have hpair : pairOf (carField (φ := φ) α β c) (carField (φ := φ) α β d) = ∑ i, c.1 i * d.2 i := by
    have := congrArg (fun T : Module.End ℂ E => T Ψ) hsp
    simp only [LinearMap.smul_apply, Module.End.one_apply] at this
    have h3 := smul_left_injective ℂ hΨ0 this
    exact h3.symm
  rw [hpair] at hw
  simpa [SplitField.φ] using hw

end Instance

end Lightlike.OperatorAlgebras
