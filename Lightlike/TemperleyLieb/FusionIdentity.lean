import Mathlib
import Lightlike.TemperleyLieb.Rank
import Lightlike.TemperleyLieb.QNumbers
import Lightlike.TemperleyLieb.Complete

/-!
# The fusion identity `Q(a,b) = Σ_i E_i` (rank bound (B) and assembly)

The channel idempotents are `E_i = κ_i⁻¹ V_i W_i`.  The lower bound `rank E_i ≥ a + b - 2i + 1` comes from the
`q`-Dicke vectors, which are independent, fixed by `p_{a+b-2i}`, and sent to independent vectors by `V_i`
because `W_i V_i = κ_i p_{a+b-2i}`.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical
open Finsupp Module

variable {k : Type*} [Field k]

/-- The vertex norm does not vanish below the first root of unity. -/
theorem kapRec_ne (q : kˣ) (i a b : ℕ) (hia : i ≤ a) (hib : i ≤ b)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) : kapRec q a b i ≠ 0 := by
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  have hnz : ∀ m, 1 ≤ m → m ≤ a + b + 1 → qb q m ≠ 0 := fun m h1 h2 => qb_ne q hD m (hq2 m h1 h2)
  have hf := qfac_ne q (a + b + 1) hnz
  rw [kapRec_eq q i a b hia hib hq2]
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (hf _ (by omega))) (hf _ (by omega))) (hf _ (by omega))) (hf _ (by omega))
  · exact mul_ne_zero (mul_ne_zero (hf _ (by omega)) (hf _ (by omega))) (hf _ (by omega))

/-- A vector killed by `e_j` (`j + 1 < c`) is fixed by the projector `jwAt 0 c`. -/
theorem jwAt_fix (q : kˣ) (c : ℕ) {v : ModelSpace k} (hv : ∀ j, j + 2 ≤ c → modelE q j v = 0) :
    jwAt q 0 c v = v := by
  have hne : ∃ σ : ℕ → Bool, True := ⟨fun _ => false, trivial⟩
  obtain ⟨σ, -⟩ := hne
  let Y : Module.End k (ModelSpace k) := (LinearMap.toSpanSingleton k (ModelSpace k) v) ∘ₗ (Finsupp.lapply σ)
  have hY : ∀ j, j + 1 < c → (fun j => (modelE q (j + 0) : Module.End k (ModelSpace k))) j * Y = 0 := by
    intro j hj
    ext w
    simp [Y, hv j (by omega)]
  have := jw_mul_of_kill (k := k) (δ := loopVal q) (fun j => (modelE q (j + 0) : Module.End k (ModelSpace k))) c Y hY
  have h2 := congrArg (fun T : Module.End k (ModelSpace k) => T (single σ (1 : k))) this
  simpa [jwAt, Y] using h2

/-- **`W V = κ p`**: the dual vertex composed with the vertex is the vertex norm times the projector. -/
theorem Wop_mul_Vop (q : kˣ) (a b i : ℕ) (hia : i ≤ a) (hib : i ≤ b)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0) :
    Wop q a b i * Vop q a b i = kapRec q a b i • jwAt q 0 (a + b - 2 * i) := by
  have hQ := Qab_idem q a b (fun j hj => hd j (by omega))
  have hn := vertex_norm_value q i a b hia hib hd
  unfold Wop Vop
  calc jwAt q 0 (a + b - 2 * i) * nestCap q (a - i) i * Qab q a b *
        (Qab q a b * nestCup q (a - i) i * jwAt q 0 (a + b - 2 * i))
      = jwAt q 0 (a + b - 2 * i) * (nestCap q (a - i) i * (Qab q a b * Qab q a b) * nestCup q (a - i) i) *
          jwAt q 0 (a + b - 2 * i) := by simp only [mul_assoc]
    _ = _ := by rw [hQ]; exact hn

/-- The Dicke vector lies in its window. -/
theorem dicke_mem_Win (q : kˣ) (c m : ℕ) : (dicke q c m : ModelSpace k) ∈ Win k c := by
  unfold dicke
  refine Submodule.sum_mem _ fun σ hσ => ?_
  exact single_mem_Win ((mem_dickeSet.mp hσ).1) _

/-- The Dicke vector is fixed by the projector on its strands. -/
theorem jwAt_dicke (q : kˣ) (c m : ℕ) : jwAt q 0 c (dicke q c m : ModelSpace k) = dicke q c m :=
  jwAt_fix q c fun j hj => modelE_dicke q hj

/-- The vectors `V_i D_m` lie in the window `a + b`. -/
theorem Vop_dicke_mem (q : kˣ) (a b i m : ℕ) (hia : i ≤ a) (hib : i ≤ b) :
    Vop q a b i (dicke q (a + b - 2 * i) m) ∈ Win k (a + b) := by
  unfold Vop
  simp only [Module.End.mul_apply, jwAt_dicke]
  have h1 := nestCup_preserves q (l := a - i) (c := a + b - 2 * i) (by omega) i _ (dicke_mem_Win q (a + b - 2 * i) m)
  rw [show a + b - 2 * i + 2 * i = a + b by omega] at h1
  have h2 := jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl _ h1
  exact jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _ h2

/-- The images `V_i D_m` of the Dicke vectors are linearly independent. -/
theorem Vop_dicke_independent (q : kˣ) (a b i : ℕ) (hia : i ≤ a) (hib : i ≤ b)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    LinearIndependent k (fun m : Fin (a + b - 2 * i + 1) =>
      Vop q a b i (dicke q (a + b - 2 * i) m : ModelSpace k)) := by
  have hκ := kapRec_ne (k := k) q i a b hia hib hq2
  refine LinearIndependent.of_comp ((kapRec q a b i)⁻¹ • Wop q a b i) ?_
  have h : ∀ m : Fin (a + b - 2 * i + 1), (((kapRec q a b i)⁻¹ • Wop q a b i : Module.End k (ModelSpace k)) :
      ModelSpace k →ₗ[k] ModelSpace k) (Vop q a b i (dicke q (a + b - 2 * i) m : ModelSpace k)) =
      dicke q (a + b - 2 * i) m := by
    intro m
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (dicke q (a + b - 2 * i) m))
      (Wop_mul_Vop q a b i hia hib hd)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, jwAt_dicke] at this
    simp only [LinearMap.smul_apply, this, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  have hfun : (((kapRec q a b i)⁻¹ • Wop q a b i : Module.End k (ModelSpace k)) :
      ModelSpace k →ₗ[k] ModelSpace k) ∘ (fun m : Fin (a + b - 2 * i + 1) =>
      Vop q a b i (dicke q (a + b - 2 * i) m : ModelSpace k)) =
      fun m : Fin (a + b - 2 * i + 1) => (dicke q (a + b - 2 * i) m : ModelSpace k) := by
    funext m; exact h m
  rw [hfun]
  exact dicke_linearIndependent q (a + b - 2 * i)

end Lightlike.TemperleyLieb
