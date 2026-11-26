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

/-! ### Tail equivariance -/

/-- Glue a window sequence `ρ` (positions `< N`) to a tail `τ` (positions `≥ N`). -/
def app (N : ℕ) (ρ τ : ℕ → Bool) : ℕ → Bool := fun j => if j < N then ρ j else τ j

/-- The linear map gluing a fixed tail `τ` beyond `N` to every basis sequence. -/
noncomputable def iota (N : ℕ) (τ : ℕ → Bool) : ModelSpace k →ₗ[k] ModelSpace k :=
  Finsupp.lmapDomain k k (fun ρ => app N ρ τ)

/-- Gluing a tail to a basis vector. -/
lemma iota_single (N : ℕ) (τ ρ : ℕ → Bool) (c : k) : iota N τ (single ρ c) = single (app N ρ τ) c := by
  simp [iota]

/-- `T` acts on the first `N` strands and does not see the tail. -/
def Eqv (N : ℕ) (T : Module.End k (ModelSpace k)) : Prop :=
  ∀ τ, ∀ ρ : ℕ → Bool, T (single (app N ρ τ) 1) = iota N τ (T (single ρ 1))

/-- An equivariant operator commutes with `iota` on every vector. -/
lemma Eqv.apply {N : ℕ} {T : Module.End k (ModelSpace k)} (hT : Eqv N T) (τ : ℕ → Bool) (v : ModelSpace k) :
    T (iota N τ v) = iota N τ (T v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single ρ c =>
    have := hT τ ρ
    calc T (iota N τ (single ρ c)) = c • T (single (app N ρ τ) 1) := by
          rw [iota_single, show (single (app N ρ τ) c : ModelSpace k) = c • single (app N ρ τ) 1 by simp]
          rw [map_smul]
      _ = c • iota N τ (T (single ρ 1)) := by rw [this]
      _ = iota N τ (T (single ρ c)) := by
          rw [show (single ρ c : ModelSpace k) = c • single ρ 1 by simp, map_smul, map_smul]

/-- Equivariant operators are closed under products. -/
lemma Eqv.mul {N : ℕ} {S T : Module.End k (ModelSpace k)} (hS : Eqv N S) (hT : Eqv N T) : Eqv N (S * T) := by
  intro τ ρ
  rw [Module.End.mul_apply, hT τ ρ, hS.apply, Module.End.mul_apply]

/-- Equivariant operators are closed under sums. -/
lemma Eqv.add {N : ℕ} {S T : Module.End k (ModelSpace k)} (hS : Eqv N S) (hT : Eqv N T) : Eqv N (S + T) := by
  intro τ ρ
  rw [LinearMap.add_apply, hS τ ρ, hT τ ρ, LinearMap.add_apply, map_add]

/-- Equivariant operators are closed under scalars. -/
lemma Eqv.smul {N : ℕ} {T : Module.End k (ModelSpace k)} (r : k) (hT : Eqv N T) : Eqv N (r • T) := by
  intro τ ρ
  rw [LinearMap.smul_apply, hT τ ρ, LinearMap.smul_apply, map_smul]

/-- The identity does not see the tail. -/
lemma eqv_one (N : ℕ) : Eqv N (1 : Module.End k (ModelSpace k)) := by
  intro τ ρ; simp [iota_single]

/-- Setting two bits inside the window commutes with gluing. -/
lemma app_set2 {N j : ℕ} (hj : j + 2 ≤ N) (ρ τ : ℕ → Bool) (x y : Bool) :
    set2 (app N ρ τ) j x y = app N (set2 ρ j x y) τ := by
  funext n
  simp only [set2, app, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- The generators `e_j` (`j + 2 ≤ N`) do not see the tail. -/
lemma eqv_modelE (q : kˣ) {N j : ℕ} (hj : j + 2 ≤ N) : Eqv N (modelE q j : Module.End k (ModelSpace k)) := by
  intro τ ρ
  have h0 : app N ρ τ j = ρ j := by simp [app]; omega
  have h1 : app N ρ τ (j + 1) = ρ (j + 1) := by simp [app]; omega
  simp only [modelE_single, one_smul, eBasis, h0, h1]
  rcases ρ j with _ | _ <;> rcases ρ (j + 1) with _ | _ <;>
    simp [iota_single, app_set2 hj, map_sub, map_smul]

/-- Removing a pair inside the window commutes with gluing, up to a shift of the tail. -/
lemma removeTwo_app {N m : ℕ} (hm : m + 2 ≤ N) (ρ τ : ℕ → Bool) :
    removeTwo (app N ρ τ) m = app (N - 2) (removeTwo ρ m) (fun j => τ (j + 2)) := by
  funext n
  simp only [removeTwo, app]
  split_ifs <;> first | rfl | omega

/-- Inserting a pair inside the window commutes with gluing, up to a shift of the tail. -/
lemma insertTwo_app {N m : ℕ} (hm : m ≤ N) (ρ τ : ℕ → Bool) (x y : Bool) :
    insertTwo (app N ρ τ) m x y = app (N + 2) (insertTwo ρ m x y) (fun j => τ (j - 2)) := by
  funext n
  simp only [insertTwo, app]
  split_ifs <;> first | rfl | omega

/-- The cap commutes with gluing. -/
lemma capOp_iota (q : kˣ) {N m : ℕ} (hm : m + 2 ≤ N) (τ : ℕ → Bool) (v : ModelSpace k) :
    capOp q m (iota N τ v) = iota (N - 2) (fun j => τ (j + 2)) (capOp q m v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single ρ c =>
    have h0 : app N ρ τ m = ρ m := by simp [app]; omega
    have h1 : app N ρ τ (m + 1) = ρ (m + 1) := by simp [app]; omega
    simp only [iota_single, capOp_single, capBasis, h0, h1, removeTwo_app hm, map_smul]

/-- The cup commutes with gluing. -/
lemma cupOp_iota (q : kˣ) {N m : ℕ} (hm : m ≤ N) (τ : ℕ → Bool) (v : ModelSpace k) :
    cupOp q m (iota N τ v) = iota (N + 2) (fun j => τ (j - 2)) (cupOp q m v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single ρ c =>
    simp only [iota_single, cupOp_single, cupBasis, insertTwo_app hm, map_smul, map_sub]

/-- The glued tail only matters beyond the window. -/
lemma iota_congr (N : ℕ) {τ τ' : ℕ → Bool} (h : ∀ j, N ≤ j → τ j = τ' j) (v : ModelSpace k) :
    iota N τ v = iota N τ' v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single ρ c =>
    have : app N ρ τ = app N ρ τ' := by
      funext j; simp only [app]; split_ifs with hj; rfl; exact h j (by omega)
    rw [iota_single, iota_single, this]

/-- **Conjugating by a cup and a cap** (insertion position `m ≤ n`) keeps the operator independent of the tail. -/
lemma Eqv.cup_mul_cap (q : kˣ) {n m : ℕ} (hm : m ≤ n) {z : Module.End k (ModelSpace k)} (hz : Eqv n z) :
    Eqv (n + 2) (cupOp q m * z * capOp q m) := by
  intro τ ρ
  have e1 : capOp q m (iota (n + 2) τ (single ρ 1)) = iota n (fun j => τ (j + 2)) (capOp q m (single ρ 1)) := by
    have := capOp_iota q (N := n + 2) (m := m) (by omega) τ (single ρ (1 : k))
    simpa using this
  have e2 := hz.apply (fun j => τ (j + 2)) (capOp q m (single ρ 1))
  have e3 := cupOp_iota q (N := n) (m := m) hm (fun j => τ (j + 2)) (z (capOp q m (single ρ 1)))
  have e4 : iota (n + 2) (fun j => (fun j => τ (j + 2)) (j - 2)) (cupOp q m (z (capOp q m (single ρ 1)))) =
      iota (n + 2) τ (cupOp q m (z (capOp q m (single ρ 1)))) :=
    iota_congr (n + 2) (fun j hj => by simp only []; congr 1; omega) _
  rw [← iota_single, Module.End.mul_apply, Module.End.mul_apply, e1, e2, e3, e4]
  simp [Module.End.mul_apply]

/-- The nested sandwich of an equivariant operator is equivariant (junction `l ≤ n`). -/
lemma Eqv.nest (q : kˣ) {n l : ℕ} (hl : l ≤ n) {z : Module.End k (ModelSpace k)} (hz : Eqv n z) :
    ∀ i : ℕ, Eqv (n + 2 * i) (nestCup q l i * z * nestCap q l i) := by
  intro i
  induction i with
  | zero => simpa [nestCup, nestCap] using hz
  | succ i ih =>
    have h := Eqv.cup_mul_cap q (n := n + 2 * i) (m := l + i) (by omega) ih
    have e : nestCup q l (i + 1) * z * nestCap q l (i + 1) =
        cupOp q (l + i) * (nestCup q l i * z * nestCap q l i) * capOp q (l + i) := by
      simp only [nestCup, nestCap, mul_assoc]
    rw [e, show n + 2 * (i + 1) = n + 2 * i + 2 by ring]
    exact h

/-- Every element of the algebra generated by `e_0, …, e_{m-1}` (`m + 1 ≤ N`) does not see the tail. -/
theorem eqv_of_mem (q : kˣ) {N m : ℕ} (hm : m + 1 ≤ N) {x : Module.End k (ModelSpace k)}
    (hx : x ∈ CSub q m) : Eqv N x := by
  unfold CSub tlSub at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact eqv_modelE q (by omega)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact (eqv_one N).smul r
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-- **An equivariant operator vanishing on the window vanishes.** -/
theorem eq_zero_of_window {N : ℕ} {T : Module.End k (ModelSpace k)} (hT : Eqv N T)
    (h0 : ∀ v ∈ Win k N, T v = 0) : T = 0 := by
  apply Finsupp.lhom_ext
  intro σ c
  have hρ : (fun j => if j < N then σ j else false) ∈ tailZero N := by
    intro j hj; simp; omega
  have hσ : app N (fun j => if j < N then σ j else false) σ = σ := by
    funext j; simp only [app]; split_ifs with h1 <;> simp_all
  have h1 : T (single σ (1 : k)) = 0 := by
    have := hT σ (fun j => if j < N then σ j else false)
    rw [hσ] at this
    rw [this, h0 _ (single_mem_Win hρ 1), map_zero]
  have : (single σ c : ModelSpace k) = c • single σ 1 := by simp
  rw [this, map_smul, h1, smul_zero]; simp

/-! ### The channel idempotents -/

/-- The projector `p_c` is idempotent. -/
theorem jwAt_idem (q : kˣ) {c N : ℕ} (hc : c ≤ N) (hd : ∀ j, j < N → chebD (loopVal q) j ≠ 0) :
    jwAt q 0 c * jwAt q 0 c = (jwAt q 0 c : Module.End k (ModelSpace k)) :=
  (jwProps_of_le (isTL_shift q 0) N hd c hc).idem

/-- `e_j p_c = 0` for `j + 1 < c`. -/
theorem modelE_mul_jwAt (q : kˣ) {c N : ℕ} (hc : c ≤ N) (hd : ∀ j, j < N → chebD (loopVal q) j ≠ 0) {j : ℕ}
    (hj : j + 1 < c) : (modelE q j : Module.End k (ModelSpace k)) * jwAt q 0 c = 0 := by
  have := (jwProps_of_le (isTL_shift q 0) N hd c hc).killL j hj
  simp only [add_zero] at this
  exact this

/-- The channel idempotent `E_i = κ_i⁻¹ V_i W_i`. -/
noncomputable def Eop (q : kˣ) (a b i : ℕ) : Module.End k (ModelSpace k) :=
  (kapRec q a b i)⁻¹ • (Vop q a b i * Wop q a b i)

section algebra

variable (q : kˣ) (a b : ℕ) (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
include hd

/-- `V_i p = V_i`. -/
theorem Vop_mul_jwAt {i : ℕ} (hi : i ≤ a) (hi' : i ≤ b) :
    Vop q a b i * jwAt q 0 (a + b - 2 * i) = Vop q a b i := by
  have := jwAt_idem (k := k) q (c := a + b - 2 * i) (N := a + b + 1) (by omega) (fun j hj => hd j (by omega))
  unfold Vop; rw [mul_assoc, this]

/-- `p W_i = W_i`. -/
theorem jwAt_mul_Wop {i : ℕ} (hi : i ≤ a) (hi' : i ≤ b) :
    jwAt q 0 (a + b - 2 * i) * Wop q a b i = Wop q a b i := by
  have := jwAt_idem (k := k) q (c := a + b - 2 * i) (N := a + b + 1) (by omega) (fun j hj => hd j (by omega))
  unfold Wop; rw [← mul_assoc, ← mul_assoc, this]

/-- `Q V_i = V_i`. -/
theorem Qab_mul_Vop (i : ℕ) :
    Qab q a b * Vop q a b i = Vop q a b i := by
  have := Qab_idem (k := k) q a b (fun j hj => hd j (by omega))
  unfold Vop; rw [← mul_assoc, ← mul_assoc, this]

/-- `W_i Q = W_i`. -/
theorem Wop_mul_Qab (i : ℕ) :
    Wop q a b i * Qab q a b = Wop q a b i := by
  have := Qab_idem (k := k) q a b (fun j hj => hd j (by omega))
  unfold Wop; rw [mul_assoc, this]

/-- `E_i` is idempotent. -/
theorem Eop_idem {i : ℕ} (hi : i ≤ a) (hi' : i ≤ b)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Eop q a b i * Eop q a b i = Eop q a b i := by
  have hκ := kapRec_ne (k := k) q i a b hi hi' hq2
  unfold Eop
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have : Vop q a b i * Wop q a b i * (Vop q a b i * Wop q a b i) =
      kapRec q a b i • (Vop q a b i * Wop q a b i) := by
    calc _ = Vop q a b i * (Wop q a b i * Vop q a b i) * Wop q a b i := by simp only [mul_assoc]
      _ = Vop q a b i * (kapRec q a b i • jwAt q 0 (a + b - 2 * i)) * Wop q a b i := by
          rw [Wop_mul_Vop q a b i hi hi' hd]
      _ = kapRec q a b i • (Vop q a b i * jwAt q 0 (a + b - 2 * i) * Wop q a b i) := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = _ := by rw [Vop_mul_jwAt q a b hd hi hi']
  rw [this, smul_smul, mul_assoc, inv_mul_cancel₀ hκ, mul_one]

/-- `E_i E_j = 0` for distinct channels. -/
theorem Eop_orth (ha : 1 ≤ a) (hb : 1 ≤ b) {i j : ℕ} (hi : i ≤ a) (hi' : i ≤ b) (hj : j ≤ a) (hj' : j ≤ b)
    (hij : i ≠ j) (hq2 : ∀ m, 1 ≤ m → m ≤ a + b + 1 → (q : k) ^ (2 * m) ≠ 1) :
    Eop q a b i * Eop q a b j = 0 := by
  have h0 := channel_orth q a b i j ha hb hi hi' hj hj' hd (lamRec_ne q a b i j hi hi' hj hj' hij hq2)
  unfold Eop
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have : Vop q a b i * Wop q a b i * (Vop q a b j * Wop q a b j) = 0 := by
    calc _ = Vop q a b i * (Wop q a b i * Vop q a b j) * Wop q a b j := by simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp
  rw [this, smul_zero]

/-- `Q E_i = E_i`. -/
theorem Qab_mul_Eop (i : ℕ) : Qab q a b * Eop q a b i = Eop q a b i := by
  unfold Eop
  rw [mul_smul_comm, ← mul_assoc, Qab_mul_Vop q a b hd]

/-- `E_i Q = E_i`. -/
theorem Eop_mul_Qab (i : ℕ) : Eop q a b i * Qab q a b = Eop q a b i := by
  unfold Eop
  rw [smul_mul_assoc, mul_assoc, Wop_mul_Qab q a b hd]

end algebra

/-! ### Window and tail behaviour of `Q` and `E_i` -/

/-- The shifted projectors do not see the tail. -/
theorem eqv_jwAt (q : kˣ) {s n N : ℕ} (h : s + n ≤ N) : Eqv N (jwAt q s n : Module.End k (ModelSpace k)) := by
  rcases n with _ | n
  · unfold jwAt; rw [jw_zero]; exact eqv_one N
  · exact eqv_of_mem q (m := s + (n + 1) - 1) (by omega) (jwAt_mem q s (n + 1))

/-- `V_i` maps the window `a + b - 2 i` into the window `a + b`. -/
theorem Vop_maps (q : kˣ) {a b i : ℕ} (hia : i ≤ a) (hib : i ≤ b) :
    ∀ v ∈ Win k (a + b - 2 * i), Vop q a b i v ∈ Win k (a + b) := by
  intro v hv
  unfold Vop
  simp only [Module.End.mul_apply]
  have h0 := jwAt_preserves q (s := 0) (n := a + b - 2 * i) (N := a + b - 2 * i) (by omega) v hv
  have h1 := nestCup_preserves q (l := a - i) (c := a + b - 2 * i) (by omega) i _ h0
  rw [show a + b - 2 * i + 2 * i = a + b by omega] at h1
  have h2 := jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl _ h1
  exact jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _ h2

/-- `W_i` maps the window `a + b` into the window `a + b - 2 i`. -/
theorem Wop_maps (q : kˣ) {a b i : ℕ} (hia : i ≤ a) (hib : i ≤ b) :
    ∀ v ∈ Win k (a + b), Wop q a b i v ∈ Win k (a + b - 2 * i) := by
  intro v hv
  unfold Wop
  simp only [Module.End.mul_apply]
  have h0 := jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _
    (jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl v hv)
  have h1 := nestCap_preserves q (l := a - i) i (a + b) (by omega) _ h0
  exact jwAt_preserves q (s := 0) (n := a + b - 2 * i) (N := a + b - 2 * i) (by omega) _ h1

/-- `Q` does not see the tail. -/
theorem eqv_Qab (q : kˣ) {a b : ℕ} : Eqv (a + b) (Qab q a b : Module.End k (ModelSpace k)) :=
  (eqv_jwAt q (by omega)).mul (eqv_jwAt q le_rfl)

/-- `E_i` does not see the tail. -/
theorem eqv_Eop (q : kˣ) {a b i : ℕ} (hia : i ≤ a) (hib : i ≤ b) : Eqv (a + b) (Eop q a b i : Module.End k (ModelSpace k)) := by
  have hp : Eqv (a + b - 2 * i) (jwAt q 0 (a + b - 2 * i) * jwAt q 0 (a + b - 2 * i) :
      Module.End k (ModelSpace k)) := (eqv_jwAt q (by omega)).mul (eqv_jwAt q (by omega))
  have hn := Eqv.nest q (l := a - i) (by omega) hp i
  rw [show a + b - 2 * i + 2 * i = a + b by omega] at hn
  have hVW : Vop q a b i * Wop q a b i = Qab q a b * (nestCup q (a - i) i * (jwAt q 0 (a + b - 2 * i) *
      jwAt q 0 (a + b - 2 * i)) * nestCap q (a - i) i) * Qab q a b := by
    unfold Vop Wop; simp only [mul_assoc]
  unfold Eop
  rw [hVW]
  exact ((eqv_Qab q).mul hn |>.mul (eqv_Qab q)).smul _

/-! ### The window as a finite-dimensional space -/

instance finiteDimensional_Win (N : ℕ) : FiniteDimensional k (Win k N) := by
  haveI : Finite (tailZero N) := (tailZero_finite N).to_subtype
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := k) (R := k) (tailZero N)).symm

/-- The window is a free module. -/
instance free_Win (N : ℕ) : Module.Free k (Win k N) := Module.Free.of_divisionRing k (Win k N)

/-- Restriction of an operator that preserves the window. -/
noncomputable def resW {N : ℕ} (T : Module.End k (ModelSpace k)) (hT : ∀ v ∈ Win k N, T v ∈ Win k N) :
    Module.End k (Win k N) := LinearMap.restrict T hT

/-- The restriction acts as the operator. -/
lemma resW_apply {N : ℕ} (T : Module.End k (ModelSpace k)) (hT : ∀ v ∈ Win k N, T v ∈ Win k N) (x : Win k N) :
    ((resW T hT x : Win k N) : ModelSpace k) = T x := rfl

/-- Restriction is multiplicative. -/
lemma resW_mul {N : ℕ} (S T : Module.End k (ModelSpace k)) (hS : ∀ v ∈ Win k N, S v ∈ Win k N)
    (hT : ∀ v ∈ Win k N, T v ∈ Win k N) :
    resW S hS * resW T hT = resW (S * T) (fun v hv => hS _ (hT v hv)) := by
  ext x; rfl

/-- A restriction determines the operator on the window. -/
lemma resW_inj {N : ℕ} (S T : Module.End k (ModelSpace k)) (hS : ∀ v ∈ Win k N, S v ∈ Win k N)
    (hT : ∀ v ∈ Win k N, T v ∈ Win k N) (h : resW S hS = resW T hT) : ∀ v ∈ Win k N, S v = T v := by
  intro v hv
  have := congrArg (fun f : Module.End k (Win k N) => ((f ⟨v, hv⟩ : Win k N) : ModelSpace k)) h
  exact this

/-! ### Rank of `Q` -/

/-- `e_j Q = 0` for the generators `j` inside the two blocks. -/
theorem modelE_mul_Qab (q : kˣ) {a b j : ℕ} (hd : ∀ i, i ≤ a + b → chebD (loopVal q) i ≠ 0) (hj : Jab a b j) :
    (modelE q j : Module.End k (ModelSpace k)) * Qab q a b = 0 := by
  unfold Qab
  rcases hj with hj | ⟨hj1, hj2⟩
  · rw [← mul_assoc, modelE_mul_jwAt q (c := a) (N := a + b + 1) (by omega) (fun i hi => hd i (by omega)) (by omega),
      zero_mul]
  · have hc := (jwProps_of_le (isTL_shift q 0) (a + b + 1) (fun i hi => hd i (by omega)) a (by omega)).comm j hj1
    simp only [add_zero] at hc
    have hk := (jwProps_of_le (isTL_shift q a) (a + b + 1) (fun i hi => hd i (by omega)) b (by omega)).killL (j - a)
      (by omega)
    rw [show j - a + a = j by omega] at hk
    rw [← mul_assoc]
    have : (modelE q j : Module.End k (ModelSpace k)) * jwAt q 0 a = jwAt q 0 a * modelE q j := hc
    rw [this, mul_assoc]
    have hk' : (modelE q j : Module.End k (ModelSpace k)) * jwAt q a b = 0 := hk
    rw [hk', mul_zero]

/-- **Rank bound (A) for `Q`** on the window: `rank Q ≤ (a+1)(b+1)`. -/
theorem finrank_range_Qab_le (q : kˣ) (a b : ℕ) (hd : ∀ i, i ≤ a + b → chebD (loopVal q) i ≠ 0) :
    Module.finrank k (LinearMap.range (resW (N := a + b) (Qab q a b : Module.End k (ModelSpace k))
      (fun v hv => jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _
        (jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl v hv)))) ≤ (a + 1) * (b + 1) := by
  set R := resW (N := a + b) (Qab q a b : Module.End k (ModelSpace k))
      (fun v hv => jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _
        (jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl v hv)) with hR
  set U : Submodule k (ModelSpace k) := (LinearMap.range R).map (Win k (a + b)).subtype with hU
  have hUW : U ≤ Win k (a + b) := by
    rintro _ ⟨x, _, rfl⟩; exact x.2
  have hker : ∀ v ∈ U, ∀ j, Jab a b j → modelE q j v = 0 := by
    rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩ j hj
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (y : ModelSpace k)) (modelE_mul_Qab (k := k) q hd hj)
    rw [Submodule.subtype_apply]
    have e : ((R y : Win k (a + b)) : ModelSpace k) = Qab q a b (y : ModelSpace k) := by rw [hR]; rfl
    rw [e]
    simpa using this
  have : FiniteDimensional k U := inferInstance
  have h1 := finrank_kernel_le q a b U hUW hker
  have h2 : Module.finrank k (LinearMap.range R) = Module.finrank k U :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Win k (a + b)).subtype
      (Submodule.injective_subtype _) (LinearMap.range R))
  rw [h2]; exact h1

/-- `E_i` preserves the window `a + b`. -/
theorem Eop_maps (q : kˣ) {a b i : ℕ} (hia : i ≤ a) (hib : i ≤ b) :
    ∀ v ∈ Win k (a + b), (Eop q a b i : Module.End k (ModelSpace k)) v ∈ Win k (a + b) := by
  intro v hv
  unfold Eop
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (Vop_maps q hia hib _ (Wop_maps q hia hib v hv))

/-- `Q` preserves the window `a + b`. -/
theorem Qab_maps (q : kˣ) (a b : ℕ) : ∀ v ∈ Win k (a + b), (Qab q a b : Module.End k (ModelSpace k)) v ∈ Win k (a + b) :=
  fun v hv => jwAt_preserves q (s := 0) (n := a) (N := a + b) (by omega) _
    (jwAt_preserves q (s := a) (n := b) (N := a + b) le_rfl v hv)

/-- **Rank bound (B)**: `rank E_i ≥ a + b - 2 i + 1`. -/
theorem le_finrank_range_Eop (q : kˣ) {a b i : ℕ} (hia : i ≤ a) (hib : i ≤ b)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    a + b - 2 * i + 1 ≤ Module.finrank k (LinearMap.range (resW (N := a + b) (Eop q a b i : Module.End k (ModelSpace k))
      (Eop_maps q hia hib))) := by
  have hκ := kapRec_ne (k := k) q i a b hia hib hq2
  set c := a + b - 2 * i with hc
  -- the vectors `V D_m`, as elements of the range of `E_i` restricted to the window
  have hfix : ∀ m : Fin (c + 1), (Eop q a b i : Module.End k (ModelSpace k)) (Vop q a b i (dicke q c m)) =
      Vop q a b i (dicke q c m) := by
    intro m
    have h1 := congrArg (fun T : Module.End k (ModelSpace k) => T (dicke q c m))
      (Wop_mul_Vop q a b i hia hib hd)
    have e : (jwAt q 0 (a + b - 2 * i) : Module.End k (ModelSpace k)) (dicke q c m) = dicke q c m :=
      jwAt_dicke q c m
    simp only [Module.End.mul_apply, LinearMap.smul_apply, e] at h1
    unfold Eop
    rw [LinearMap.smul_apply, Module.End.mul_apply, h1, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  let g : Fin (c + 1) → LinearMap.range (resW (N := a + b) (Eop q a b i : Module.End k (ModelSpace k))
      (Eop_maps q hia hib)) := fun m =>
    ⟨⟨Vop q a b i (dicke q c m), Vop_dicke_mem q a b i m hia hib⟩, ⟨⟨Vop q a b i (dicke q c m),
      Vop_dicke_mem q a b i m hia hib⟩, Subtype.ext (hfix m)⟩⟩
  have hli : LinearIndependent k g := by
    have h1 := Vop_dicke_independent (k := k) q a b i hia hib hd hq2
    refine LinearIndependent.of_comp ((Submodule.subtype _) ∘ₗ (Submodule.subtype _)) ?_
    exact h1
  have := hli.fintype_card_le_finrank
  simpa using this

/-! ### Assembly -/

/-- The channel dimensions add up to the dimension bound: `Σ_{i ≤ min a b} (a + b - 2 i + 1) = (a+1)(b+1)`. -/
theorem sum_channel_dims (a b : ℕ) :
    (a + 1) * (b + 1) ≤ ∑ i ∈ Finset.range (min a b + 1), (a + b - 2 * i + 1) := by
  have key : ∀ m, m ≤ a → m ≤ b → ∑ i ∈ Finset.range (m + 1), (a + b - 2 * i + 1) + m * (m + 1) =
      (m + 1) * (a + b + 1) := by
    intro m
    induction m with
    | zero => intro _ _; simp
    | succ m ih =>
      intro h1 h2
      have := ih (by omega) (by omega)
      rw [Finset.sum_range_succ]
      obtain ⟨t, ht⟩ : ∃ t, a + b - 2 * (m + 1) + 1 = t ∧ t + 2 * (m + 1) = a + b + 1 :=
        ⟨a + b - 2 * (m + 1) + 1, rfl, by omega⟩
      rw [ht.1]
      nlinarith [ht.2]
  have h := key (min a b) (min_le_left _ _) (min_le_right _ _)
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab] at h ⊢
    nlinarith [h]
  · rw [min_eq_right hab] at h ⊢
    nlinarith [h]

/-- Equal operators have equal restrictions. -/
lemma resW_congr {N : ℕ} {S T : Module.End k (ModelSpace k)} (h : S = T) (hS : ∀ v ∈ Win k N, S v ∈ Win k N)
    (hT : ∀ v ∈ Win k N, T v ∈ Win k N) : resW S hS = resW T hT := by
  subst h; rfl

/-- Equivariant operators are closed under finite sums. -/
lemma Eqv.sum {N : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Module.End k (ModelSpace k)} (h : ∀ i ∈ s, Eqv N (f i)) :
    Eqv N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (eqv_one (k := k) N).smul 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The fusion identity** `Q(a,b) = Σ_{i ≤ min a b} E_i` in the model of the Temperley–Lieb algebra. -/
theorem fusion_identity [CharZero k] (q : kˣ) (a b : ℕ)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Qab q a b = ∑ i : Fin (min a b + 1), Eop q a b i := by
  have hia : ∀ i : Fin (min a b + 1), (i : ℕ) ≤ a := fun i => by have := i.2; omega
  have hib : ∀ i : Fin (min a b + 1), (i : ℕ) ≤ b := fun i => by have := i.2; omega
  have hQm := Qab_maps (k := k) q a b
  have hEm : ∀ i : Fin (min a b + 1), ∀ v ∈ Win k (a + b), (Eop q a b i : Module.End k (ModelSpace k)) v ∈ Win k (a + b) :=
    fun i => Eop_maps q (hia i) (hib i)
  have hcomp : Qab q a b = ∑ i : Fin (min a b + 1), Eop q a b i := by
    -- on the window
    have hwin : ∀ v ∈ Win k (a + b), (Qab q a b : Module.End k (ModelSpace k)) v =
        (∑ i : Fin (min a b + 1), (Eop q a b i : Module.End k (ModelSpace k))) v := by
      have hrank := complete_of_rank (K := k) (V := Win k (a + b)) (ι := Fin (min a b + 1))
        (resW (Qab q a b : Module.End k (ModelSpace k)) hQm)
        (fun i => resW (Eop q a b i : Module.End k (ModelSpace k)) (hEm i))
        (by
          show resW _ hQm * resW _ hQm = resW _ hQm
          rw [resW_mul]
          exact resW_congr (Qab_idem q a b (fun j hj => hd j (by omega))) _ _)
        (fun i => by
          show resW _ (hEm i) * resW _ (hEm i) = resW _ (hEm i)
          rw [resW_mul]
          exact resW_congr (Eop_idem q a b hd (hia i) (hib i) hq2) _ _)
        (fun i j hij => by
          have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
          have hm : 1 ≤ min a b := by have h1 := i.2; have h2 := j.2; omega
          have this : (Eop q a b i * Eop q a b j : Module.End k (ModelSpace k)) = 0 :=
            Eop_orth q a b hd (by omega) (by omega) (hia i) (hib i) (hia j) (hib j) hne hq2
          refine LinearMap.ext fun x => Subtype.ext ?_
          have h2 := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k)) this
          simpa [resW_apply] using h2)
        (fun i => by
          rw [resW_mul]
          exact resW_congr (Qab_mul_Eop q a b hd i) _ _)
        (fun i => by
          rw [resW_mul]
          exact resW_congr (Eop_mul_Qab q a b hd i) _ _)
        (by
          have h1 := finrank_range_Qab_le (k := k) q a b (fun j hj => hd j (by omega))
          have h2 : ∑ i : Fin (min a b + 1), (a + b - 2 * (i : ℕ) + 1) ≤
              ∑ i : Fin (min a b + 1), Module.finrank k (LinearMap.range
                (resW (Eop q a b i : Module.End k (ModelSpace k)) (hEm i))) :=
            Finset.sum_le_sum fun i _ => le_finrank_range_Eop q (hia i) (hib i) hd hq2
          have h3 := sum_channel_dims a b
          rw [← Fin.sum_univ_eq_sum_range (fun i => a + b - 2 * i + 1) (min a b + 1)] at h3
          exact h1.trans (h3.trans h2))
      intro v hv
      have := congrArg (fun f : Module.End k (Win k (a + b)) => ((f ⟨v, hv⟩ : Win k (a + b)) : ModelSpace k)) hrank
      simpa [LinearMap.sum_apply, Submodule.coe_sum, resW_apply] using this
    -- tail equivariance
    have hT : Eqv (a + b) ((Qab q a b : Module.End k (ModelSpace k)) -
        ∑ i : Fin (min a b + 1), (Eop q a b i : Module.End k (ModelSpace k))) := by
      have h1 : Eqv (a + b) (Qab q a b : Module.End k (ModelSpace k)) := eqv_Qab q
      have h2 : Eqv (a + b) (∑ i : Fin (min a b + 1), (Eop q a b i : Module.End k (ModelSpace k))) :=
        Eqv.sum _ fun i _ => eqv_Eop q (hia i) (hib i)
      have := h1.add (h2.smul (-1 : k))
      have e : ((Qab q a b : Module.End k (ModelSpace k)) -
          ∑ i : Fin (min a b + 1), (Eop q a b i : Module.End k (ModelSpace k))) =
          (Qab q a b : Module.End k (ModelSpace k)) +
          (-1 : k) • ∑ i : Fin (min a b + 1), (Eop q a b i : Module.End k (ModelSpace k)) := by
        refine LinearMap.ext fun v => ?_
        simp [sub_eq_add_neg]
      rw [e]; exact this
    have hz := eq_zero_of_window hT (fun v hv => by
      rw [LinearMap.sub_apply, hwin v hv, sub_self])
    exact sub_eq_zero.mp hz
  exact hcomp

/-- **The rank of the channel is exactly `a + b - 2i + 1`** on the window. -/
theorem finrank_range_Eop_eq [CharZero k] (q : kˣ) (a b : ℕ)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) (i : Fin (min a b + 1)) :
    Module.finrank k (LinearMap.range (resW (N := a + b) (Eop q a b i : Module.End k (ModelSpace k))
      (Eop_maps q ((Nat.lt_succ_iff.mp i.2).trans (min_le_left _ _)) ((Nat.lt_succ_iff.mp i.2).trans (min_le_right _ _)))))
      = a + b - 2 * (i : ℕ) + 1 := by
  have hia : ∀ i : Fin (min a b + 1), (i : ℕ) ≤ a := fun i => (Nat.lt_succ_iff.mp i.2).trans (min_le_left _ _)
  have hib : ∀ i : Fin (min a b + 1), (i : ℕ) ≤ b := fun i => (Nat.lt_succ_iff.mp i.2).trans (min_le_right _ _)
  have hQm := Qab_maps (k := k) q a b
  have hEm : ∀ i : Fin (min a b + 1), ∀ v ∈ Win k (a + b), (Eop q a b i : Module.End k (ModelSpace k)) v ∈ Win k (a + b) :=
    fun i => Eop_maps q (hia i) (hib i)
  set R : Fin (min a b + 1) → Module.End k (Win k (a + b)) :=
    fun i => resW (Eop q a b i : Module.End k (ModelSpace k)) (hEm i) with hR
  set RQ : Module.End k (Win k (a + b)) := resW (Qab q a b : Module.End k (ModelSpace k)) hQm with hRQ
  have hfi := fusion_identity (k := k) q a b hd hq2
  have hsum : RQ = ∑ i, R i := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k)) hfi
    simpa [hRQ, hR, LinearMap.sum_apply, Submodule.coe_sum, resW_apply] using this
  have hidQ : IsIdempotentElem RQ := by
    show RQ * RQ = RQ
    rw [hRQ, resW_mul]
    exact resW_congr (Qab_idem q a b (fun j hj => hd j (by omega))) _ _
  have hidE : ∀ i, IsIdempotentElem (R i) := fun i => by
    show R i * R i = R i
    simp only [hR]
    rw [resW_mul]
    exact resW_congr (Eop_idem q a b hd (hia i) (hib i) hq2) _ _
  have tr : ∀ {X : Module.End k (Win k (a + b))}, IsIdempotentElem X →
      LinearMap.trace k (Win k (a + b)) X = (Module.finrank k (LinearMap.range X) : k) :=
    fun {X} (hX : IsIdempotentElem X) => trace_idempotent (K := k) (V := Win k (a + b)) hX
  have h1 : (Module.finrank k (LinearMap.range RQ) : k) = ∑ i, (Module.finrank k (LinearMap.range (R i)) : k) := by
    rw [← tr hidQ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => tr (hidE i)
  have h2 : Module.finrank k (LinearMap.range RQ) = ∑ i, Module.finrank k (LinearMap.range (R i)) := by
    exact_mod_cast h1
  have hA := finrank_range_Qab_le (k := k) q a b (fun j hj => hd j (by omega))
  have hB := sum_channel_dims a b
  rw [← Fin.sum_univ_eq_sum_range (fun i => a + b - 2 * i + 1) (min a b + 1)] at hB
  have hlow : ∀ i ∈ (Finset.univ : Finset (Fin (min a b + 1))), a + b - 2 * (i : ℕ) + 1 ≤
      Module.finrank k (LinearMap.range (R i)) := fun i _ => le_finrank_range_Eop q (hia i) (hib i) hd hq2
  have hle : ∑ i : Fin (min a b + 1), (a + b - 2 * (i : ℕ) + 1) ≤
      ∑ i : Fin (min a b + 1), Module.finrank k (LinearMap.range (R i)) := Finset.sum_le_sum hlow
  have heq : ∑ i : Fin (min a b + 1), (a + b - 2 * (i : ℕ) + 1) =
      ∑ i : Fin (min a b + 1), Module.finrank k (LinearMap.range (R i)) := by
    apply le_antisymm hle
    rw [← h2]
    exact hA.trans hB
  exact ((Finset.sum_eq_sum_iff_of_le hlow).mp heq i (Finset.mem_univ i)).symm

/-- `Q(a,b)` preserves every window containing the two blocks. -/
theorem Qab_maps_gen (q : kˣ) {a b M : ℕ} (hM : a + b ≤ M) :
    ∀ v ∈ Win k M, (Qab q a b : Module.End k (ModelSpace k)) v ∈ Win k M :=
  fun v hv => jwAt_preserves q (s := 0) (n := a) (N := M) (by omega) _
    (jwAt_preserves q (s := a) (n := b) (N := M) hM v hv)

/-- `V_i` maps the window `M - 2 i` into the window `M`. -/
theorem Vop_maps_gen (q : kˣ) {a b i M : ℕ} (hia : i ≤ a) (hib : i ≤ b) (hM : a + b ≤ M) :
    ∀ v ∈ Win k (M - 2 * i), Vop q a b i v ∈ Win k M := by
  intro v hv
  unfold Vop
  simp only [Module.End.mul_apply]
  have h0 := jwAt_preserves q (s := 0) (n := a + b - 2 * i) (N := M - 2 * i) (by omega) v hv
  have h1 := nestCup_preserves q (l := a - i) (c := M - 2 * i) (by omega) i _ h0
  rw [show M - 2 * i + 2 * i = M by omega] at h1
  exact Qab_maps_gen q hM _ h1

/-- `W_i` maps the window `M` into the window `M - 2 i`. -/
theorem Wop_maps_gen (q : kˣ) {a b i M : ℕ} (hia : i ≤ a) (hib : i ≤ b) (hM : a + b ≤ M) :
    ∀ v ∈ Win k M, Wop q a b i v ∈ Win k (M - 2 * i) := by
  intro v hv
  unfold Wop
  simp only [Module.End.mul_apply]
  have h0 := Qab_maps_gen q hM v hv
  have h1 := nestCap_preserves q (l := a - i) i M (by omega) _ h0
  exact jwAt_preserves q (s := 0) (n := a + b - 2 * i) (N := M - 2 * i) (by omega) _ h1

end Lightlike.TemperleyLieb
