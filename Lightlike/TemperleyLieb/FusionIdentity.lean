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

lemma Eqv.mul {N : ℕ} {S T : Module.End k (ModelSpace k)} (hS : Eqv N S) (hT : Eqv N T) : Eqv N (S * T) := by
  intro τ ρ
  rw [Module.End.mul_apply, hT τ ρ, hS.apply, Module.End.mul_apply]

lemma Eqv.add {N : ℕ} {S T : Module.End k (ModelSpace k)} (hS : Eqv N S) (hT : Eqv N T) : Eqv N (S + T) := by
  intro τ ρ
  rw [LinearMap.add_apply, hS τ ρ, hT τ ρ, LinearMap.add_apply, map_add]

lemma Eqv.smul {N : ℕ} {T : Module.End k (ModelSpace k)} (r : k) (hT : Eqv N T) : Eqv N (r • T) := by
  intro τ ρ
  rw [LinearMap.smul_apply, hT τ ρ, LinearMap.smul_apply, map_smul]

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

end Lightlike.TemperleyLieb
