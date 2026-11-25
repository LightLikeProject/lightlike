import Mathlib
import Lightlike.TemperleyLieb.Shift

/-!
# Local operators commute with translated operators

An operator acting on the first `s` strands commutes with `sh s Y` (`Y` acts on the tail); a cup
inserted at a position `m ≤ s` carries `sh s Y` to `sh (s+2) Y`.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- Gluing commutes with `set2` below the head. -/
lemma pre_set2_lt {s j : ℕ} (hj : j + 1 < s) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre s (set2 σ j x y) ρ = set2 (pre s σ ρ) j x y := by
  funext n
  simp only [pre, set2, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | simp_all

/-- The tail is unchanged by `set2` below the head. -/
lemma tl_set2_lt {s j : ℕ} (hj : j + 1 < s) (σ : ℕ → Bool) (x y : Bool) :
    tl s (set2 σ j x y) = tl s σ := by
  funext n
  simp only [tl, set2, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Gluing commutes with `insertTwo` below the head, the head growing by two. -/
lemma pre_insertTwo_le {s m : ℕ} (hm : m ≤ s) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre (s + 2) (insertTwo σ m x y) ρ = insertTwo (pre s σ ρ) m x y := by
  funext n
  simp only [pre, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | skip

/-- The tail of an insertion below the head. -/
lemma tl_insertTwo_le {s m : ℕ} (hm : m ≤ s) (σ : ℕ → Bool) (x y : Bool) :
    tl (s + 2) (insertTwo σ m x y) = tl s σ := by
  funext n
  simp only [tl, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- `e_j` below the head acts on the head of a glued vector. -/
lemma modelE_lmap (q : kˣ) {s j : ℕ} (hj : j + 1 < s) (σ : ℕ → Bool) (w : ModelSpace k) :
    modelE q j (Finsupp.lmapDomain k k (pre s σ) w) =
      match σ j, σ (j + 1) with
      | true, false => Finsupp.lmapDomain k k (pre s (set2 σ j false true)) w -
          (q : k) • Finsupp.lmapDomain k k (pre s σ) w
      | false, true => Finsupp.lmapDomain k k (pre s (set2 σ j true false)) w -
          ((q⁻¹ : kˣ) : k) • Finsupp.lmapDomain k k (pre s σ) w
      | _, _ => 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp; split <;> rfl
  | add f g hf hg =>
    simp only [map_add, hf, hg]
    split <;> simp [add_sub_add_comm, smul_add]
  | single ρ c =>
    have h0 : pre s σ ρ j = σ j := by simp only [pre]; rw [if_pos (by omega)]
    have h1 : pre s σ ρ (j + 1) = σ (j + 1) := by simp only [pre]; rw [if_pos hj]
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, modelE_single]
    simp only [eBasis, h0, h1]
    rcases hx : σ j <;> rcases hy : σ (j + 1) <;> simp [pre_set2_lt hj, Finsupp.mapDomain_single, smul_sub, Finsupp.smul_single, mul_comm]

/-- A generator below the head commutes with every translated operator. -/
theorem modelE_comm_sh (q : kˣ) {s j : ℕ} (hj : j + 1 < s) (Y : Module.End k (ModelSpace k)) :
    modelE q j * sh s Y = sh s Y * modelE q j := by
  apply Finsupp.lhom_ext
  intro τ c
  have hτ : (single τ c : ModelSpace k) = c • Finsupp.lmapDomain k k (pre s τ) (single (tl s τ) 1) := by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, pre_tl]; simp
  rw [hτ, Module.End.mul_apply, Module.End.mul_apply, map_smul, map_smul, map_smul, sh_lmapDomain, modelE_lmap q hj]
  rw [modelE_lmap q hj]
  rcases hx : τ j <;> rcases hy : τ (j + 1) <;> simp only [map_sub, map_smul, sh_lmapDomain, map_zero, smul_zero]

/-- A cup at a position `m ≤ s` acts on the head of a glued vector. -/
lemma cupOp_lmap (q : kˣ) {s m : ℕ} (hm : m ≤ s) (σ : ℕ → Bool) (w : ModelSpace k) :
    cupOp q m (Finsupp.lmapDomain k k (pre s σ) w) =
      Finsupp.lmapDomain k k (pre (s + 2) (insertTwo σ m false true)) w -
        (q : k) • Finsupp.lmapDomain k k (pre (s + 2) (insertTwo σ m true false)) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg]
    rw [smul_add]; abel
  | single ρ c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, cupOp_single]
    simp only [cupBasis, pre_insertTwo_le hm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      smul_sub, Finsupp.smul_single, smul_eq_mul, mul_comm, mul_one]

/-- A cup at a position `m ≤ s` carries `sh s Y` to `sh (s+2) Y`. -/
theorem cupOp_comm_sh (q : kˣ) {s m : ℕ} (hm : m ≤ s) (Y : Module.End k (ModelSpace k)) :
    cupOp q m * sh s Y = sh (s + 2) Y * cupOp q m := by
  apply Finsupp.lhom_ext
  intro τ c
  have hτ : (single τ c : ModelSpace k) = c • Finsupp.lmapDomain k k (pre s τ) (single (tl s τ) 1) := by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, pre_tl]; simp
  have h1 : (single (insertTwo τ m false true) (1 : k) : ModelSpace k) =
      Finsupp.lmapDomain k k (pre (s + 2) (insertTwo τ m false true)) (single (tl s τ) 1) := by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ← tl_insertTwo_le hm τ false true, pre_tl]
  have h2 : (single (insertTwo τ m true false) (1 : k) : ModelSpace k) =
      Finsupp.lmapDomain k k (pre (s + 2) (insertTwo τ m true false)) (single (tl s τ) 1) := by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ← tl_insertTwo_le hm τ true false, pre_tl]
  rw [Module.End.mul_apply, Module.End.mul_apply, hτ, map_smul, map_smul, map_smul, map_smul,
    sh_lmapDomain, cupOp_lmap q hm, cupOp_lmap q hm]
  simp only [cupBasis, h1, h2, map_sub, map_smul, sh_lmapDomain]

/-- Every element of `C(N)` commutes with a translate `sh s Y` once `N < s`. -/
theorem CSub_comm_sh (q : kˣ) {N s : ℕ} (hN : N < s) {X : Module.End k (ModelSpace k)}
    (hX : X ∈ CSub (k := k) q N) (Y : Module.End k (ModelSpace k)) : X * sh s Y = sh s Y * X := by
  unfold CSub tlSub at hX
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact modelE_comm_sh q (by omega) Y
  | algebraMap r => exact Algebra.commutes r (sh s Y)
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

/-- A nest of cups at the positions `≥ l`, with `l ≤ s`, carries `sh s Y` to `sh (s + 2i) Y`. -/
theorem nestCup_comm_sh (q : kˣ) {s l : ℕ} (hl : l ≤ s) (Y : Module.End k (ModelSpace k)) :
    ∀ i, nestCup q l i * sh s Y = sh (s + 2 * i) Y * nestCup q l i := by
  intro i
  induction i with
  | zero => simp [nestCup]
  | succ i ih =>
    rw [nestCup, mul_assoc, ih, ← mul_assoc, cupOp_comm_sh q (by omega) Y, mul_assoc,
      show s + 2 * i + 2 = s + 2 * (i + 1) by ring]

/-- `jwAt q u n` commutes with `sh s Y` when it lives on the first `s` strands. -/
theorem jwAt_comm_sh (q : kˣ) {u n s : ℕ} (h : u + n ≤ s) (Y : Module.End k (ModelSpace k)) :
    jwAt q u n * sh s Y = sh s Y * jwAt q u n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [jwAt, jw_zero, jw_one]
  · exact CSub_comm_sh q (N := u + n - 1) (by omega) (jwAt_mem q u n) Y

/-- **The vertex `V` carries a translate of the tail through.** -/
theorem Vop_comm_sh (q : kˣ) {a b e : ℕ} (hea : e ≤ a) (heb : e ≤ b) (Y : Module.End k (ModelSpace k)) :
    Vop q a b e * sh (a + b - 2 * e) Y = sh (a + b) Y * Vop q a b e := by
  have hs : a + b - 2 * e + 2 * e = a + b := by omega
  unfold Vop Qab
  rw [mul_assoc, mul_assoc, jwAt_comm_sh q (u := 0) (by omega) Y, ← mul_assoc (nestCup q _ _),
    nestCup_comm_sh q (by omega) Y, hs, ← mul_assoc, ← mul_assoc, mul_assoc (jwAt q 0 a),
    jwAt_comm_sh q (u := a) (by omega) Y]
  rw [← mul_assoc, jwAt_comm_sh q (u := 0) (by omega) Y]
  simp only [mul_assoc]

end Lightlike.TemperleyLieb
