import Mathlib
import Lightlike.TemperleyLieb.Iterated

/-!
# Translation of operators by `s` strands

`sh s T` acts as `T` on the strands `s, s + 1, …` and as the identity on the first `s` strands.  It is an algebra
homomorphism sending `e_j`, `cup_m`, `cap_m` to `e_{j+s}`, `cup_{m+s}`, `cap_{m+s}`, hence the Jones–Wenzl projector
`jwAt q 0 n` to `jwAt q s n`.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical
open Finsupp

variable {k : Type*} [Field k]

/-- Glue the first `s` bits of `σ` to a sequence `ρ` placed after them. -/
def pre (s : ℕ) (σ ρ : ℕ → Bool) : ℕ → Bool := fun j => if j < s then σ j else ρ (j - s)

/-- Forget the first `s` bits. -/
def tl (s : ℕ) (σ : ℕ → Bool) : ℕ → Bool := fun j => σ (j + s)

/-- Gluing the head back to the tail returns the sequence. -/
lemma pre_tl (s : ℕ) (σ : ℕ → Bool) : pre s σ (tl s σ) = σ := by
  funext j; simp only [pre, tl]; split_ifs with h
  · rfl
  · congr 1; omega

/-- The tail of a glued sequence. -/
lemma tl_pre (s : ℕ) (σ ρ : ℕ → Bool) : tl s (pre s σ ρ) = ρ := by
  funext j; simp [pre, tl]

/-- Gluing twice keeps the first head. -/
lemma pre_pre (s : ℕ) (σ ρ τ : ℕ → Bool) : pre s (pre s σ ρ) τ = pre s σ τ := by
  funext j; simp only [pre]; split_ifs <;> rfl

/-- Gluing twice keeps the first head (as functions). -/
lemma pre_pre' (s : ℕ) (σ ρ : ℕ → Bool) : pre s (pre s σ ρ) = pre s σ := funext (pre_pre s σ ρ)

/-- Translation by `s` strands, as a linear map on the operators. -/
noncomputable def sh (s : ℕ) (T : Module.End k (ModelSpace k)) : Module.End k (ModelSpace k) :=
  Finsupp.lsum k fun σ => LinearMap.toSpanSingleton k _
    (Finsupp.lmapDomain k k (pre s σ) (T (single (tl s σ) 1)))

/-- Translation on a basis vector. -/
lemma sh_single (s : ℕ) (T : Module.End k (ModelSpace k)) (σ : ℕ → Bool) (c : k) :
    sh s T (single σ c) = c • Finsupp.lmapDomain k k (pre s σ) (T (single (tl s σ) 1)) := by
  simp [sh]

/-- Translation acts as the operator on the part after the head. -/
lemma sh_lmapDomain (s : ℕ) (T : Module.End k (ModelSpace k)) (σ : ℕ → Bool) (w : ModelSpace k) :
    sh s T (Finsupp.lmapDomain k k (pre s σ) w) = Finsupp.lmapDomain k k (pre s σ) (T w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single ρ c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, sh_single, tl_pre]
    have : (single ρ c : ModelSpace k) = c • single ρ 1 := by simp
    rw [pre_pre', this, map_smul, map_smul]

/-- Translation is multiplicative. -/
lemma sh_mul (s : ℕ) (S T : Module.End k (ModelSpace k)) : sh s (S * T) = sh s S * sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [Module.End.mul_apply, sh_single, sh_single, map_smul, sh_lmapDomain, Module.End.mul_apply]

/-- Translation preserves the identity. -/
lemma sh_one (s : ℕ) : sh s (1 : Module.End k (ModelSpace k)) = 1 := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [sh_single, Module.End.one_apply]
  simp [pre_tl]

/-- Gluing commutes with `set2`. -/
lemma pre_set2 (s j : ℕ) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre s σ (set2 ρ j x y) = set2 (pre s σ ρ) (j + s) x y := by
  funext n
  simp only [pre, set2, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- Gluing commutes with `insertTwo`. -/
lemma pre_insertTwo (s m : ℕ) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre s σ (insertTwo ρ m x y) = insertTwo (pre s σ ρ) (m + s) x y := by
  funext n
  simp only [pre, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- Gluing commutes with `removeTwo`. -/
lemma pre_removeTwo (s m : ℕ) (σ ρ : ℕ → Bool) :
    pre s σ (removeTwo ρ m) = removeTwo (pre s σ ρ) (m + s) := by
  funext n
  simp only [pre, removeTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- Gluing on a basis vector. -/
lemma lmap_single (s : ℕ) (σ ρ : ℕ → Bool) (c : k) :
    Finsupp.lmapDomain k k (pre s σ) (single ρ c) = single (pre s σ ρ) c := by
  simp

/-- Translation sends `e_j` to `e_{j+s}`. -/
theorem sh_modelE (q : kˣ) (s j : ℕ) : sh s (modelE q j : Module.End k (ModelSpace k)) = modelE q (j + s) := by
  apply Finsupp.lhom_ext
  intro σ c
  have h0 : tl s σ j = σ (j + s) := rfl
  have h1 : tl s σ (j + 1) = σ (j + s + 1) := by simp only [tl]; congr 1; omega
  rw [sh_single, modelE_single, modelE_single, one_smul]
  congr 1
  simp only [eBasis, h0, h1]
  rcases σ (j + s) with _ | _ <;> rcases σ (j + s + 1) with _ | _ <;>
    simp [lmap_single, pre_set2, pre_tl, map_sub, map_smul]

/-- Translation sends the cap `cap_m` to `cap_{m+s}`. -/
theorem sh_capOp (q : kˣ) (s m : ℕ) : sh s (capOp q m : Module.End k (ModelSpace k)) = capOp q (m + s) := by
  apply Finsupp.lhom_ext
  intro σ c
  have h0 : tl s σ m = σ (m + s) := rfl
  have h1 : tl s σ (m + 1) = σ (m + s + 1) := by simp only [tl]; congr 1; omega
  rw [sh_single, capOp_single, capOp_single, one_smul]
  congr 1
  simp only [capBasis, h0, h1, lmap_single, pre_removeTwo, pre_tl]

/-- Translation sends the cup `cup_m` to `cup_{m+s}`. -/
theorem sh_cupOp (q : kˣ) (s m : ℕ) : sh s (cupOp q m : Module.End k (ModelSpace k)) = cupOp q (m + s) := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [sh_single, cupOp_single, cupOp_single, one_smul]
  congr 1
  simp only [cupBasis, map_sub, map_smul, lmap_single, pre_insertTwo, pre_tl]

/-- Translation is additive. -/
lemma sh_add (s : ℕ) (S T : Module.End k (ModelSpace k)) : sh s (S + T) = sh s S + sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [LinearMap.add_apply, sh_single, sh_single, sh_single, LinearMap.add_apply, map_add, smul_add]

/-- Translation commutes with scalars. -/
lemma sh_smul (s : ℕ) (r : k) (T : Module.End k (ModelSpace k)) : sh s (r • T) = r • sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [LinearMap.smul_apply, sh_single, sh_single, LinearMap.smul_apply, map_smul, smul_comm]

/-- Translation preserves differences. -/
lemma sh_sub (s : ℕ) (S T : Module.End k (ModelSpace k)) : sh s (S - T) = sh s S - sh s T := by
  have : S - T = S + (-1 : k) • T := by
    refine LinearMap.ext fun v => ?_; simp [sub_eq_add_neg]
  rw [this, sh_add, sh_smul]
  refine LinearMap.ext fun v => ?_; simp [sub_eq_add_neg]

/-- Translation sends the projector on the strands `u, …` to the projector on `u + t, …`. -/
theorem sh_jwAt (q : kˣ) (t u : ℕ) : ∀ n, sh t (jwAt q u n : Module.End k (ModelSpace k)) = jwAt q (u + t) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jwAt, jw_zero, sh_one]
    · simp [jwAt, jw_one, sh_one]
    · have h2 : ∀ s', jwAt q s' (n + 2) = jwAt q s' (n + 1) -
          (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
            (jwAt q s' (n + 1) * modelE q (n + s') * jwAt q s' (n + 1)) := fun s' => jw_succ_succ n
      rw [h2 u, h2 (u + t), sh_sub, sh_smul, sh_mul, sh_mul, ih (n + 1) (by omega), sh_modelE,
        show n + u + t = n + (u + t) by ring]

/-- Translation preserves zero. -/
lemma sh_zero (s : ℕ) : sh s (0 : Module.End k (ModelSpace k)) = 0 := by
  apply Finsupp.lhom_ext
  intro σ c
  simp [sh_single]

/-- Translation preserves finite sums. -/
lemma sh_sum {ι : Type*} (s : ℕ) (S : Finset ι) (f : ι → Module.End k (ModelSpace k)) :
    sh s (∑ i ∈ S, f i) = ∑ i ∈ S, sh s (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sh_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sh_add, ih]

/-- Translation sends the nested cups at the junction `l` to the nested cups at `l + s`. -/
theorem sh_nestCup (q : kˣ) (s l : ℕ) : ∀ i, sh s (nestCup q l i : Module.End k (ModelSpace k)) = nestCup q (l + s) i := by
  intro i
  induction i with
  | zero => simp [nestCup, sh_one]
  | succ i ih => rw [nestCup, nestCup, sh_mul, ih, sh_cupOp, show l + i + s = l + s + i by ring]

/-- Translation sends the nested caps at the junction `l` to the nested caps at `l + s`. -/
theorem sh_nestCap (q : kˣ) (s l : ℕ) : ∀ i, sh s (nestCap q l i : Module.End k (ModelSpace k)) = nestCap q (l + s) i := by
  intro i
  induction i with
  | zero => simp [nestCap, sh_one]
  | succ i ih => rw [nestCap, nestCap, sh_mul, ih, sh_capOp, show l + i + s = l + s + i by ring]

/-- The shifted projector is idempotent. -/
theorem jwAt_shift_idem (q : kˣ) {s c N : ℕ} (hc : c ≤ N) (hd : ∀ j, j < N → chebD (loopVal q) j ≠ 0) :
    (jwAt q s c : Module.End k (ModelSpace k)) * jwAt q s c = jwAt q s c := by
  have := jwAt_idem (k := k) q hc hd
  have h := congrArg (sh s) this
  rw [sh_mul, sh_jwAt] at h
  simpa using h

/-- The nested cups at junction `≥ a` commute with `p_a` on the left. -/
theorem jwAt_mul_nestCup (q : kˣ) {a l : ℕ} (hl : a ≤ l) :
    ∀ i, (jwAt q 0 a : Module.End k (ModelSpace k)) * nestCup q l i = nestCup q l i * jwAt q 0 a := by
  intro i
  induction i with
  | zero => simp [nestCup]
  | succ i ih =>
    rw [nestCup, ← mul_assoc, jwAt_mul_cupOp q a (by omega), mul_assoc, ih, ← mul_assoc]

/-- The nested caps at junction `≥ a` commute with `p_a` on the left. -/
theorem jwAt_mul_nestCap (q : kˣ) {a l : ℕ} (hl : a ≤ l) :
    ∀ i, (jwAt q 0 a : Module.End k (ModelSpace k)) * nestCap q l i = nestCap q l i * jwAt q 0 a := by
  intro i
  induction i with
  | zero => simp [nestCap]
  | succ i ih =>
    rw [nestCap, ← mul_assoc, ih, mul_assoc, jwAt_mul_capOp q a (by omega), ← mul_assoc]

/-- The translated vertex. -/
theorem sh_Vop (q : kˣ) (a b c f : ℕ) : sh a (Vop q b c f : Module.End k (ModelSpace k)) =
    (jwAt q a b * jwAt q (b + a) c) * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) := by
  unfold Vop Qab
  rw [sh_mul, sh_mul, sh_mul, sh_jwAt, sh_jwAt, sh_nestCup, sh_jwAt]
  simp only [zero_add]

/-- The translated dual vertex. -/
theorem sh_Wop (q : kˣ) (a b c f : ℕ) : sh a (Wop q b c f : Module.End k (ModelSpace k)) =
    jwAt q a (b + c - 2 * f) * nestCap q (b - f + a) f * (jwAt q a b * jwAt q (b + a) c) := by
  unfold Wop Qab
  rw [sh_mul, sh_mul, sh_mul, sh_jwAt, sh_jwAt, sh_nestCap, sh_jwAt]
  simp only [zero_add]

/-- The tree idempotent of the second bracketing: first fuse `(b,c)` into `f`, then `(a,f)` into `d`. -/
noncomputable def treeR (q : kˣ) (a b c f d : ℕ) : Module.End k (ModelSpace k) :=
  (kapRec q b c f)⁻¹ • (sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * sh a (Wop q b c f))

/-- **The second bracketing decomposes `p_a Q(b,c)` into the tree idempotents.** -/
theorem jwAt_mul_Qab_trees [CharZero k] (q : kˣ) (a b c : ℕ)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    jwAt q 0 a * sh a (Qab q b c) = ∑ f : Fin (min b c + 1), ∑ d : Fin (min a (b + c - 2 * f) + 1),
      treeR q a b c f d := by
  have hfi := fusion_identity (k := k) q b c (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
  rw [hfi, sh_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hfb : (f : ℕ) ≤ b := (Nat.lt_succ_iff.mp f.2).trans (min_le_left _ _)
  have hfc : (f : ℕ) ≤ c := (Nat.lt_succ_iff.mp f.2).trans (min_le_right _ _)
  have hQ := fusion_identity (k := k) q a (b + c - 2 * f) (fun j hj => hd j (by omega))
    (fun j h1 h2 => hq2 j h1 (by omega))
  have hshE : sh a (Eop q b c f : Module.End k (ModelSpace k)) =
      (kapRec q b c f)⁻¹ • (sh a (Vop q b c f) * sh a (Wop q b c f)) := by
    unfold Eop; rw [sh_smul, sh_mul]
  have hsum : ∑ d : Fin (min a (b + c - 2 * f) + 1), treeR q a b c f d =
      (kapRec q b c f)⁻¹ • (sh a (Vop q b c f) * Qab q a (b + c - 2 * f) * sh a (Wop q b c f)) := by
    unfold treeR
    rw [← Finset.smul_sum]
    congr 1
    rw [hQ, Finset.mul_sum, Finset.sum_mul]
  rw [hshE, hsum, mul_smul_comm]
  congr 1
  set J : Module.End k (ModelSpace k) := jwAt q a (b + c - 2 * f) with hJ
  have hJJ : J * J = J := jwAt_shift_idem q (c := b + c - 2 * f) (N := a + b + c + 1) (by omega)
    (fun j hj => hd j (by omega))
  have hV : sh a (Vop q b c f) * J = sh a (Vop q b c f) := by
    rw [sh_Vop, mul_assoc, hJJ]
  have hW : J * sh a (Wop q b c f) = sh a (Wop q b c f) := by
    rw [sh_Wop]
    calc J * (J * nestCap q (b - f + a) f * (jwAt q a b * jwAt q (b + a) c))
        = (J * J) * nestCap q (b - f + a) f * (jwAt q a b * jwAt q (b + a) c) := by simp only [mul_assoc]
      _ = _ := by rw [hJJ]
  have hcomm : (jwAt q 0 a : Module.End k (ModelSpace k)) * sh a (Vop q b c f) =
      sh a (Vop q b c f) * jwAt q 0 a := by
    rw [sh_Vop]
    have c1 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q a b = jwAt q a b * jwAt q 0 a :=
      jwAt_comm_jwAt q le_rfl b
    have c2 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (b + a) c = jwAt q (b + a) c * jwAt q 0 a :=
      jwAt_comm_jwAt q (by omega) c
    have c3 := jwAt_mul_nestCup (k := k) q (a := a) (l := b - f + a) (by omega) f
    have c4 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q a (b + c - 2 * f) =
        jwAt q a (b + c - 2 * f) * jwAt q 0 a := jwAt_comm_jwAt q le_rfl _
    exact (((Commute.mul_right (show Commute _ _ from c1) (show Commute _ _ from c2)).mul_right
      (show Commute _ _ from c3)).mul_right (show Commute _ _ from c4))
  calc (jwAt q 0 a : Module.End k (ModelSpace k)) * (sh a (Vop q b c f) * sh a (Wop q b c f))
      = sh a (Vop q b c f) * jwAt q 0 a * sh a (Wop q b c f) := by rw [← mul_assoc, hcomm]
    _ = sh a (Vop q b c f) * jwAt q 0 a * (J * sh a (Wop q b c f)) := by rw [hW]
    _ = sh a (Vop q b c f) * (jwAt q 0 a * J) * sh a (Wop q b c f) := by simp only [mul_assoc]
    _ = _ := by unfold Qab; rfl

/-- `Q(A,c)` absorbs the projector on the strands of the second block. -/
theorem Qab_mul_jwAt_shift (q : kˣ) (A c : ℕ) (hd : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0) :
    (Qab q A c : Module.End k (ModelSpace k)) * jwAt q A c = Qab q A c := by
  have := jwAt_shift_idem (k := k) q (s := A) (c := c) (N := A + c + 1) (by omega) (fun j hj => hd j (by omega))
  unfold Qab; rw [mul_assoc, this]

/-- `jwAt A c` absorbs into `Q(A,c)` on the left. -/
theorem jwAt_shift_mul_Qab (q : kˣ) (A c : ℕ) (hd : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0) :
    (jwAt q A c : Module.End k (ModelSpace k)) * Qab q A c = Qab q A c := by
  have h1 := jwAt_shift_idem (k := k) q (s := A) (c := c) (N := A + c + 1) (by omega) (fun j hj => hd j (by omega))
  unfold Qab
  rw [← mul_assoc, ← jwAt_comm_jwAt q le_rfl c, mul_assoc, h1]

/-- `E_d(A,c)` absorbs the projector on the second block, on both sides. -/
theorem Eop_mul_jwAt_shift (q : kˣ) (A c d : ℕ) (hd : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0) :
    (Eop q A c d : Module.End k (ModelSpace k)) * jwAt q A c = Eop q A c d := by
  have h1 := Eop_mul_Qab q A c hd d
  calc (Eop q A c d : Module.End k (ModelSpace k)) * jwAt q A c
      = (Eop q A c d * Qab q A c) * jwAt q A c := by rw [h1]
    _ = Eop q A c d * (Qab q A c * jwAt q A c) := by rw [mul_assoc]
    _ = Eop q A c d := by rw [Qab_mul_jwAt_shift q A c hd, h1]

/-- `jwAt A c` is absorbed by `E_d(A,c)` on the left. -/
theorem jwAt_shift_mul_Eop (q : kˣ) (A c d : ℕ) (hd : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0) :
    (jwAt q A c : Module.End k (ModelSpace k)) * Eop q A c d = Eop q A c d := by
  have h1 := Qab_mul_Eop q A c hd d
  calc (jwAt q A c : Module.End k (ModelSpace k)) * Eop q A c d
      = jwAt q A c * (Qab q A c * Eop q A c d) := by rw [h1]
    _ = (jwAt q A c * Qab q A c) * Eop q A c d := by rw [mul_assoc]
    _ = Eop q A c d := by rw [jwAt_shift_mul_Qab q A c hd, h1]

/-- **The tree idempotents of the second bracketing are orthogonal idempotents.** -/
theorem treeR_mul [CharZero k] (q : kˣ) (a b c : ℕ)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    {f d f' d' : ℕ} (hf : f ≤ min b c) (hf' : f' ≤ min b c) (hdd : d ≤ min a (b + c - 2 * f))
    (hdd' : d' ≤ min a (b + c - 2 * f')) :
    treeR q a b c f d * treeR q a b c f' d' =
      if f = f' ∧ d = d' then treeR q a b c f d else 0 := by
  have hfb : f ≤ b := hf.trans (min_le_left _ _)
  have hfc : f ≤ c := hf.trans (min_le_right _ _)
  have hfb' : f' ≤ b := hf'.trans (min_le_left _ _)
  have hfc' : f' ≤ c := hf'.trans (min_le_right _ _)
  unfold treeR
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  by_cases hff : f = f'
  · subst hff
    have hκ := kapRec_ne (k := k) q f b c hfb hfc (fun j h1 h2 => hq2 j h1 (by omega))
    have hWV := Wop_mul_Vop q b c f hfb hfc (fun j hj => hd j (by omega))
    have hWV' : sh a (Wop q b c f : Module.End k (ModelSpace k)) * sh a (Vop q b c f) =
        kapRec q b c f • jwAt q a (b + c - 2 * f) := by
      rw [← sh_mul, hWV, sh_smul, sh_jwAt]; simp
    have hdc : ∀ j, j ≤ a + (b + c - 2 * f) → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
    have hEE : Eop q a (b + c - 2 * f) d * Eop q a (b + c - 2 * f) d' =
        if d = d' then Eop q a (b + c - 2 * f) d else 0 := by
      by_cases hdeq : d = d'
      · subst hdeq
        rw [if_pos rfl]
        exact Eop_idem q a _ hdc (hdd.trans (min_le_left _ _)) (hdd.trans (min_le_right _ _))
          (fun j h1 h2 => hq2 j h1 (by omega))
      · rw [if_neg hdeq]
        have hm : 1 ≤ min a (b + c - 2 * f) := by omega
        exact Eop_orth q a _ hdc (by omega) (by omega) (hdd.trans (min_le_left _ _))
          (hdd.trans (min_le_right _ _)) (hdd'.trans (min_le_left _ _)) (hdd'.trans (min_le_right _ _)) hdeq
          (fun j h1 h2 => hq2 j h1 (by omega))
    have hp1 := Eop_mul_jwAt_shift (k := k) q a (b + c - 2 * f) d hdc
    have key : sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * sh a (Wop q b c f) *
        (sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d' * sh a (Wop q b c f)) =
        kapRec q b c f • (sh a (Vop q b c f) * (Eop q a (b + c - 2 * f) d * Eop q a (b + c - 2 * f) d') *
          sh a (Wop q b c f)) := by
      calc _ = sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * (sh a (Wop q b c f) * sh a (Vop q b c f)) *
            Eop q a (b + c - 2 * f) d' * sh a (Wop q b c f) := by simp only [mul_assoc]
        _ = sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * (kapRec q b c f • jwAt q a (b + c - 2 * f)) *
            Eop q a (b + c - 2 * f) d' * sh a (Wop q b c f) := by rw [hWV']
        _ = _ := by
            rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
            simp only [mul_assoc]
            rw [← mul_assoc (Eop q a (b + c - 2 * f) d) (jwAt q a (b + c - 2 * f)), hp1]
    rw [key, hEE, smul_smul]
    by_cases hdeq : d = d'
    · subst hdeq
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      rw [mul_assoc, inv_mul_cancel₀ hκ, mul_one]
    · rw [if_neg hdeq, if_neg (fun h => hdeq h.2)]
      simp
  · rw [if_neg (fun h => hff h.1)]
    have hm : 1 ≤ min b c := by omega
    have h0 := channel_orth q b c f f' (by omega) (by omega) hfb hfc hfb' hfc' (fun j hj => hd j (by omega))
      (lamRec_ne q b c f f' hfb hfc hfb' hfc' hff (fun j h1 h2 => hq2 j h1 (by omega)))
    have h0' : sh a (Wop q b c f : Module.End k (ModelSpace k)) * sh a (Vop q b c f') = 0 := by
      rw [← sh_mul, h0, sh_zero]
    have : sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * sh a (Wop q b c f) *
        (sh a (Vop q b c f') * Eop q a (b + c - 2 * f') d' * sh a (Wop q b c f')) = 0 := by
      calc _ = sh a (Vop q b c f) * Eop q a (b + c - 2 * f) d * (sh a (Wop q b c f) * sh a (Vop q b c f')) *
            Eop q a (b + c - 2 * f') d' * sh a (Wop q b c f') := by simp only [mul_assoc]
        _ = 0 := by rw [h0']; simp
    rw [this, smul_zero]

end Lightlike.TemperleyLieb
