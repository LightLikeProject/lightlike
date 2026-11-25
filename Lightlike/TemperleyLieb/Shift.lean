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

lemma pre_tl (s : ℕ) (σ : ℕ → Bool) : pre s σ (tl s σ) = σ := by
  funext j; simp only [pre, tl]; split_ifs with h
  · rfl
  · congr 1; omega

lemma tl_pre (s : ℕ) (σ ρ : ℕ → Bool) : tl s (pre s σ ρ) = ρ := by
  funext j; simp [pre, tl]

lemma pre_pre (s : ℕ) (σ ρ τ : ℕ → Bool) : pre s (pre s σ ρ) τ = pre s σ τ := by
  funext j; simp only [pre]; split_ifs <;> rfl

lemma pre_pre' (s : ℕ) (σ ρ : ℕ → Bool) : pre s (pre s σ ρ) = pre s σ := funext (pre_pre s σ ρ)

/-- Translation by `s` strands, as a linear map on the operators. -/
noncomputable def sh (s : ℕ) (T : Module.End k (ModelSpace k)) : Module.End k (ModelSpace k) :=
  Finsupp.lsum k fun σ => LinearMap.toSpanSingleton k _
    (Finsupp.lmapDomain k k (pre s σ) (T (single (tl s σ) 1)))

lemma sh_single (s : ℕ) (T : Module.End k (ModelSpace k)) (σ : ℕ → Bool) (c : k) :
    sh s T (single σ c) = c • Finsupp.lmapDomain k k (pre s σ) (T (single (tl s σ) 1)) := by
  simp [sh]

lemma sh_lmapDomain (s : ℕ) (T : Module.End k (ModelSpace k)) (σ : ℕ → Bool) (w : ModelSpace k) :
    sh s T (Finsupp.lmapDomain k k (pre s σ) w) = Finsupp.lmapDomain k k (pre s σ) (T w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single ρ c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, sh_single, tl_pre]
    have : (single ρ c : ModelSpace k) = c • single ρ 1 := by simp
    rw [pre_pre', this, map_smul, map_smul]

lemma sh_mul (s : ℕ) (S T : Module.End k (ModelSpace k)) : sh s (S * T) = sh s S * sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [Module.End.mul_apply, sh_single, sh_single, map_smul, sh_lmapDomain, Module.End.mul_apply]

lemma sh_one (s : ℕ) : sh s (1 : Module.End k (ModelSpace k)) = 1 := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [sh_single, Module.End.one_apply]
  simp [pre_tl]

lemma pre_set2 (s j : ℕ) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre s σ (set2 ρ j x y) = set2 (pre s σ ρ) (j + s) x y := by
  funext n
  simp only [pre, set2, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

lemma pre_insertTwo (s m : ℕ) (σ ρ : ℕ → Bool) (x y : Bool) :
    pre s σ (insertTwo ρ m x y) = insertTwo (pre s σ ρ) (m + s) x y := by
  funext n
  simp only [pre, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

lemma pre_removeTwo (s m : ℕ) (σ ρ : ℕ → Bool) :
    pre s σ (removeTwo ρ m) = removeTwo (pre s σ ρ) (m + s) := by
  funext n
  simp only [pre, removeTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

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

lemma sh_add (s : ℕ) (S T : Module.End k (ModelSpace k)) : sh s (S + T) = sh s S + sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [LinearMap.add_apply, sh_single, sh_single, sh_single, LinearMap.add_apply, map_add, smul_add]

lemma sh_smul (s : ℕ) (r : k) (T : Module.End k (ModelSpace k)) : sh s (r • T) = r • sh s T := by
  apply Finsupp.lhom_ext
  intro σ c
  rw [LinearMap.smul_apply, sh_single, sh_single, LinearMap.smul_apply, map_smul, smul_comm]

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

end Lightlike.TemperleyLieb
