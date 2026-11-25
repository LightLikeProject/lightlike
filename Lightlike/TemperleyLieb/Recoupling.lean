import Mathlib
import Lightlike.TemperleyLieb.Shift

/-!
# Recoupling: the two decompositions of the projector on three blocks

`P₃ = Q(a,b) p_c` is the sum of the first-bracketing tree idempotents `treeL e d` and also of the second-bracketing
ones `treeR f d'`.  Every `treeL e d` is one-dimensional inside `C (N-1)`, so the scalars `treeL · treeR · treeL`
are well defined: these are the recoupling coefficients, and their row sums are `1`.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The projector on three blocks. -/
noncomputable def P3 (q : kˣ) (a b c : ℕ) : Module.End k (ModelSpace k) := Qab q a b * jwAt q (a + b) c

/-- `Q(a,b)` commutes with a projector on the strands beyond `a + b`. -/
theorem Qab_comm_jwAt (q : kˣ) (a b c : ℕ) :
    (Qab q a b : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * Qab q a b := by
  have h1 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * jwAt q 0 a :=
    jwAt_comm_jwAt q (by omega) c
  have h2 := congrArg (sh a) (jwAt_comm_jwAt (k := k) q (A := b) (s := b) le_rfl c)
  rw [sh_mul, sh_mul, sh_jwAt, sh_jwAt] at h2
  simp only [zero_add] at h2
  rw [add_comm b a] at h2
  unfold Qab
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

/-- `treeL · P₃ = treeL`. -/
theorem treeL_mul_P3 (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    treeL q a b c e d * P3 q a b c = treeL q a b c e d := by
  have hdAc : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQ := Qab_idem (k := k) q a b (fun j hj => hd j (by omega))
  have hnc := nestCap_mul_jwAt (k := k) q (l := a - e) (s := a + b - 2 * e) (by omega) c e
  rw [show a + b - 2 * e + 2 * e = a + b by omega] at hnc
  have hEJ := Eop_mul_jwAt_shift (k := k) q (a + b - 2 * e) c d hdAc
  unfold treeL P3
  rw [smul_mul_assoc]
  congr 1
  calc Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e * Qab q a b *
        (Qab q a b * jwAt q (a + b) c)
      = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        ((Qab q a b * Qab q a b) * jwAt q (a + b) c) := by simp only [mul_assoc]
    _ = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        (jwAt q (a + b) c * Qab q a b) := by rw [hQ, Qab_comm_jwAt]
    _ = Qab q a b * nestCup q (a - e) e * (Eop q (a + b - 2 * e) c d * jwAt q (a + b - 2 * e) c) *
        nestCap q (a - e) e * Qab q a b := by
          simp only [← mul_assoc]; rw [mul_assoc _ (nestCap q (a - e) e), hnc]; simp only [mul_assoc]
    _ = _ := by rw [hEJ]

/-- `p_c ≠ 0`. -/
theorem jwAt_ne_zero (q : kˣ) (c : ℕ) : (jwAt q 0 c : Module.End k (ModelSpace k)) ≠ 0 := by
  intro h
  have := jwAt_dicke (k := k) q c 0
  rw [h] at this
  exact dicke_ne_zero (k := k) q (Nat.zero_le c) this.symm

/-- **The first-bracketing tree idempotents are non-zero.** -/
theorem treeL_ne_zero (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c)
    (hdA : d ≤ a + b - 2 * e)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    treeL q a b c e d ≠ 0 := by
  set A := a + b - 2 * e with hA
  have hdAc : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hκ1 := kapRec_ne (k := k) q e a b hea heb (fun j h1 h2 => hq2 j h1 (by omega))
  have hκ2 := kapRec_ne (k := k) q d A c hdA hdc (fun j h1 h2 => hq2 j h1 (by omega))
  have hW1 := Wop_mul_Vop q a b e hea heb (fun j hj => hd j (by omega))
  have hW2 := Wop_mul_Vop q A c d hdA hdc hdAc
  have hpA := jwAt_mul_Qab' (k := k) q A c hdAc
  -- `W_d W_e V_e V_d = κ_e κ_d p_D`
  have hmid : Wop q A c d * (Wop q a b e * Vop q a b e) * Vop q A c d =
      (kapRec q a b e * kapRec q A c d) • jwAt q 0 (A + c - 2 * d) := by
    rw [hW1, mul_smul_comm, smul_mul_assoc]
    have : jwAt q 0 A * Vop q A c d = Vop q A c d := by
      unfold Vop; rw [← mul_assoc, ← mul_assoc, hpA]
    rw [mul_assoc, this, hW2, smul_smul]
  intro h0
  have hT : treeL q a b c e d = ((kapRec q a b e)⁻¹ * (kapRec q A c d)⁻¹) •
      (Vop q a b e * Vop q A c d * Wop q A c d * Wop q a b e) := by
    rw [treeL_eq q a b c e d hdAc]
    unfold Eop
    rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    simp only [mul_assoc, hA]
  rw [hT] at h0
  have h1 : Vop q a b e * Vop q A c d * Wop q A c d * Wop q a b e = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero (inv_ne_zero hκ1) (inv_ne_zero hκ2))
    · exact h
  have hm : (Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d) =
      (kapRec q a b e * kapRec q A c d) • jwAt q 0 (A + c - 2 * d) := by
    rw [← hmid]; simp only [mul_assoc]
  have h1' : (Vop q a b e * Vop q A c d) * (Wop q A c d * Wop q a b e) = 0 := by
    rw [← h1]; simp only [mul_assoc]
  have h2 : ((Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d)) *
      ((Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d)) = 0 := by
    calc _ = (Wop q A c d * Wop q a b e) * ((Vop q a b e * Vop q A c d) * (Wop q A c d * Wop q a b e)) *
          (Vop q a b e * Vop q A c d) := by simp only [mul_assoc]
      _ = 0 := by rw [h1']; simp
  rw [hm, smul_mul_assoc, mul_smul_comm, smul_smul] at h2
  have hpp : jwAt q 0 (A + c - 2 * d) * jwAt q 0 (A + c - 2 * d) = (jwAt q 0 (A + c - 2 * d) : Module.End k (ModelSpace k)) :=
    jwAt_idem (k := k) q (N := A + c + 1) (by omega) (fun j hj => hdAc j (by omega))
  rw [hpp] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hκ1 hκ2) (mul_ne_zero hκ1 hκ2))
  · exact jwAt_ne_zero q _ h

/-- The two bracketings give the same projector. -/
theorem jwAt_mul_sh_Qab (q : kˣ) (a b c : ℕ) :
    (jwAt q 0 a : Module.End k (ModelSpace k)) * sh a (Qab q b c) = P3 q a b c := by
  unfold Qab P3
  rw [sh_mul, sh_jwAt, sh_jwAt, zero_add, add_comm b a, Qab, mul_assoc]

/-- The recoupling coefficient: the scalar by which `treeL e d · treeR f d' · treeL e d` multiplies `treeL e d`. -/
noncomputable def recoup (q : kˣ) (a b c e d f d' : ℕ) : k :=
  if h : ∃ μ : k, treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = μ • treeL q a b c e d
  then h.choose else 0

/-- The scalar is unique when the tree idempotent is non-zero. -/
theorem smul_left_cancel_of_ne_zero {T : Module.End k (ModelSpace k)} (hT : T ≠ 0) {μ ν : k}
    (h : μ • T = ν • T) : μ = ν := by
  by_contra hne
  have : (μ - ν) • T = 0 := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun S : Module.End k (ModelSpace k) => S v) h
    simp only [LinearMap.smul_apply] at this ⊢
    rw [sub_smul, this, sub_self]; rfl
  rcases smul_eq_zero.mp this with h1 | h1
  · exact hne (sub_eq_zero.mp h1)
  · exact hT h1

/-- Specification of the recoupling coefficient (first colour `a ≥ 1`, last colour `c ≥ 1`). -/
theorem recoup_spec [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (ha : 1 ≤ a)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = recoup q a b c e d f d' • treeL q a b c e d := by
  have hY := treeR_mem (k := k) q hδ (a := a) (b := b) (c := c) (f := f) (d := d') hd hfb hfc hda hdf (by omega)
  obtain ⟨μ, hμ⟩ := treeL_sandwich q a b c e d (by omega) hd hea heb hdc hdA hY
  have hex : ∃ μ : k, treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = μ • treeL q a b c e d := ⟨μ, hμ⟩
  unfold recoup
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **Row sums of the recoupling matrix are `1`.** -/
theorem recoup_row_sum [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d : ℕ) (ha : 1 ≤ a)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e) :
    ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), recoup q a b c e d f d' = 1 := by
  have hT0 := treeL_ne_zero (k := k) q a b c e d hea heb hdc hdA hd hq2
  have hidem := treeL_mul (k := k) q a b c hd hq2 (e := e) (d := d) (e' := e) (d' := d)
    (le_min hea heb) (le_min hea heb) (le_min hdA hdc |>.trans_eq (by rw [min_comm])) (le_min hdA hdc |>.trans_eq (by rw [min_comm]))
  rw [if_pos ⟨rfl, rfl⟩] at hidem
  have hsum : ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), treeR q a b c f d' = P3 q a b c := by
    rw [← jwAt_mul_Qab_trees q a b c hd hq2, jwAt_mul_sh_Qab]
  have hL := treeL_mul_P3 (k := k) q a b c e d hea heb hd
  have key : treeL q a b c e d * P3 q a b c * treeL q a b c e d = treeL q a b c e d := by
    rw [hL, hidem]
  have hexp : treeL q a b c e d * P3 q a b c * treeL q a b c e d =
      (∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), recoup q a b c e d f d') •
        treeL q a b c e d := by
    rw [← hsum, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d' _ => ?_
    have hfb : (f : ℕ) ≤ b := (Nat.lt_succ_iff.mp f.2).trans (min_le_left _ _)
    have hfc : (f : ℕ) ≤ c := (Nat.lt_succ_iff.mp f.2).trans (min_le_right _ _)
    exact recoup_spec q hδ a b c e d f d' ha hd hea heb hdc hdA hfb hfc
      ((Nat.lt_succ_iff.mp d'.2).trans (min_le_left _ _)) ((Nat.lt_succ_iff.mp d'.2).trans (min_le_right _ _))
  rw [hexp] at key
  have := smul_left_cancel_of_ne_zero hT0 (μ := ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1),
    recoup q a b c e d f d') (ν := 1) (by rw [key, one_smul])
  exact this

/-- **The two-level sandwich of the second bracketing is a scalar.** -/
theorem Wop_Wop_sandwich_R (q : kˣ) (a b c f d : ℕ) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d ≤ a) (hdf : d ≤ b + c - 2 * f)
    {Y : Module.End k (ModelSpace k)} (hY : Y ∈ CSub q (a + b + c - 1)) :
    ∃ ε : k, Wop q a (b + c - 2 * f) d * (sh a (Wop q b c f) * Y * sh a (Vop q b c f)) *
      Vop q a (b + c - 2 * f) d = ε • jwAt q 0 (a + (b + c - 2 * f) - 2 * d) := by
  set C := b + c - 2 * f with hC
  have hdAc : ∀ j, j ≤ a + C → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQmem : (jwAt q a b * jwAt q (b + a) c : Module.End k (ModelSpace k)) ∈ CSub q (a + b + c - 1) := by
    have h1 : jwAt q a b ∈ CSub q (a + b + c - 1) :=
      tlSub_mono (m := a + b - 1) (n := a + b + c - 1) (by omega) (jwAt_mem q a b)
    have h2 : jwAt q (b + a) c ∈ CSub q (a + b + c - 1) :=
      tlSub_mono (m := b + a + c - 1) (n := a + b + c - 1) (by omega) (jwAt_mem q (b + a) c)
    exact Subalgebra.mul_mem _ h1 h2
  have hZ0 : (jwAt q a b * jwAt q (b + a) c) * Y * (jwAt q a b * jwAt q (b + a) c) ∈ CSub q (a + b + c - 1) :=
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hQmem hY) hQmem
  have hX1 := nestCap_mul_nestCup_mem q (b - f + a) f (a + b + c - 1) hZ0 (by omega)
  rw [show a + b + c - 1 - 2 * f = a + C - 1 by omega] at hX1
  set X1 := nestCap q (b - f + a) f * ((jwAt q a b * jwAt q (b + a) c) * Y * (jwAt q a b * jwAt q (b + a) c)) *
    nestCup q (b - f + a) f with hX1def
  have hW1 : sh a (Wop q b c f) * Y * sh a (Vop q b c f) = jwAt q a C * X1 * jwAt q a C := by
    rw [sh_Wop, sh_Vop]; rw [hX1def]; simp only [mul_assoc, hC]
  have hQ'mem : Qab q a C ∈ CSub q (a + C - 1) := Qab_mem q a C
  have hJ1 := Qab_mul_jwAt_shift (k := k) q a C hdAc
  have hJ2 := jwAt_shift_mul_Qab (k := k) q a C hdAc
  have hX2 : Qab q a C * X1 * Qab q a C ∈ CSub q (a + C - 1) :=
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hQ'mem hX1) hQ'mem
  have hX3 := nestCap_mul_nestCup_mem q (a - d) d (a + C - 1) hX2 (by omega)
  rw [show a + C - 1 - 2 * d = (a + C - 2 * d) - 1 by omega] at hX3
  have hDd : ∀ j, j < a + C - 2 * d → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  obtain ⟨ε, hε⟩ := jwAt_sandwich q hDd hX3
  refine ⟨ε, ?_⟩
  rw [hW1]
  unfold Wop Vop
  calc jwAt q 0 (a + C - 2 * d) * nestCap q (a - d) d * Qab q a C * (jwAt q a C * X1 * jwAt q a C) *
        (Qab q a C * nestCup q (a - d) d * jwAt q 0 (a + C - 2 * d))
      = jwAt q 0 (a + C - 2 * d) * (nestCap q (a - d) d * ((Qab q a C * jwAt q a C) * X1 *
        (jwAt q a C * Qab q a C)) * nestCup q (a - d) d) * jwAt q 0 (a + C - 2 * d) := by simp only [mul_assoc]
    _ = jwAt q 0 (a + C - 2 * d) * (nestCap q (a - d) d * (Qab q a C * X1 * Qab q a C) * nestCup q (a - d) d) *
        jwAt q 0 (a + C - 2 * d) := by rw [hJ1, hJ2]
    _ = ε • jwAt q 0 (a + C - 2 * d) := hε

/-- **One-dimensionality of the second-bracketing tree corner.** -/
theorem treeR_sandwich (q : kˣ) (a b c f d : ℕ) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d ≤ a) (hdf : d ≤ b + c - 2 * f)
    {Y : Module.End k (ModelSpace k)} (hY : Y ∈ CSub q (a + b + c - 1)) :
    ∃ μ : k, treeR q a b c f d * Y * treeR q a b c f d = μ • treeR q a b c f d := by
  obtain ⟨ε, hε⟩ := Wop_Wop_sandwich_R q a b c f d hN hd hfb hfc hda hdf hY
  set C := b + c - 2 * f with hC
  have hdAc : ∀ j, j ≤ a + C → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hV2 := Vop_mul_jwAt (k := k) q a C hdAc hda hdf
  have hT : treeR q a b c f d = ((kapRec q b c f)⁻¹ * (kapRec q a C d)⁻¹) •
      (sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f)) := by
    unfold treeR Eop
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, hC]
  rw [hT]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  refine ⟨ε * ((kapRec q b c f)⁻¹ * (kapRec q a C d)⁻¹), ?_⟩
  have key : (sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f)) * Y *
      (sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f)) =
      ε • (sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f)) := by
    calc _ = sh a (Vop q b c f) * Vop q a C d * (Wop q a C d * (sh a (Wop q b c f) * Y * sh a (Vop q b c f)) *
          Vop q a C d) * Wop q a C d * sh a (Wop q b c f) := by simp only [mul_assoc]
      _ = sh a (Vop q b c f) * Vop q a C d * (ε • jwAt q 0 (a + C - 2 * d)) * Wop q a C d *
          sh a (Wop q b c f) := by rw [hε]
      _ = _ := by
          rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
          congr 1
          rw [mul_assoc (sh a (Vop q b c f)), hV2]
  rw [key, smul_smul]
  congr 1
  ring

/-- `treeL` preserves the window `a + b + c`. -/
theorem treeL_maps (q : kˣ) {a b c e d : ℕ} (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    ∀ v ∈ Win k (a + b + c), (treeL q a b c e d : Module.End k (ModelSpace k)) v ∈ Win k (a + b + c) := by
  intro v hv
  rw [treeL_eq q a b c e d (fun j hj => hd j (by omega))]
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have h1 := Wop_maps_gen q (a := a) (b := b) (i := e) (M := a + b + c) hea heb (by omega) v hv
  rw [show a + b + c - 2 * e = (a + b - 2 * e) + c by omega] at h1
  have h2 := Eop_maps (k := k) q (a := a + b - 2 * e) (b := c) (i := d) hdA hdc _ h1
  have h3 := Vop_maps_gen q (a := a) (b := b) (i := e) (M := a + b + c) hea heb (by omega) _
    (by rw [show a + b + c - 2 * e = (a + b - 2 * e) + c by omega]; exact h2)
  simpa [Module.End.mul_apply] using h3

/-- **The rank of the first-bracketing tree idempotent** is `D + 1`, `D = a + b - 2e + c - 2d`. -/
theorem finrank_range_treeL [CharZero k] (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c)
    (hdA : d ≤ a + b - 2 * e)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Module.finrank k (LinearMap.range (resW (N := a + b + c) (treeL q a b c e d : Module.End k (ModelSpace k))
      (treeL_maps q hea heb hdc hdA hd))) = a + b - 2 * e + c - 2 * d + 1 := by
  set A := a + b - 2 * e with hA
  have hdAc : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hκ := kapRec_ne (k := k) q e a b hea heb (fun j h1 h2 => hq2 j h1 (by omega))
  have hNA : a + b + c - 2 * e = A + c := by omega
  have hVmap : ∀ x ∈ Win k (A + c), (Vop q a b e : Module.End k (ModelSpace k)) x ∈ Win k (a + b + c) := fun x hx =>
    Vop_maps_gen q (a := a) (b := b) (i := e) (M := a + b + c) hea heb (by omega) x (by rw [hNA]; exact hx)
  have hWmap : ∀ x ∈ Win k (a + b + c), (Wop q a b e : Module.End k (ModelSpace k)) x ∈ Win k (A + c) := fun x hx => by
    have := Wop_maps_gen q (a := a) (b := b) (i := e) (M := a + b + c) hea heb (by omega) x hx
    rwa [hNA] at this
  let Vw : Win k (A + c) →ₗ[k] Win k (a + b + c) := LinearMap.restrict (Vop q a b e) hVmap
  let Ww : Win k (a + b + c) →ₗ[k] Win k (A + c) := LinearMap.restrict (Wop q a b e) hWmap
  let Ew : Module.End k (Win k (A + c)) := resW (N := A + c) (Eop q A c d : Module.End k (ModelSpace k))
    (Eop_maps q hdA hdc)
  let Pp : Module.End k (Win k (A + c)) := resW (N := A + c) (jwAt q 0 A : Module.End k (ModelSpace k))
    (fun v hv => jwAt_preserves q (s := 0) (n := A) (N := A + c) (by omega) v hv)
  have hWV : Ww ∘ₗ Vw = (kapRec q a b e) • Pp := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k)) (Wop_mul_Vop q a b e hea heb
      (fun j hj => hd j (by omega)))
    simpa [Vw, Ww, Pp, resW_apply] using this
  have hEP : Ew ∘ₗ Pp = Ew := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k))
      (Eop_mul_jwAt (k := k) q A c hdAc d)
    simpa [Ew, Pp, resW_apply] using this
  have hE : IsIdempotentElem Ew := by
    show Ew * Ew = Ew
    simp only [Ew]
    rw [resW_mul]
    exact resW_congr (Eop_idem q A c hdAc hdA hdc (fun j h1 h2 => hq2 j h1 (by omega))) _ _
  have hTeq : (kapRec q a b e)⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww) =
      resW (N := a + b + c) (treeL q a b c e d : Module.End k (ModelSpace k)) (treeL_maps q hea heb hdc hdA hd) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [resW_apply, treeL_eq q a b c e d hdAc]
    simp [Vw, Ww, Ew, resW_apply, hA]
  have hPE : Pp ∘ₗ Ew = Ew := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k))
      (jwAt_mul_Eop (k := k) q A c hdAc d)
    simpa [Ew, Pp, resW_apply] using this
  have h1 := finrank_conj (K := k) (P := Win k (A + c)) (Q := Win k (a + b + c)) Vw Ww Ew Pp (kapRec q a b e) hκ hWV hEP hPE hE
  rw [hTeq] at h1
  rw [h1]
  have h2 := finrank_range_Eop_eq (k := k) q A c hdAc (fun j h1 h2 => hq2 j h1 (by omega))
    ⟨d, by have := le_min hdA hdc; omega⟩
  simpa using h2

/-- The translated vertex maps the window `a + C` into the window `a + b + c`. -/
theorem shV_maps (q : kˣ) {a b c f : ℕ} (hfb : f ≤ b) (hfc : f ≤ c) :
    ∀ v ∈ Win k (a + (b + c - 2 * f)), sh a (Vop q b c f : Module.End k (ModelSpace k)) v ∈ Win k (a + b + c) := by
  intro v hv
  rw [sh_Vop]
  simp only [Module.End.mul_apply]
  have h0 := jwAt_preserves q (s := a) (n := b + c - 2 * f) (N := a + (b + c - 2 * f)) le_rfl v hv
  have h1 := nestCup_preserves q (l := b - f + a) (c := a + (b + c - 2 * f)) (by omega) f _ h0
  rw [show a + (b + c - 2 * f) + 2 * f = a + b + c by omega] at h1
  exact jwAt_preserves q (s := a) (n := b) (N := a + b + c) (by omega) _
    (jwAt_preserves q (s := b + a) (n := c) (N := a + b + c) (by omega) _ h1)

/-- The translated dual vertex maps the window `a + b + c` into the window `a + C`. -/
theorem shW_maps (q : kˣ) {a b c f : ℕ} (hfb : f ≤ b) (hfc : f ≤ c) :
    ∀ v ∈ Win k (a + b + c), sh a (Wop q b c f : Module.End k (ModelSpace k)) v ∈ Win k (a + (b + c - 2 * f)) := by
  intro v hv
  rw [sh_Wop]
  simp only [Module.End.mul_apply]
  have h0 := jwAt_preserves q (s := a) (n := b) (N := a + b + c) (by omega) _
    (jwAt_preserves q (s := b + a) (n := c) (N := a + b + c) (by omega) v hv)
  have h1 := nestCap_preserves q (l := b - f + a) f (a + b + c) (by omega) _ h0
  rw [show a + b + c - 2 * f = a + (b + c - 2 * f) by omega] at h1
  exact jwAt_preserves q (s := a) (n := b + c - 2 * f) (N := a + (b + c - 2 * f)) le_rfl _ h1

/-- `treeR` preserves the window `a + b + c`. -/
theorem treeR_maps (q : kˣ) {a b c f d : ℕ} (hfb : f ≤ b) (hfc : f ≤ c) (hda : d ≤ a) (hdf : d ≤ b + c - 2 * f) :
    ∀ v ∈ Win k (a + b + c), (treeR q a b c f d : Module.End k (ModelSpace k)) v ∈ Win k (a + b + c) := by
  intro v hv
  unfold treeR
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have h1 := shW_maps q hfb hfc v hv
  have h2 := Eop_maps (k := k) q (a := a) (b := b + c - 2 * f) (i := d) hda hdf _ h1
  have h3 := shV_maps q hfb hfc _ h2
  simpa [Module.End.mul_apply] using h3

/-- **The rank of the second-bracketing tree idempotent** is `D + 1`, `D = a + (b + c - 2f) - 2d`. -/
theorem finrank_range_treeR [CharZero k] (q : kˣ) (a b c f d : ℕ) (hfb : f ≤ b) (hfc : f ≤ c) (hda : d ≤ a)
    (hdf : d ≤ b + c - 2 * f)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Module.finrank k (LinearMap.range (resW (N := a + b + c) (treeR q a b c f d : Module.End k (ModelSpace k))
      (treeR_maps q hfb hfc hda hdf))) = a + (b + c - 2 * f) - 2 * d + 1 := by
  set C := b + c - 2 * f with hC
  have hdAc : ∀ j, j ≤ a + C → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hκ := kapRec_ne (k := k) q f b c hfb hfc (fun j h1 h2 => hq2 j h1 (by omega))
  let Vw : Win k (a + C) →ₗ[k] Win k (a + b + c) := LinearMap.restrict (sh a (Vop q b c f)) (shV_maps q hfb hfc)
  let Ww : Win k (a + b + c) →ₗ[k] Win k (a + C) := LinearMap.restrict (sh a (Wop q b c f)) (shW_maps q hfb hfc)
  let Ew : Module.End k (Win k (a + C)) := resW (N := a + C) (Eop q a C d : Module.End k (ModelSpace k))
    (Eop_maps q hda hdf)
  let Pp : Module.End k (Win k (a + C)) := resW (N := a + C) (jwAt q a C : Module.End k (ModelSpace k))
    (fun v hv => jwAt_preserves q (s := a) (n := C) (N := a + C) le_rfl v hv)
  have hWV : Ww ∘ₗ Vw = (kapRec q b c f) • Pp := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k))
      (congrArg (sh a) (Wop_mul_Vop q b c f hfb hfc (fun j hj => hd j (by omega))))
    simp only [sh_mul, sh_smul, sh_jwAt, zero_add, Module.End.mul_apply, LinearMap.smul_apply] at this
    simpa [Vw, Ww, Pp, resW_apply, hC] using this
  have hEP : Ew ∘ₗ Pp = Ew := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k))
      (Eop_mul_jwAt_shift (k := k) q a C d hdAc)
    simpa [Ew, Pp, resW_apply] using this
  have hPE : Pp ∘ₗ Ew = Ew := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (x : ModelSpace k))
      (jwAt_shift_mul_Eop (k := k) q a C d hdAc)
    simpa [Ew, Pp, resW_apply] using this
  have hE : IsIdempotentElem Ew := by
    show Ew * Ew = Ew
    simp only [Ew]
    rw [resW_mul]
    exact resW_congr (Eop_idem q a C hdAc hda hdf (fun j h1 h2 => hq2 j h1 (by omega))) _ _
  have hTeq : (kapRec q b c f)⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww) =
      resW (N := a + b + c) (treeR q a b c f d : Module.End k (ModelSpace k)) (treeR_maps q hfb hfc hda hdf) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [resW_apply]
    unfold treeR
    simp [Vw, Ww, Ew, resW_apply, hC]
  have h1 := finrank_conj (K := k) (P := Win k (a + C)) (Q := Win k (a + b + c)) Vw Ww Ew Pp (kapRec q b c f) hκ
    hWV hEP hPE hE
  rw [hTeq] at h1
  rw [h1]
  have h2 := finrank_range_Eop_eq (k := k) q a C hdAc (fun j h1 h2 => hq2 j h1 (by omega))
    ⟨d, by have := le_min hda hdf; omega⟩
  simpa using h2

/-- **Overlapping idempotents have comparable ranks**: if `x y x = λ x` with `λ ≠ 0` then `rank x ≤ rank y`. -/
theorem finrank_le_of_overlap {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {x y : Module.End k W} (hx : IsIdempotentElem x) {μ : k} (hμ : μ ≠ 0) (h : x * y * x = μ • x) :
    Module.finrank k (LinearMap.range x) ≤ Module.finrank k (LinearMap.range y) := by
  let f : LinearMap.range x →ₗ[k] LinearMap.range y :=
    { toFun := fun v => ⟨y v, LinearMap.mem_range_self y v⟩
      map_add' := fun v w => by apply Subtype.ext; simp
      map_smul' := fun r v => by apply Subtype.ext; simp }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun v hv => ?_
    obtain ⟨u, hu⟩ := v.2
    have hyv : y (v : W) = 0 := congrArg Subtype.val hv
    have h1 := congrArg (fun T : Module.End k W => T u) h
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hu, hyv, map_zero] at h1
    have h2 : μ • (v : W) = 0 := h1.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hμ
    · exact Subtype.ext h3
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **The recoupling coefficient vanishes unless the total channels agree.** -/
theorem recoup_eq_zero_of_ne [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hD : a + b - 2 * e + c - 2 * d ≠ a + (b + c - 2 * f) - 2 * d') :
    recoup q a b c e d f d' = 0 := by
  by_contra hlam
  have hL0 := treeL_ne_zero (k := k) q a b c e d hea heb hdc hdA hd hq2
  have hspec := recoup_spec (k := k) q hδ a b c e d f d' ha hd hea heb hdc hdA hfb hfc hda hdf
  have hLmem := treeL_mem (k := k) q hδ (a := a) (b := b) (c := c) (e := e) (d := d) hea heb hdc hdA (by omega)
  obtain ⟨μ', hμ'⟩ := treeR_sandwich q a b c f d' (by omega) hd hfb hfc hda hdf hLmem
  -- `μ' = recoup`
  have hmul : μ' = recoup q a b c e d f d' := by
    have e1 : treeL q a b c e d * (treeR q a b c f d' * treeL q a b c e d * treeR q a b c f d') *
        treeL q a b c e d = (μ' * recoup q a b c e d f d') • treeL q a b c e d := by
      rw [hμ', mul_smul_comm, smul_mul_assoc, hspec, smul_smul]
    have e2 : treeL q a b c e d * (treeR q a b c f d' * treeL q a b c e d * treeR q a b c f d') *
        treeL q a b c e d = (recoup q a b c e d f d' * recoup q a b c e d f d') • treeL q a b c e d := by
      calc _ = (treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d) * treeR q a b c f d' *
            treeL q a b c e d := by simp only [mul_assoc]
        _ = _ := by rw [hspec, smul_mul_assoc, smul_mul_assoc, hspec, smul_smul]
    rw [e1] at e2
    have := smul_left_cancel_of_ne_zero hL0 e2
    exact mul_right_cancel₀ hlam this
  -- ranks on the window
  have hxm := treeL_maps (k := k) q hea heb hdc hdA hd
  have hym := treeR_maps (k := k) q (a := a) (b := b) (c := c) hfb hfc hda hdf
  set x := resW (N := a + b + c) (treeL q a b c e d : Module.End k (ModelSpace k)) hxm with hx
  set y := resW (N := a + b + c) (treeR q a b c f d' : Module.End k (ModelSpace k)) hym with hy
  have hxx : IsIdempotentElem x := by
    show x * x = x
    rw [hx, resW_mul]
    have := treeL_mul (k := k) q a b c hd hq2 (e := e) (d := d) (e' := e) (d' := d)
      (le_min hea heb) (le_min hea heb) (le_min hdA hdc |>.trans_eq (by rw [min_comm]))
      (le_min hdA hdc |>.trans_eq (by rw [min_comm]))
    rw [if_pos ⟨rfl, rfl⟩] at this
    exact resW_congr this _ _
  have hyy : IsIdempotentElem y := by
    show y * y = y
    rw [hy, resW_mul]
    have := treeR_mul (k := k) q a b c hd hq2 (f := f) (d := d') (f' := f) (d' := d')
      (le_min hfb hfc) (le_min hfb hfc) (le_min hda hdf) (le_min hda hdf)
    rw [if_pos ⟨rfl, rfl⟩] at this
    exact resW_congr this _ _
  have hxyx : x * y * x = recoup q a b c e d f d' • x := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (v : ModelSpace k)) hspec
    simpa [hx, hy, resW_apply] using this
  have hyxy : y * x * y = recoup q a b c e d f d' • y := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have := congrArg (fun T : Module.End k (ModelSpace k) => T (v : ModelSpace k)) hμ'
    rw [hmul] at this
    simpa [hx, hy, resW_apply] using this
  have r1 := finrank_le_of_overlap (W := Win k (a + b + c)) (x := x) (y := y) hxx hlam hxyx
  have r2 := finrank_le_of_overlap (W := Win k (a + b + c)) (x := y) (y := x) hyy hlam hyxy
  rw [hx, hy] at r1 r2
  rw [finrank_range_treeL q a b c e d hea heb hdc hdA hd hq2, finrank_range_treeR q a b c f d' hfb hfc hda hdf hd hq2] at r1 r2
  omega

/-- `treeR` as a sandwich of the translated three-block projector. -/
theorem treeR_eq (q : kˣ) (a b c f d : ℕ) (hfb : f ≤ b) (hfc : f ≤ c)
    (hdc : ∀ j, j ≤ a + (b + c - 2 * f) → chebD (loopVal q) j ≠ 0) :
    treeR q a b c f d = (kapRec q b c f)⁻¹ • ((jwAt q a b * jwAt q (b + a) c) *
      (nestCup q (b - f + a) f * Eop q a (b + c - 2 * f) d * nestCap q (b - f + a) f) *
      (jwAt q a b * jwAt q (b + a) c)) := by
  unfold treeR
  congr 1
  have hJE := jwAt_shift_mul_Eop (k := k) q a (b + c - 2 * f) d hdc
  have hEJ := Eop_mul_jwAt_shift (k := k) q a (b + c - 2 * f) d hdc
  have hJEJ : (jwAt q a (b + c - 2 * f) : Module.End k (ModelSpace k)) * Eop q a (b + c - 2 * f) d *
      jwAt q a (b + c - 2 * f) = Eop q a (b + c - 2 * f) d := by rw [hJE, hEJ]
  rw [sh_Vop, sh_Wop]
  calc _ = (jwAt q a b * jwAt q (b + a) c) * nestCup q (b - f + a) f * (jwAt q a (b + c - 2 * f) *
        Eop q a (b + c - 2 * f) d * jwAt q a (b + c - 2 * f)) * nestCap q (b - f + a) f *
        (jwAt q a b * jwAt q (b + a) c) := by simp only [mul_assoc]
    _ = _ := by rw [hJEJ]; simp only [mul_assoc]

/-- `treeR · P₃ = treeR`. -/
theorem treeR_mul_P3 (q : kˣ) (a b c f d : ℕ) (hfb : f ≤ b) (hfc : f ≤ c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    treeR q a b c f d * P3 q a b c = treeR q a b c f d := by
  have hdc : ∀ j, j ≤ a + (b + c - 2 * f) → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hsh := congrArg (sh a) (Qab_idem (k := k) q b c (fun j hj => hd j (by omega)))
  rw [sh_mul] at hsh
  have hQs : sh a (Qab q b c : Module.End k (ModelSpace k)) = jwAt q a b * jwAt q (b + a) c := by
    unfold Qab; rw [sh_mul, sh_jwAt, sh_jwAt]; simp
  rw [hQs] at hsh
  have hp : (jwAt q 0 a : Module.End k (ModelSpace k)) * (jwAt q a b * jwAt q (b + a) c) =
      (jwAt q a b * jwAt q (b + a) c) * jwAt q 0 a := by
    rw [← mul_assoc, jwAt_comm_jwAt q le_rfl b, mul_assoc, jwAt_comm_jwAt q (by omega) c, mul_assoc]
  have hP3 : P3 q a b c = jwAt q 0 a * (jwAt q a b * jwAt q (b + a) c) := by
    rw [← jwAt_mul_sh_Qab, hQs]
  have hEp := Eop_mul_jwAt (k := k) q a (b + c - 2 * f) hdc d
  have hnp := jwAt_mul_nestCap (k := k) q (a := a) (l := b - f + a) (by omega) f
  rw [treeR_eq q a b c f d hfb hfc hdc, smul_mul_assoc, hP3]
  congr 1
  set Qs : Module.End k (ModelSpace k) := jwAt q a b * jwAt q (b + a) c with hQsdef
  have hQp : Qs * (jwAt q 0 a * Qs) = jwAt q 0 a * Qs := by
    rw [← mul_assoc, ← hp, mul_assoc, hsh]
  have hEn : Eop q a (b + c - 2 * f) d * (nestCap q (b - f + a) f * jwAt q 0 a) =
      Eop q a (b + c - 2 * f) d * nestCap q (b - f + a) f := by
    rw [← hnp, ← mul_assoc, hEp]
  calc Qs * (nestCup q (b - f + a) f * Eop q a (b + c - 2 * f) d * nestCap q (b - f + a) f) * Qs *
        (jwAt q 0 a * Qs)
      = Qs * (nestCup q (b - f + a) f * Eop q a (b + c - 2 * f) d * nestCap q (b - f + a) f) *
        (Qs * (jwAt q 0 a * Qs)) := by simp only [mul_assoc]
    _ = Qs * (nestCup q (b - f + a) f * (Eop q a (b + c - 2 * f) d * (nestCap q (b - f + a) f * jwAt q 0 a))) * Qs := by
          rw [hQp]; simp only [mul_assoc]
    _ = _ := by rw [hEn]; simp only [mul_assoc]

/-- **The second-bracketing tree idempotents are non-zero.** -/
theorem treeR_ne_zero (q : kˣ) (a b c f d : ℕ) (hfb : f ≤ b) (hfc : f ≤ c) (hda : d ≤ a)
    (hdf : d ≤ b + c - 2 * f)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    treeR q a b c f d ≠ 0 := by
  set C := b + c - 2 * f with hC
  have hdAc : ∀ j, j ≤ a + C → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hκ1 := kapRec_ne (k := k) q f b c hfb hfc (fun j h1 h2 => hq2 j h1 (by omega))
  have hκ2 := kapRec_ne (k := k) q d a C hda hdf (fun j h1 h2 => hq2 j h1 (by omega))
  have hW1 := Wop_mul_Vop q b c f hfb hfc (fun j hj => hd j (by omega))
  have hW2 := Wop_mul_Vop q a C d hda hdf hdAc
  have hW1' : sh a (Wop q b c f : Module.End k (ModelSpace k)) * sh a (Vop q b c f) =
      kapRec q b c f • jwAt q a C := by
    rw [← sh_mul, hW1, sh_smul, sh_jwAt]; simp [hC]
  have hJV : jwAt q a C * Vop q a C d = Vop q a C d := by
    have := jwAt_shift_mul_Qab (k := k) q a C hdAc
    unfold Vop; rw [← mul_assoc, ← mul_assoc, this]
  have hmid : Wop q a C d * (sh a (Wop q b c f) * sh a (Vop q b c f)) * Vop q a C d =
      (kapRec q b c f * kapRec q a C d) • jwAt q 0 (a + C - 2 * d) := by
    rw [hW1', mul_smul_comm, smul_mul_assoc, mul_assoc, hJV, hW2, smul_smul]
  intro h0
  have hT : treeR q a b c f d = ((kapRec q b c f)⁻¹ * (kapRec q a C d)⁻¹) •
      (sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f)) := by
    unfold treeR Eop
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, hC]
  rw [hT] at h0
  have h1 : sh a (Vop q b c f) * Vop q a C d * Wop q a C d * sh a (Wop q b c f) = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero (inv_ne_zero hκ1) (inv_ne_zero hκ2))
    · exact h
  have hm : (Wop q a C d * sh a (Wop q b c f)) * (sh a (Vop q b c f) * Vop q a C d) =
      (kapRec q b c f * kapRec q a C d) • jwAt q 0 (a + C - 2 * d) := by
    rw [← hmid]; simp only [mul_assoc]
  have h1' : (sh a (Vop q b c f) * Vop q a C d) * (Wop q a C d * sh a (Wop q b c f)) = 0 := by
    rw [← h1]; simp only [mul_assoc]
  have h2 : ((Wop q a C d * sh a (Wop q b c f)) * (sh a (Vop q b c f) * Vop q a C d)) *
      ((Wop q a C d * sh a (Wop q b c f)) * (sh a (Vop q b c f) * Vop q a C d)) = 0 := by
    calc _ = (Wop q a C d * sh a (Wop q b c f)) * ((sh a (Vop q b c f) * Vop q a C d) *
          (Wop q a C d * sh a (Wop q b c f))) * (sh a (Vop q b c f) * Vop q a C d) := by simp only [mul_assoc]
      _ = 0 := by rw [h1']; simp
  rw [hm, smul_mul_assoc, mul_smul_comm, smul_smul] at h2
  have hpp : jwAt q 0 (a + C - 2 * d) * jwAt q 0 (a + C - 2 * d) =
      (jwAt q 0 (a + C - 2 * d) : Module.End k (ModelSpace k)) :=
    jwAt_idem (k := k) q (N := a + C + 1) (by omega) (fun j hj => hdAc j (by omega))
  rw [hpp] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hκ1 hκ2) (mul_ne_zero hκ1 hκ2))
  · exact jwAt_ne_zero q _ h

end Lightlike.TemperleyLieb
