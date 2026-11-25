import Mathlib
import Lightlike.TemperleyLieb.Recoupling

/-!
# Balanced cap and cup words reduce to the Temperley–Lieb subalgebra

`nestCap l i · Z · nestCup l' i ∈ C (N - 2 i)` for `Z ∈ C N`, with two different junctions `l`, `l'`, and a version
with leftover caps or cups that meet other elements of `C`.  This is the reduction needed for the Gram pairing of the
two tree bases.
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- Splitting a stack of caps. -/
lemma nestCap_add (q : kˣ) (l i j : ℕ) :
    (nestCap q l (i + j) : Module.End k (ModelSpace k)) = nestCap q l i * nestCap q (l + i) j := by
  induction j with
  | zero => simp [nestCap]
  | succ j ih =>
    have e1 : (nestCap q l (i + (j + 1)) : Module.End k (ModelSpace k)) = nestCap q l (i + j) * capOp q (l + (i + j)) := rfl
    have e2 : (nestCap q (l + i) (j + 1) : Module.End k (ModelSpace k)) = nestCap q (l + i) j * capOp q (l + i + j) := rfl
    rw [e1, e2, ih, mul_assoc, show l + (i + j) = l + i + j by ring]

/-- Splitting a stack of cups. -/
lemma nestCup_add (q : kˣ) (l i j : ℕ) :
    (nestCup q l (i + j) : Module.End k (ModelSpace k)) = nestCup q (l + i) j * nestCup q l i := by
  induction j with
  | zero => simp [nestCup]
  | succ j ih =>
    have e1 : (nestCup q l (i + (j + 1)) : Module.End k (ModelSpace k)) = cupOp q (l + (i + j)) * nestCup q l (i + j) := rfl
    have e2 : (nestCup q (l + i) (j + 1) : Module.End k (ModelSpace k)) = cupOp q (l + i + j) * nestCup q (l + i) j := rfl
    rw [e1, e2, ih, ← mul_assoc, show l + (i + j) = l + i + j by ring]

/-- **Balanced nested caps and cups at two junctions reduce.** -/
theorem nestCap_mul_nestCup_mem_gen (q : kˣ) (l l' : ℕ) :
    ∀ (i N : ℕ) {Z : Module.End k (ModelSpace k)}, Z ∈ CSub q N → l + 2 * i ≤ N + 1 → l' + 2 * i ≤ N + 1 →
      nestCap q l i * Z * nestCup q l' i ∈ CSub q (N - 2 * i) := by
  intro i
  induction i with
  | zero => intro N Z hZ _ _; simpa [nestCap, nestCup] using hZ
  | succ i ih =>
    intro N Z hZ hl hl'
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h1 : nestCap q l (i + 1) * Z * nestCup q l' (i + 1) =
        nestCap q l i * (capOp q (l + i) * Z * cupOp q (l' + i)) * nestCup q l' i := by
      simp only [nestCap, nestCup, mul_assoc]
    rw [h1]
    have h2 := cap_mul_cup_mem q hZ (l + i) (l' + i) (by omega) (by omega)
    have h3 := ih (n - 1) h2 (by omega) (by omega)
    have e : n + 1 - 2 * (i + 1) = n - 1 - 2 * i := by omega
    rw [e]; exact h3

/-- **Three layers, case `e ≤ f`.** `caps_{d'+t} · Y_L · caps_e · Z · cups_{t+e} · Y_R · cups_{d'}` lies in
`C (N - 2e - 2t - 2d')` for `Z ∈ C N`, `Y_L ∈ C (N - 2e)`, `Y_R ∈ C (N - 2e - 2t)`. -/
theorem balanced_le (q : kˣ) {N : ℕ} {Z YL YR : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q N)
    (e t d' lam l l' l'' : ℕ) (hYL : YL ∈ CSub q (N - 2 * e)) (hYR : YR ∈ CSub q (N - 2 * e - 2 * t))
    (h1 : l + 2 * e ≤ N + 1) (h1' : l' + t + 2 * e ≤ N + 1)
    (h2 : lam + d' + 2 * t ≤ N - 2 * e + 1) (h2' : l' + 2 * t ≤ N - 2 * e + 1)
    (h3 : lam + 2 * d' ≤ N - 2 * e - 2 * t + 1) (h3' : l'' + 2 * d' ≤ N - 2 * e - 2 * t + 1) :
    nestCap q lam (d' + t) * YL * nestCap q l e * Z * nestCup q l' (t + e) * YR * nestCup q l'' d' ∈
      CSub q (N - 2 * e - 2 * t - 2 * d') := by
  have hZ1 := nestCap_mul_nestCup_mem_gen q l (l' + t) e N hZ h1 h1'
  have hY1 : YL * (nestCap q l e * Z * nestCup q (l' + t) e) ∈ CSub q (N - 2 * e) := Subalgebra.mul_mem _ hYL hZ1
  have hZ2 := nestCap_mul_nestCup_mem_gen q (lam + d') l' t (N - 2 * e) hY1 h2 h2'
  have hZ3 : nestCap q (lam + d') t * (YL * (nestCap q l e * Z * nestCup q (l' + t) e)) * nestCup q l' t * YR ∈
      CSub q (N - 2 * e - 2 * t) := Subalgebra.mul_mem _ hZ2 hYR
  have hZ4 := nestCap_mul_nestCup_mem_gen q lam l'' d' (N - 2 * e - 2 * t) hZ3 h3 h3'
  have e1 : nestCap q lam (d' + t) * YL * nestCap q l e * Z * nestCup q l' (t + e) * YR * nestCup q l'' d' =
      nestCap q lam d' * ((nestCap q (lam + d') t * (YL * (nestCap q l e * Z * nestCup q (l' + t) e)) *
        nestCup q l' t * YR)) * nestCup q l'' d' := by
    rw [nestCap_add, nestCup_add]
    simp only [mul_assoc]
  rw [e1]
  have e2 : N - 2 * e - 2 * t - 2 * d' = N - 2 * e - 2 * t - 2 * d' := rfl
  exact hZ4

/-- **Three layers, case `f ≤ e`.** `caps_d · Y_L · caps_{t+f} · Z · cups_f · Y_R · cups_{d+t}` lies in
`C (N - 2f - 2t - 2d)` for `Z ∈ C N`, `Y_R ∈ C (N - 2f)`, `Y_L ∈ C (N - 2f - 2t)`. -/
theorem balanced_ge (q : kˣ) {N : ℕ} {Z YL YR : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q N)
    (f t d lam l l' l'' : ℕ) (hYR : YR ∈ CSub q (N - 2 * f)) (hYL : YL ∈ CSub q (N - 2 * f - 2 * t))
    (h1 : l + t + 2 * f ≤ N + 1) (h1' : l' + 2 * f ≤ N + 1)
    (h2 : l + 2 * t ≤ N - 2 * f + 1) (h2' : l'' + d + 2 * t ≤ N - 2 * f + 1)
    (h3 : lam + 2 * d ≤ N - 2 * f - 2 * t + 1) (h3' : l'' + 2 * d ≤ N - 2 * f - 2 * t + 1) :
    nestCap q lam d * YL * nestCap q l (t + f) * Z * nestCup q l' f * YR * nestCup q l'' (d + t) ∈
      CSub q (N - 2 * f - 2 * t - 2 * d) := by
  have hZ1 := nestCap_mul_nestCup_mem_gen q (l + t) l' f N hZ h1 h1'
  have hZ1' : (nestCap q (l + t) f * Z * nestCup q l' f) * YR ∈ CSub q (N - 2 * f) := Subalgebra.mul_mem _ hZ1 hYR
  have hZ2 := nestCap_mul_nestCup_mem_gen q l (l'' + d) t (N - 2 * f) hZ1' h2 h2'
  have hZ3 : YL * (nestCap q l t * ((nestCap q (l + t) f * Z * nestCup q l' f) * YR) * nestCup q (l'' + d) t) ∈
      CSub q (N - 2 * f - 2 * t) := Subalgebra.mul_mem _ hYL hZ2
  have hZ4 := nestCap_mul_nestCup_mem_gen q lam l'' d (N - 2 * f - 2 * t) hZ3 h3 h3'
  have e1 : nestCap q lam d * YL * nestCap q l (t + f) * Z * nestCup q l' f * YR * nestCup q l'' (d + t) =
      nestCap q lam d * (YL * (nestCap q l t * ((nestCap q (l + t) f * Z * nestCup q l' f) * YR) *
        nestCup q (l'' + d) t)) * nestCup q l'' d := by
    rw [nestCap_add, nestCup_add]
    simp only [mul_assoc]
  rw [e1]
  exact hZ4

/-- The middle factor of the Gram pairing (as a product of caps, cups and elements of `C`). -/
noncomputable def gramMid (q : kˣ) (a b c e d f d' : ℕ) : Module.End k (ModelSpace k) :=
  nestCap q (a + b - 2 * e - d) d * (Qab q (a + b - 2 * e) c * jwAt q 0 (a + b - 2 * e)) *
    nestCap q (a - e) e * (Qab q a b * (jwAt q a b * jwAt q (b + a) c)) *
    nestCup q (b - f + a) f * (jwAt q a (b + c - 2 * f) * Qab q a (b + c - 2 * f)) * nestCup q (a - d') d'

/-- **The Gram pairing as a product with the projectors**: `W_d W_e · sh V_f V_{d'} = p_D · gramMid · p_{D'}`. -/
theorem gram_eq (q : kˣ) (a b c e d f d' : ℕ) :
    (Wop q (a + b - 2 * e) c d * Wop q a b e) * (sh a (Vop q b c f) * Vop q a (b + c - 2 * f) d') =
      jwAt q 0 (a + b - 2 * e + c - 2 * d) * gramMid q a b c e d f d' *
        jwAt q 0 (a + (b + c - 2 * f) - 2 * d') := by
  rw [sh_Vop]
  unfold gramMid Wop Vop
  simp only [mul_assoc]

/-- The factors lie in the expected subalgebras. -/
theorem gramMid_mem (q : kˣ) (a b c e d f d' : ℕ) (hN : 1 ≤ a + b + c)
    (hea : e ≤ a) (heb : e ≤ b) (hfb : f ≤ b) (hfc : f ≤ c) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hD : a + b - 2 * e + c - 2 * d = a + (b + c - 2 * f) - 2 * d') :
    gramMid q a b c e d f d' ∈ CSub q (a + b - 2 * e + c - 2 * d - 1) := by
  set N := a + b + c with hNdef
  have hZ : Qab q a b * (jwAt q a b * jwAt q (b + a) c) ∈ CSub q (N - 1) := by
    have h1 : Qab q a b ∈ CSub q (N - 1) := tlSub_mono (m := a + b - 1) (n := N - 1) (by omega) (Qab_mem q a b)
    have h2 : jwAt q a b ∈ CSub q (N - 1) := tlSub_mono (m := a + b - 1) (n := N - 1) (by omega) (jwAt_mem q a b)
    have h3 : jwAt q (b + a) c ∈ CSub q (N - 1) :=
      tlSub_mono (m := b + a + c - 1) (n := N - 1) (by omega) (jwAt_mem q (b + a) c)
    exact Subalgebra.mul_mem _ h1 (Subalgebra.mul_mem _ h2 h3)
  have hYL : Qab q (a + b - 2 * e) c * jwAt q 0 (a + b - 2 * e) ∈ CSub q (N - 1 - 2 * e) := by
    have h1 : Qab q (a + b - 2 * e) c ∈ CSub q (N - 1 - 2 * e) :=
      tlSub_mono (m := a + b - 2 * e + c - 1) (n := N - 1 - 2 * e) (by omega) (Qab_mem q _ c)
    have h2 : jwAt q 0 (a + b - 2 * e) ∈ CSub q (N - 1 - 2 * e) := by
      have := jwAt_mem (k := k) q 0 (a + b - 2 * e)
      exact tlSub_mono (by omega) this
    exact Subalgebra.mul_mem _ h1 h2
  have hYR : jwAt q a (b + c - 2 * f) * Qab q a (b + c - 2 * f) ∈ CSub q (N - 1 - 2 * f) := by
    have h1 : jwAt q a (b + c - 2 * f) ∈ CSub q (N - 1 - 2 * f) :=
      tlSub_mono (m := a + (b + c - 2 * f) - 1) (n := N - 1 - 2 * f) (by omega) (jwAt_mem q a _)
    have h2 : Qab q a (b + c - 2 * f) ∈ CSub q (N - 1 - 2 * f) :=
      tlSub_mono (m := a + (b + c - 2 * f) - 1) (n := N - 1 - 2 * f) (by omega) (Qab_mem q a _)
    exact Subalgebra.mul_mem _ h1 h2
  rcases le_total e f with hef | hef
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hef
    obtain rfl : d = d' + t := by omega
    have hYR2 : jwAt q a (b + c - 2 * (t + e)) * Qab q a (b + c - 2 * (t + e)) ∈ CSub q (N - 1 - 2 * e - 2 * t) := by
      have := hYR
      rw [show e + t = t + e from add_comm e t] at this
      rwa [show N - 1 - 2 * (t + e) = N - 1 - 2 * e - 2 * t by omega] at this
    have key := balanced_le q (N := N - 1) hZ e t d' (a + b - 2 * e - (d' + t)) (a - e) (b - (t + e) + a) (a - d')
      (YL := Qab q (a + b - 2 * e) c * jwAt q 0 (a + b - 2 * e))
      (YR := jwAt q a (b + c - 2 * (t + e)) * Qab q a (b + c - 2 * (t + e)))
      hYL hYR2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    unfold gramMid
    rw [show e + t = t + e from add_comm e t]
    have hidx : a + b - 2 * e + c - 2 * (d' + t) - 1 = N - 1 - 2 * e - 2 * t - 2 * d' := by omega
    rw [hidx]
    exact key
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hef
    obtain rfl : d' = d + t := by omega
    have hYL2 : Qab q (a + b - 2 * (t + f)) c * jwAt q 0 (a + b - 2 * (t + f)) ∈ CSub q (N - 1 - 2 * f - 2 * t) := by
      have := hYL
      rw [show f + t = t + f from add_comm f t] at this
      rwa [show N - 1 - 2 * (t + f) = N - 1 - 2 * f - 2 * t by omega] at this
    have key := balanced_ge q (N := N - 1) hZ f t d (a + b - 2 * (t + f) - d) (a - (t + f)) (b - f + a) (a - (d + t))
      (YL := Qab q (a + b - 2 * (t + f)) c * jwAt q 0 (a + b - 2 * (t + f)))
      (YR := jwAt q a (b + c - 2 * f) * Qab q a (b + c - 2 * f))
      hYR hYL2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    unfold gramMid
    rw [show f + t = t + f from add_comm f t]
    have hidx : a + b - 2 * (t + f) + c - 2 * d - 1 = N - 1 - 2 * f - 2 * t - 2 * d := by omega
    rw [hidx]
    exact key

end Lightlike.TemperleyLieb
