import Lightlike.TuraevViro.Reflect.SixJNormOne
import Lightlike.TuraevViro.Reflect.AdmRange

/-!
# Orthogonality of the q-6j symbol from the boundary evaluation

For colours `B, A, E, F, q` with `q` admissible (`qAdm B F q`, `qAdm E A q`), the sum
`Σ_x [x+1] {B A x; E F q}² = 1 / [q+1]` follows from the boundary evaluation `QDougall`. The colours
`0` and `r - 2` need no special treatment, because the endpoint rows of the recurrence are proved
(`row_at`).
-/

set_option maxHeartbeats 400000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- The boundary evaluation for the data `B, A, E, F`, as a statement about the lowest colours. -/
def QDougallAt (r B A E F : ℕ) : Prop :=
  QDougall r B A E F (aLo B A E F) ((aHi r B A E F - aLo B A E F) / 2) (aLo B F E A)

/-- Restricting the sum over the third colour to a progression that covers the admissible ones. -/
lemma sum_reindex {r : ℕ} (hr : 2 ≤ r) (B A E F q xL n : ℕ)
    (hadm : ∀ k ≤ n, qAdm r B A (xL + 2 * k) ∧ qAdm r E F (xL + 2 * k))
    (hcov : ∀ x, qAdm r B A x ∧ qAdm r E F x → ∃ k ≤ n, x = xL + 2 * k) :
    ∑ x ∈ range (r - 1), qnum r (x + 1) * qSixJ r B A x E F q ^ 2 =
      ∑ k ∈ range (n + 1), qnum r (xL + 2 * k + 1) * qSixJ r B A (xL + 2 * k) E F q ^ 2 := by
  have hinj : Set.InjOn (fun k => xL + 2 * k) (range (n + 1) : Set ℕ) := fun a _ b _ h => by
    simp only at h; omega
  rw [← Finset.sum_image (f := fun x => qnum r (x + 1) * qSixJ r B A x E F q ^ 2) hinj]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have := (hadm k (by simpa [Nat.lt_succ_iff] using hk)).1
    unfold qAdm Lightlike.Pentagon.Tri at this
    simp only [Finset.mem_range]; omega
  · intro x _ hx
    by_contra hne
    have h0 : qSixJ r B A x E F q ≠ 0 := by
      intro h; exact hne (by rw [h]; simp)
    obtain ⟨h1, -, -, h4⟩ := qSixJ_ok h0
    obtain ⟨k, hk, rfl⟩ := hcov x ⟨h1, h4⟩
    exact hx (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩)

/-- One term of the sum, in the variables of the recurrence. -/
lemma term_eq {r : ℕ} (B A E F q x : ℕ) (h1 : qAdm r B A x) (h2 : qAdm r B F q)
    (h3 : qAdm r E A q) (h4 : qAdm r E F x) :
    qnum r (x + 1) * qSixJ r B A x E F q ^ 2 =
      jOmega r B A E F x * Sj r B A E F q (x : ℤ) ^ 2 * (qDelta r B F q ^ 2 * qDelta r E A q ^ 2) := by
  have : qSixJ r B A x E F q =
      qDelta r B A x * qDelta r B F q * qDelta r E A q * qDelta r E F x *
        Sj r B A E F q (x : ℤ) := by
    unfold qSixJ
    simp only [h1, h2, h3, h4, and_self, ite_true]
    rw [qRacahSum_eq_Sj]
  rw [this]; unfold jOmega; ring

/-- An admissible colour is below `r - 1`. -/
lemma qAdm_lt {r a b c : ℕ} (hr : 2 ≤ r) (h : qAdm r a b c) : c + 1 < r := by
  obtain ⟨⟨-, t2, -, -⟩, t5⟩ := h
  omega

/-- Orthogonality of the q-6j symbol in the model form, from the boundary evaluation `QDougallAt`. -/
theorem orth_interior {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hD : QDougallAt r B A E F) :
    ∑ x ∈ range (r - 1), qnum r (x + 1) * qSixJ r B A x E F q ^ 2 = 1 / qnum r (q + 1) := by
  have hqf := hq1; have hqe := hq2
  unfold qAdm Lightlike.Pentagon.Tri at hq1 hq2
  have hparX : (B + A + E + F) % 2 = 0 := by omega
  have hparQ : (B + F + E + A) % 2 = 0 := by omega
  have iffX := adm_pair_iff hr hparX
  have iffQ := adm_pair_iff hr hparQ
  obtain ⟨xLpar, xHpar, heqX, hloX0, hhiX0⟩ :=
    pair_facts (r := r) (a := B) (b := A) (c := E) (d := F) hparX (by omega) (by omega)
  obtain ⟨qLpar, qHpar, heqQ, hloQ0, hhiQ0⟩ :=
    pair_facts (r := r) (a := B) (b := F) (c := E) (d := A) hparQ (by omega) (by omega)
  have hxle : aLo B A E F ≤ aHi r B A E F := by
    have h1 := (aLo_spec B A E F).2.2.2.2
    have h2 := (aHi_spec r B A E F).2.2.2.2
    omega
  have hqle : aLo B F E A ≤ aHi r B F E A := by
    have h1 := (aLo_spec B F E A).2.2.2.2
    have h2 := (aHi_spec r B F E A).2.2.2.2
    omega
  obtain ⟨sL1, sL2, sL3, sL4, -⟩ := aLo_spec B A E F
  obtain ⟨tL1, tL2, tL3, tL4, -⟩ := aLo_spec B F E A
  obtain ⟨sH1, sH2, sH3, sH4, -⟩ := aHi_spec r B A E F
  obtain ⟨tH1, tH2, tH3, tH4, -⟩ := aHi_spec r B F E A
  unfold QDougallAt at hD
  generalize aLo B A E F = xL at *
  generalize aHi r B A E F = xH at *
  generalize aLo B F E A = qL at *
  generalize aHi r B F E A = qH at *
  revert heqX heqQ hhiX0 hhiQ0 hloX0 hloQ0
  have hadmX : ∀ k ≤ (xH - xL) / 2, qAdm r B A (xL + 2 * k) ∧ qAdm r E F (xL + 2 * k) := by
    intro k hk
    rw [iffX]
    omega
  have hadmQ : ∀ l ≤ (qH - qL) / 2, qAdm r B F (qL + 2 * l) ∧ qAdm r E A (qL + 2 * l) := by
    intro l hl
    rw [iffQ]
    omega
  have hxn : xL + 2 * ((xH - xL) / 2) = xH := by omega
  have hqn : qL + 2 * ((qH - qL) / 2) = qH := by omega
  intro d1 d2 d3 d4 d5 d6
  have key := sixj_norm_one hr B A E F xL ((xH - xL) / 2) qL ((qH - qL) / 2) hadmX
    (by assumption) (by rw [hxn]; push_cast; assumption) hadmQ (by assumption)
    (by rw [hqn]; push_cast; assumption) (by assumption) (by assumption) hD
  have hqmem := (iffQ q).1 ⟨hqf, hqe⟩
  have hcov : ∀ x, qAdm r B A x ∧ qAdm r E F x → ∃ k ≤ (xH - xL) / 2, x = xL + 2 * k := by
    intro x hx
    have := (iffX x).1 hx
    exact ⟨(x - xL) / 2, by omega, by omega⟩
  rw [sum_reindex hr B A E F q xL ((xH - xL) / 2) hadmX hcov]
  have hl := key.1 ((q - qL) / 2) (by omega)
  have hq' : qL + 2 * ((q - qL) / 2) = q := by omega
  rw [hq'] at hl
  have hterm : ∀ k ∈ range ((xH - xL) / 2 + 1),
      qnum r (xL + 2 * k + 1) * qSixJ r B A (xL + 2 * k) E F q ^ 2 =
        (qDelta r B F q ^ 2 * qDelta r E A q ^ 2) *
          (jOmega r B A E F (xL + 2 * k) * Sj r B A E F q ((xL + 2 * k : ℕ) : ℤ) ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have ha := hadmX k (by omega)
    rw [term_eq B A E F q _ ha.1 hqf hqe ha.2]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hpos : 0 < qnum r (q + 1) := qnum_pos hr (Nat.succ_pos q) (qAdm_lt hr hqf)
  have hω : jOmega r B F E A q = qnum r (q + 1) * (qDelta r B F q ^ 2 * qDelta r E A q ^ 2) := by
    unfold jOmega; ring
  rw [hω] at hl
  rw [eq_div_iff hpos.ne']
  linear_combination hl

end Lightlike.TV.Refl
