import Lightlike.TuraevViro.Reflect.RacahDc
import Lightlike.TuraevViro.Reflect.RacahTelescope

/-!
# The q-Racah recurrence for the real sums `SR`

`SR r a₁ … β₃` is the finite sum of `qRacahTerm` over `z = 0, …, β₁`. Telescoping the pointwise
recurrence at `u = e^{iπ/r}` gives a linear relation between the sums for the tuples
`(a₁+1, a₂, a₃, a₄+1, β₁, β₂+1, β₃+1)`, `(a₁, …, β₃)` and `(a₁-1, a₂, a₃, a₄-1, β₁, β₂-1, β₃-1)`.
All side conditions (bounds below `r - 1` that keep the local step relations valid, and the
nonvanishing of the quantum-integer denominators) are explicit hypotheses.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Real Finset Lightlike.TV

/-- The finite q-Racah sum over `z = 0, …, β₁`. -/
noncomputable def SR (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) : ℝ :=
  ∑ z ∈ range (b1.toNat + 1), qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z

/-- The recurrence coefficients at the root of unity. -/
noncomputable def rcR (r : ℕ) (a1 a2 a3 a4 b2 b3 : ℤ) (P : Poly) : ℂ :=
  recCoef P (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3)

lemma qRacahTerm_zero_of_lt {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ}
    (h : (z : ℤ) < a1 ∨ (z : ℤ) < a2 ∨ (z : ℤ) < a3 ∨ (z : ℤ) < a4) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold qRacahTerm
  rcases h with h | h | h | h
  · have : invQFact r (z - a1) = 0 := by simp only [invQFact, show ¬ (0 ≤ (z : ℤ) - a1) by omega, ↓reduceIte]
    simp [this]
  · have : invQFact r (z - a2) = 0 := by simp only [invQFact, show ¬ (0 ≤ (z : ℤ) - a2) by omega, ↓reduceIte]
    simp [this]
  · have : invQFact r (z - a3) = 0 := by simp only [invQFact, show ¬ (0 ≤ (z : ℤ) - a3) by omega, ↓reduceIte]
    simp [this]
  · have : invQFact r (z - a4) = 0 := by simp only [invQFact, show ¬ (0 ≤ (z : ℤ) - a4) by omega, ↓reduceIte]
    simp [this]

lemma FiC_neg {r : ℕ} {n : ℤ} (h : n < 0) : FiC r n = 0 := by
  simp only [FiC, invQFact, show ¬ (0 ≤ n) by omega, ↓reduceIte, Complex.ofReal_zero]

/-- The sum `SR` as a sum over `z = L, …, b₁` when the terms below `L` vanish. -/
lemma SR_eq {r : ℕ} (a1 a2 a3 a4 b1 b2 b3 : ℤ) (L : ℕ) (hb0 : 0 ≤ b1) (hL : (L : ℤ) ≤ b1 + 1)
    (hz : ∀ z : ℕ, z < L → qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0) :
    SR r a1 a2 a3 a4 b1 b2 b3 =
      ∑ k ∈ range (b1 + 1 - L).toNat, qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (L + k) := by
  unfold SR
  rw [show b1.toNat + 1 = L + (b1 + 1 - L).toNat by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (fun z hz' => hz z (Finset.mem_range.mp hz')), zero_add]

/-- **The telescoped q-Racah recurrence for the real sums** at `q = e^{iπ/r}`. -/
theorem real_recurrence {r : ℕ} (hr : 2 ≤ r) (a1 a2 a3 a4 b1 b2 b3 : ℤ)
    (hbal : b1 + b2 + b3 = a1 + a2 + a3 + a4) (L : ℕ) (hb0 : 0 ≤ b1) (hL : (L : ℤ) ≤ b1 + 1)
    (hA : (L : ℤ) + 1 = a1 ∨ (L : ℤ) + 1 = a2 ∨ (L : ℤ) + 1 = a3 ∨ (L : ℤ) + 1 = a4)
    (hb1 : b1 - a1 ≤ (r : ℤ) - 2) (hb2 : b1 - a2 ≤ (r : ℤ) - 2) (hb3 : b1 - a3 ≤ (r : ℤ) - 2)
    (hb4 : b1 - a4 ≤ (r : ℤ) - 2) (hb5 : b1 - L ≤ (r : ℤ) - 1)
    (hb6 : b2 - L ≤ (r : ℤ) - 2) (hb7 : b3 - L ≤ (r : ℤ) - 2)
    (hD : ∀ k : ℤ, 0 ≤ k → k ≤ 2 → ¬ (r : ℤ) ∣ b2 + b3 - a2 - a3 + k) :
    2 * (rcR r a1 a2 a3 a4 b2 b3 fNa / 2 /
          (rcR r a1 a2 a3 a4 b2 b3 fQ1 * rcR r a1 a2 a3 a4 b2 b3 fQ2))
        * (SR r (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) : ℂ)
      + 2 * (rcR r a1 a2 a3 a4 b2 b3 fbn /
          (2 * rcR r a1 a2 a3 a4 b2 b3 fQ0 * rcR r a1 a2 a3 a4 b2 b3 fQ2))
        * (SR r a1 a2 a3 a4 b1 b2 b3 : ℂ)
      + 2 * (rcR r a1 a2 a3 a4 b2 b3 fNc / 2 /
          (rcR r a1 a2 a3 a4 b2 b3 fQ0 * rcR r a1 a2 a3 a4 b2 b3 fQ1))
        * (SR r (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) : ℂ)
      - rcR r a1 a2 a3 a4 b2 b3 fCq * (SR r a1 a2 a3 a4 b1 b2 b3 : ℂ) = 0 := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have hd : uC r - (uC r)⁻¹ ≠ 0 := by
    have := bk_uC_ne hr (m := 1) (by
      intro h; have := Int.le_of_dvd one_pos h; omega)
    simpa [bk] using this
  obtain ⟨hQ0, hQ1, hQ2, hDc⟩ := nonvanishing_root hr a1 a2 a3 a4 b2 b3 hD
  have hn : ((L : ℤ) + ((b1 + 1 - L).toNat : ℕ)) = b1 + 1 := by omega
  -- vanishing of the terms below L
  have vz : ∀ (c1 c2 c3 c4 : ℤ) (d1 d2 d3 : ℤ), (L : ℤ) ≤ c1 ∨ (L : ℤ) ≤ c2 ∨ (L : ℤ) ≤ c3 ∨ (L : ℤ) ≤ c4 →
      ∀ z : ℕ, z < L → qRacahTerm r c1 c2 c3 c4 d1 d2 d3 z = 0 := by
    intro c1 c2 c3 c4 d1 d2 d3 h z hz
    apply qRacahTerm_zero_of_lt
    omega
  have e0 := SR_eq (r := r) a1 a2 a3 a4 b1 b2 b3 L hb0 hL (vz _ _ _ _ _ _ _ (by omega))
  have e1 := SR_eq (r := r) (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) L hb0 hL
    (vz _ _ _ _ _ _ _ (by omega))
  have e2 := SR_eq (r := r) (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) L hb0 hL
    (vz _ _ _ _ _ _ _ (by omega))
  have hG0 : Gq (Fi := FiC r) (Pn := PnC r) (uC r)
      (rhoC (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3))
      a1 a2 a3 a4 b1 b2 b3 L = 0 := by
    unfold Gq Gb
    rcases hA with h | h | h | h
    · rw [FiC_neg (r := r) (n := (L : ℤ) - a1) (by omega)]; simp
    · rw [FiC_neg (r := r) (n := (L : ℤ) - a2) (by omega)]; simp
    · rw [FiC_neg (r := r) (n := (L : ℤ) - a3) (by omega)]; simp
    · rw [FiC_neg (r := r) (n := (L : ℤ) - a4) (by omega)]; simp
  have hG1 : Gq (Fi := FiC r) (Pn := PnC r) (uC r)
      (rhoC (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3))
      a1 a2 a3 a4 b1 b2 b3 ((L : ℤ) + ((b1 + 1 - L).toNat : ℕ)) = 0 := by
    unfold Gq Gb
    rw [hn, FiC_neg (r := r) (n := b1 - (b1 + 1)) (by omega)]; simp
  have T := telescope (Fi := FiC r) (Pn := PnC r) (N := (r : ℤ) - 2) hu hd two_ne_zero
    (FiC_step hr) a1 a2 a3 a4 b1 b2 b3 (L : ℤ) (b1 + 1 - L).toNat _ _ _ _ _ _
    (fun z hz _ => PnC_step r hr _ (by omega))
    (fun z _ hz => by omega) (fun z _ hz => by omega) (fun z _ hz => by omega)
    (fun z _ hz => by omega) (fun z _ hz => by omega) (fun z _ hz => by omega)
    (fun z _ hz => by omega) rfl rfl rfl rfl rfl rfl
    (by rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu,
      ← zpow_add₀ hu]; congr 1; omega)
    hQ0 hQ1 hQ2 hDc hG0 hG1
  have tc : ∀ (c1 c2 c3 c4 d1 d2 d3 : ℤ) (k : ℕ),
      tt (Fi := FiC r) (Pn := PnC r) c1 c2 c3 c4 d1 d2 d3 ((L : ℤ) + k) =
        ((qRacahTerm r c1 c2 c3 c4 d1 d2 d3 (L + k) : ℝ) : ℂ) := by
    intro c1 c2 c3 c4 d1 d2 d3 k
    have := tt_eq_qRacahTerm r c1 c2 c3 c4 d1 d2 d3 (L + k)
    push_cast at this
    exact this
  simp only [tc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at T
  unfold rcR
  rw [e0, e1, e2]
  push_cast
  linear_combination T

lemma qRacahTerm_zero_of_gt {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ} (h : b1 < (z : ℤ)) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold qRacahTerm
  have : invQFact r (b1 - z) = 0 := by
    simp only [invQFact, show ¬ (0 ≤ b1 - (z : ℤ)) by omega, ↓reduceIte]
  simp [this]

end Lightlike.TV.Refl
