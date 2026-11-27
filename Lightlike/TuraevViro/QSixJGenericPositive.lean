import Mathlib
import Lightlike.TuraevViro.QSixJGenericPentagon

/-!
# The generic Biedenharn–Elliott identity for positive outer colours

`GenBE θ` (`Lightlike.TV.GenBE`) for colours with `e, a, b ≥ 1`, from the pentagon identity
`TemperleyLieb.pentagon` of the recoupling coefficients `Fc` of the Temperley–Lieb model at
`q = e^{iθ}`, given that `Fc` is the Kauffman–Lins coefficient `klCoef` on its admissible indices
(`TemperleyLieb.FcEqKL ℂ`); the remaining colours and the full statement are in `QSixJGenericBE`.

* `kladm_of_tri`, `tri_of_kladm`: the admissibilities of the pentagon terms are the triangle conditions
  of the middle colour; `sum_reindex`: the sum over `f` is the sum over the middle colour;
* `genBE_of_pos`: `GenBE θ` for colours with `e, a, b ≥ 1` (the pentagon needs three nonempty blocks).

The dictionary between the pentagon and `GenBE` (blocks `(a,b,c,d) = (e',a',b',c')`, channels
`I1 = r'`, `I2 = f'`, total `T = q`, `J1 = p`, `J2 = d'`, summed `x = b + c - 2f`) was derived and
measured by the oscillatory stream (mpmath, 40 digits); it is numerical evidence, not part of the proof.
-/

open Complex Finset Lightlike.Pentagon

namespace Lightlike.TV

open Lightlike.TemperleyLieb

/-! ## Admissibility and the triangles of the middle colour -/

/-- A triangle `(x, y, z)` in multiplied-out form: `x + y = z + 2u` with `u ≤ x`, `u ≤ y`,
`u = (x + y - z)/2`. -/
theorem tri_halves {x y z : ℕ} (h : Tri x y z) :
    x + y = z + 2 * ((x + y - z) / 2) ∧ (x + y - z) / 2 ≤ x ∧ (x + y - z) / 2 ≤ y := by
  unfold Tri at h; omega

/-- **The three admissibilities of the left side of the pentagon from the triangles of `x`**
(in multiplied-out form). -/
theorem kladm_of_tri {a b c d e f p q r' e₀ d₀ g₀ j m i fi x h dd : ℕ}
    (hx : x + 2 * fi = a + b) (hfa : fi ≤ a) (hfb : fi ≤ b)
    (hh : x + c = d + 2 * h) (hhx : h ≤ x) (hhc : h ≤ c)
    (hdd : e + x = f + 2 * dd) (hde : dd ≤ e) (hdx : dd ≤ x)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d) :
    KLAdm a b c fi h j m ∧ KLAdm e (a + b - 2 * fi) c dd g₀ h i ∧ KLAdm e a b e₀ d₀ fi dd := by
  unfold KLAdm
  simp only [le_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩,
    ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩ <;> omega

/-- **The triangles of `x` from the admissibilities** (the converse of `kladm_of_tri`). -/
theorem tri_of_kladm {a b c d e f p r' e₀ d₀ j m fi h dd : ℕ}
    (h1 : e + a = r' + 2 * e₀) (h2 : r' + b = f + 2 * d₀)
    (h4 : b + c = p + 2 * j) (_h4a : j ≤ b) (_h4b : j ≤ c) (h5 : a + p = d + 2 * m) (h5a : m ≤ a)
    (h5b : m ≤ p)
    (A1 : KLAdm a b c fi h j m) (A3 : KLAdm e a b e₀ d₀ fi dd) :
    Tri a b (a + b - 2 * fi) ∧ Tri c d (a + b - 2 * fi) ∧ Tri e f (a + b - 2 * fi) := by
  unfold KLAdm at A1 A3
  simp only [le_min_iff] at A1 A3
  obtain ⟨⟨a11, a12⟩, ⟨a21, a22⟩, -, -, a5⟩ := A1
  obtain ⟨⟨b11, b12⟩, ⟨b21, b22⟩, -, ⟨b41, b42⟩, b5⟩ := A3
  unfold Tri
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> omega

theorem tri_swap₁₂ {x y z : ℕ} (h : Tri x y z) : Tri y x z := by unfold Tri at *; omega

theorem tri_rot {x y z : ℕ} (h : Tri x y z) : Tri y z x := by unfold Tri at *; omega

/-- The q-Racah sum vanishes when a face sum exceeds a pair sum (its support is empty). -/
theorem racahG_eq_zero_of_lt (θ : ℝ) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : min ((j₁ + j₂ + j₄ + j₅) / 2) (min ((j₂ + j₃ + j₅ + j₆) / 2) ((j₃ + j₁ + j₆ + j₄) / 2)) <
      max (max ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2)) (max ((j₄ + j₂ + j₆) / 2) ((j₄ + j₅ + j₃) / 2))) :
    racahG θ j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  rw [racahG_eq_Icc, Icc_eq_empty (by omega), sum_empty]

/-- **Reindexing the sum of `GenBE`** by `x = a + b - 2f`: a function supported on the triangles
`(a, b, x)` sums over `x ≤ a + b` as over `f ≤ min a b`. -/
theorem sum_reindex {a b : ℕ} (g : ℕ → ℝ) (hg : ∀ x, g x ≠ 0 → Tri a b x) :
    ∑ fi ∈ range (a + 1), (if fi ≤ min a b then g (a + b - 2 * fi) else 0) =
      ∑ x ∈ range (a + b + 1), g x := by
  refine sum_bij_ne_zero (fun fi _ _ => a + b - 2 * fi) ?_ ?_ ?_ ?_
  · intro fi hfi hne
    simp only [mem_range] at hfi ⊢
    omega
  · intro f₁ h₁₁ h₁₂ f₂ h₂₁ h₂₂ heq
    have k1 : f₁ ≤ min a b := by by_contra hc; exact h₁₂ (by rw [ite_eq_right hc])
    have k2 : f₂ ≤ min a b := by by_contra hc; exact h₂₂ (by rw [ite_eq_right hc])
    simp only [le_min_iff] at k1 k2
    omega
  · intro x hx hgx
    have ht := hg x hgx
    unfold Tri at ht
    refine ⟨(a + b - x) / 2, by simp only [mem_range]; omega, ?_, ?_⟩
    · rw [ite_eq_left (by simp only [le_min_iff]; omega),
        show a + b - 2 * ((a + b - x) / 2) = x by omega]
      exact hgx
    · omega
  · intro fi _ hne
    have k : fi ≤ min a b := by by_contra hc; exact hne (by rw [ite_eq_right hc])
    rw [ite_eq_left k]

/-! ## The generic Biedenharn–Elliott identity, positive colours -/

/-- The admissibilities of the right side of the pentagon from the triangle `(r', p, q)`. -/
theorem kladm_right_of_tri {a b c d e f p q r' e₀ d₀ g₀ j m i gF : ℕ}
    (hg : r' + p = q + 2 * gF) (hgr : gF ≤ r') (hgp : gF ≤ p)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d) :
    KLAdm e a p e₀ gF m i ∧ KLAdm r' b c d₀ g₀ j gF := by
  unfold KLAdm
  simp only [le_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem gaugeI_ne_zero (θ : ℝ) {N a b c i D : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h1 : triPi θ a b i ≠ 0) (h2 : triPi θ i c D ≠ 0) (hi : i + 1 ≤ N) : gaugeI θ a b c i D ≠ 0 :=
  div_ne_zero (mul_ne_zero h1 h2) (hq _ hi)

theorem gaugeJ_ne_zero (θ : ℝ) {N a b c j D : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h1 : triPi θ b c j ≠ 0) (h2 : triPi θ a j D ≠ 0) (hj : j + 1 ≤ N) : gaugeJ θ a b c j D ≠ 0 :=
  div_ne_zero (mul_ne_zero h1 h2) (hq _ hj)

theorem delta2G_ne_zero (θ : ℝ) {N x y z : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h : triPi θ x y z ≠ 0) (hs : (x + y + z) / 2 + 1 ≤ N) : delta2G θ x y z ≠ 0 := by
  rw [delta2G_eq_triPi]; exact div_ne_zero h (hq _ hs)

/-- The q-Racah sum of the right side of `GenBE` vanishes when `(p, q, r')` violates a triangle
inequality (its support is empty). -/
theorem racahG_eq_zero_of_tri_fail (θ : ℝ) {p q r' e a d e₀ m i : ℕ} (h1 : e + a = r' + 2 * e₀)
    (h5 : a + p = d + 2 * m) (h6 : e + d = q + 2 * i) (hpar : (p + q + r') % 2 = 0)
    (hn : r' + p < q ∨ q + r' < p ∨ p + q < r') : racahG θ p q r' e a d = 0 := by
  apply racahG_eq_zero_of_lt
  rcases hn with h | h | h
  · have k : (r' + p + d + e) / 2 < (e + q + d) / 2 := by omega
    exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (lt_of_lt_of_le k ((le_max_left _ _).trans (le_max_right _ _)))
  · have k : (q + r' + a + d) / 2 < (p + a + d) / 2 := by omega
    exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
      (lt_of_lt_of_le k ((le_max_right _ _).trans (le_max_left _ _)))
  · have k : (p + q + e + a) / 2 < (e + a + r') / 2 := by omega
    exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le k ((le_max_right _ _).trans (le_max_right _ _)))


theorem triPi_ne_zero' (θ : ℝ) {M x y z : ℕ} (hq : ∀ n, n ≤ M → qfG θ n ≠ 0) (h : x + y + z ≤ 2 * M) :
    triPi θ x y z ≠ 0 :=
  triPi_ne_zero θ hq (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **One term of the left side of the pentagon at `q = e^{iθ}`** is the summand of `GenBE` at
`x = a + b - 2f`, times the gauge `G` and the common factor `C`. -/
theorem genBE_left_term (θ : ℝ) {a b c d e f p q r' e₀ d₀ g₀ j m i M : ℕ}
    (hqf : ∀ n, n ≤ M → qfG θ n ≠ 0) (hM : 2 * (a + b + c + d + e + f + p + q + r') + 4 ≤ M)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d)
    (hI1 : e + a - 2 * e₀ = r') (hI2 : r' + b - 2 * d₀ = f) (hTq : f + c - 2 * g₀ = q)
    (hJ1 : b + c - 2 * j = p) :
    ∀ fi ∈ range (a + 1),
      klCoef (qE θ) a b c fi ((a + b - 2 * fi + c - d) / 2) j m *
        (klCoef (qE θ) e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀
            ((a + b - 2 * fi + c - d) / 2) i *
          klCoef (qE θ) e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)) =
      (((gaugeJ θ e a p d q / gaugeI θ e a p r' q * (gaugeJ θ r' b c p q / gaugeI θ r' b c f q)) *
        ((-1 : ℝ) ^ (r' + (e + a + r') / 2 + (r' + p + q) / 2 + (f + (r' + b + f) / 2 + (f + c + q) / 2)) *
          (qnG θ (p + 1) * qnG θ (d + 1) * delta2G θ e a r' * delta2G θ r' b f * delta2G θ f c q)) *
        (if fi ≤ min a b then genBETerm θ a b c d e f p q r' (a + b - 2 * fi) else 0) : ℝ) : ℂ) := by
  have hTP : ∀ x y z : ℕ, x + y + z ≤ 2 * M → triPi θ x y z ≠ 0 := fun x y z h => triPi_ne_zero' θ hqf h
  intro fi hfi
  rw [mem_range] at hfi
  have hq1 : ∀ n, n ≤ a + b + c + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  have hq2 : ∀ n, n ≤ e + (a + b - 2 * fi) + c + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  have hq3 : ∀ n, n ≤ e + a + b + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  by_cases hA : KLAdm a b c fi ((a + b - 2 * fi + c - d) / 2) j m ∧
      KLAdm e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀ ((a + b - 2 * fi + c - d) / 2) i ∧
      KLAdm e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)
  · obtain ⟨A1, A2, A3⟩ := hA
    obtain ⟨T1, T2, T3⟩ := tri_of_kladm h1 h2 h4 h4a h4b h5 h5a h5b A1 A3
    have hfm : fi ≤ min a b := A3.2.2.1
    rw [klCoef_qE θ A1 hq1, klCoef_qE θ A2 hq2, klCoef_qE θ A3 hq3, ite_eq_left hfm]
    clear A1 A2 A3 hfm hq1 hq2 hq3
    unfold genBETerm
    rw [ite_eq_left ⟨T1, T2, T3⟩]
    unfold Tri at T1 T2 T3
    have hx1 : a + b - 2 * fi + c - 2 * ((a + b - 2 * fi + c - d) / 2) = d := by omega
    have hx2 : e + (a + b - 2 * fi) - 2 * ((e + (a + b - 2 * fi) - f) / 2) = f := by omega
    rw [hJ1, hx1, hx2, hTq, hI1, hI2, ← ofReal_mul, ← ofReal_mul, ofReal_inj]
    have hk := klK_left θ (a := e) (b := a) (c := b) (d := c) (x := a + b - 2 * fi) (I1 := r') (I2 := f)
      (T := q) (J1 := p) (J2 := d) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have hfa : fi ≤ a := by omega
    clear h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b T1 T2 T3 hI1 hI2 hTq hJ1 hx1 hx2
    have hg := gauge_cancel θ (a := e) (b := a) (c := b) (d := c) (x := a + b - 2 * fi) (I1 := r') (I2 := f)
      (T := q) (J1 := p) (J2 := d) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega))
      (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega))
      (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega))
    calc _ = (gaugeJ θ a b c p d / gaugeI θ a b c (a + b - 2 * fi) d *
            (gaugeJ θ e (a + b - 2 * fi) c d q / gaugeI θ e (a + b - 2 * fi) c f q *
              (gaugeJ θ e a b (a + b - 2 * fi) f / gaugeI θ e a b r' f))) *
          (klK θ a b c (a + b - 2 * fi) d p *
            (klK θ e (a + b - 2 * fi) c f q d * klK θ e a b r' f (a + b - 2 * fi))) := by ring
      _ = _ := by rw [hg, hk]; ring
  · have h0 : klCoef (qE θ) a b c fi ((a + b - 2 * fi + c - d) / 2) j m *
        (klCoef (qE θ) e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀
            ((a + b - 2 * fi + c - d) / 2) i *
          klCoef (qE θ) e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)) = 0 := by
      by_cases A1 : KLAdm a b c fi ((a + b - 2 * fi + c - d) / 2) j m
      · by_cases A3 : KLAdm e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)
        · exfalso
          obtain ⟨T1, T2, T3⟩ := tri_of_kladm h1 h2 h4 h4a h4b h5 h5a h5b A1 A3
          have hfa : fi ≤ a := A3.2.2.1.trans (min_le_left _ _)
          have hfb : fi ≤ b := A3.2.2.1.trans (min_le_right _ _)
          clear A1 A3 hq1 hq2 hq3
          unfold Tri at T1 T2 T3
          refine hA (kladm_of_tri (x := a + b - 2 * fi) (by omega) hfa hfb (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b)
        · rw [klCoef_of_not _ A3, mul_zero, mul_zero]
      · rw [klCoef_of_not _ A1, zero_mul]
    rw [h0]
    have hz : (if fi ≤ min a b then genBETerm θ a b c d e f p q r' (a + b - 2 * fi) else 0) = 0 := by
      split_ifs with hfm
      · unfold genBETerm
        refine ite_eq_right fun hT => hA ?_
        obtain ⟨T1, T2, T3⟩ := hT
        unfold Tri at T1 T2 T3
        simp only [le_min_iff] at hfm
        obtain ⟨hfa, hfb⟩ := hfm
        clear hq1 hq2 hq3
        exact kladm_of_tri (x := a + b - 2 * fi) (by omega) hfa hfb (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b
      · rfl
    rw [hz, mul_zero, ofReal_zero]

set_option maxHeartbeats 1000000 in
/-- **The generic Biedenharn–Elliott identity when the colours `e`, `a`, `b` are positive**, from the
Temperley–Lieb pentagon at `q = e^{iθ}` and `FcEqKL ℂ`. -/
theorem genBE_of_pos (hKL : FcEqKL ℂ) (θ : ℝ) {a b c d e f p q r' : ℕ}
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d + e + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0)
    (he : 1 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b) : GenBE θ a b c d e f p q r' := by
  intro t1 t2 t3 t4 t5 t6
  obtain ⟨h1, h1a, h1b⟩ := tri_halves t5
  obtain ⟨h2, h2a, h2b⟩ := tri_halves (tri_rot (tri_rot t6))
  obtain ⟨h3, h3a, h3b⟩ := tri_halves (tri_swap₁₂ t3)
  obtain ⟨h4, h4a, h4b⟩ := tri_halves (tri_swap₁₂ t2)
  obtain ⟨h5, h5a, h5b⟩ := tri_halves (tri_swap₁₂ (tri_rot (tri_rot t1)))
  obtain ⟨h6, h6a, h6b⟩ := tri_halves t4
  clear t1 t2 t3 t4 t5 t6
  set e₀ := (e + a - r') / 2
  set d₀ := (r' + b - f) / 2
  set g₀ := (f + c - q) / 2
  set j := (b + c - p) / 2
  set m := (a + p - d) / 2
  set i := (e + d - q) / 2
  set N := 2 * (a + b + c + d + e + f + p + q + r') + 4
  have hs1 : Real.sin θ ≠ 0 := by simpa using hθ 1 le_rfl (by omega)
  have hqf : ∀ n, n ≤ N → qfG θ n ≠ 0 := qfG_ne_zero hθ hs1
  have hI1 : e + a - 2 * e₀ = r' := by omega
  have hI2 : r' + b - 2 * d₀ = f := by omega
  have hTq : f + c - 2 * g₀ = q := by omega
  have hJ1 : b + c - 2 * j = p := by omega
  have hJ2 : a + p - 2 * m = d := by omega
  have hTi : e + d - 2 * i = q := by omega
  have P := pentagon_klCoef hKL (qE θ) (loopVal_qE_ne_zero (hθ 2 (by omega) (by omega)))
    e a b c e₀ d₀ g₀ j m i he ha hb
    (fun x hx => chebD_qE_ne_zero hs1 (hθ (x + 1) (by omega) (by omega)))
    (fun n h1 h2 => qE_pow_ne_one (hθ n h1 (by omega)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨by simp only [le_min_iff]; omega, by simp only [le_min_iff]; omega, by omega, by omega⟩
  rw [hJ1, hJ2, hI1, hI2, hTi] at P
  have hTP : ∀ x y z : ℕ, (x + y + z) / 2 ≤ N → triPi θ x y z ≠ 0 := fun x y z h =>
    triPi_ne_zero θ hqf (by omega) (by omega) (by omega)
  have hqn : ∀ n, n + 1 ≤ N → qnG θ (n + 1) ≠ 0 := fun n hn =>
    qnG_ne_zero hs1 (by exact_mod_cast hθ (n + 1) (by omega) hn)
  set G := gaugeJ θ e a p d q / gaugeI θ e a p r' q * (gaugeJ θ r' b c p q / gaugeI θ r' b c f q) with hG
  set C := (-1 : ℝ) ^ (r' + (e + a + r') / 2 + (r' + p + q) / 2 + (f + (r' + b + f) / 2 + (f + c + q) / 2)) *
      (qnG θ (p + 1) * qnG θ (d + 1) * delta2G θ e a r' * delta2G θ r' b f * delta2G θ f c q) with hC
  have hG0 : G ≠ 0 := by
    refine mul_ne_zero (div_ne_zero ?_ ?_) (div_ne_zero ?_ ?_)
    · exact gaugeJ_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeI_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeJ_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeI_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
  have hC0 : C ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hqn p (by omega)) (hqn d (by omega))) ?_) ?_) ?_
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
  -- the left side, term by term
  have hL := genBE_left_term θ hqf (le_refl _) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b hI1 hI2 hTq hJ1
  -- the right side
  have hR : klCoef (qE θ) e a p e₀ ((r' + p - q) / 2) m i * klCoef (qE θ) r' b c d₀ g₀ j ((r' + p - q) / 2) =
      ((G * C * (delta2G θ p q r' * racahG θ p q r' e a d * racahG θ p q r' f b c) : ℝ) : ℂ) := by
    by_cases hpq : r' + p = q + 2 * ((r' + p - q) / 2) ∧ (r' + p - q) / 2 ≤ r' ∧ (r' + p - q) / 2 ≤ p
    · obtain ⟨A4, A5⟩ := kladm_right_of_tri hpq.1 hpq.2.1 hpq.2.2 h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b
        h5 h5a h5b h6 h6a h6b
      have hgq : r' + p - 2 * ((r' + p - q) / 2) = q := by omega
      rw [klCoef_qE θ A4 (fun n hn => hqf n (by omega)), klCoef_qE θ A5 (fun n hn => hqf n (by omega))]
      rw [hI1, hgq, hJ2, hI2, hTq, hJ1, ← ofReal_mul, ofReal_inj]
      have hk := klK_right θ (a := e) (b := a) (c := b) (d := c) (I1 := r') (I2 := f) (T := q) (J1 := p) (J2 := d)
      calc _ = G * (klK θ e a p r' q d * klK θ r' b c f q p) := by rw [hG]; ring
        _ = _ := by rw [hk]; ring
    · have h4' : ¬ KLAdm e a p e₀ ((r' + p - q) / 2) m i := fun A4 => hpq (by
        unfold KLAdm at A4; simp only [le_min_iff] at A4; omega)
      rw [klCoef_of_not _ h4', zero_mul]
      have hpar : (p + q + r') % 2 = 0 := by omega
      have hn : r' + p < q ∨ q + r' < p ∨ p + q < r' := by omega
      have hz : racahG θ p q r' e a d = 0 := racahG_eq_zero_of_tri_fail θ h1 h5 h6 hpar hn
      rw [hz, mul_zero, zero_mul, mul_zero, ofReal_zero]
  rw [sum_congr rfl hL, hR] at P
  rw [← ofReal_sum, ofReal_inj, ← mul_sum] at P
  have P' := mul_left_cancel₀ (mul_ne_zero hG0 hC0) P
  rw [← P']
  exact (sum_reindex (genBETerm θ a b c d e f p q r') fun x hx => by
    unfold genBETerm at hx; split_ifs at hx with h; exact h.1; exact absurd rfl hx).symm

end Lightlike.TV
