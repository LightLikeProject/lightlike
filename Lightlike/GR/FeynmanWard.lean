import Lightlike.GR.FeynmanRecursion

/-!
# The Ward identity of the colour-ordered Feynman amplitudes for every number of gluons

The currents of `ColourOrderedFeynman.lean` (the colour-ordered Feynman rules of Elvang-Huang p. 22, Gervais-Neveu
gauge) are not conserved off shell. They satisfy instead, for null momenta and transverse polarizations,

  `P_{a,b} · J(a, …, b) = −(1/√2) Σ_c J(a, …, c) · J(c+1, …, b)`   (`mdot_momRange_bgCurrent`),

derived here by strong induction on the recursion (the source read for the currents, Dixon, hep-ph/9601359,
p. 22, (57), states current conservation `P_{1,n} · J(1, …, n) = 0` for the Feynman-gauge vertices (53); the
Gervais-Neveu identity above is not printed there). Multiplied by `P²` it is a polynomial identity
(`mdot_momRange_bgVertexSum`); at `P² = 0` it is the on-shell Ward identity at the last gluon for every `n`
(`ward_last`).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, the Ward identity, p. 17; the Feynman rules, p. 22.
* L. Dixon, *Calculating scattering amplitudes efficiently*, hep-ph/9601359, §3.2: the current recursion (52)–(54),
  p. 21, and current conservation (57) in Feynman gauge, p. 22.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

section Ward

variable (p e : ℕ → Fin 4 → ℂ)

/-- The sum over the splittings `[a, c] [c+1, b]` of the products of the two currents. -/
def currentPairSum (a b : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico a b, mdot (bgCurrent p e a c) (bgCurrent p e (c + 1) b)

lemma mdot_vertex3_add (a pa b pb : Fin 4 → ℂ) :
    mdot (pa + pb) (vertex3 a pa b pb) =
      -((Real.sqrt 2 : ℝ) : ℂ) * (mdot a b * mdot (pa + pb) pa - mdot pa a * mdot b (pa + pb)) := by
  simp only [vertex3, mdot, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma mdot_add_self_left (u v : Fin 4 → ℂ) :
    mdot (u + v) u = (mdot (u + v) (u + v) + mdot u u - mdot v v) / 2 := by
  simp only [mdot, Pi.add_apply]; ring

lemma momRange_split {a c b : ℕ} (h1 : a ≤ c) (h2 : c < b) :
    momRange p a b = momRange p a c + momRange p (c + 1) b := by
  unfold momRange
  rw [Finset.sum_Ico_consecutive _ (by omega : a ≤ c + 1) (by omega : c + 1 ≤ b + 1)]

/-- The recursion without the division: `P² J = (planar vertices)`, also for one gluon of null momentum. -/
lemma smul_bgCurrent {a b : ℕ} (hab : a ≤ b) (hnull : mdot (p a) (p a) = 0)
    (hprop : a < b → mdot (momRange p a b) (momRange p a b) ≠ 0) :
    mdot (momRange p a b) (momRange p a b) • bgCurrent p e a b = bgVertexSum (bgCurrent p e) p a b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · have hm : momRange p a a = p a := by simp [momRange]
    rw [hm, hnull, zero_smul]
    simp [bgVertexSum]
  · rw [bgCurrent_of_lt p e hlt, smul_smul, mul_one_div_cancel (hprop hlt), one_smul]

lemma sqrt_two_ne_zero_complex : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))

/-- The cancellation for a splitting `A | B | C` into three consecutive intervals, `P = P_A + P_B + P_C`. -/
lemma split3_cancel (x α y β z γ : Fin 4 → ℂ) :
    -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot z (vertex3 x α y β) +
      (1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot x (vertex3 y β z γ) -
      mdot x y * mdot z (α + β + γ) + mdot x z * mdot (α + β + γ) y = 0 := by
  have hr := sqrt_two_ne_zero_complex
  simp only [vertex3, mdot_smul_right, mdot_add_right, mdot_neg_right]
  field_simp
  simp only [mdot, Pi.add_apply]
  ring

/-- The cancellation for a splitting `A | B | C | D` into four consecutive intervals. -/
lemma split4_cancel (w x y z : Fin 4 → ℂ) :
    -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot z (vertex4 w x y) +
      (1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot w (vertex4 x y z) = 0 := by
  simp only [vertex4, mdot_smul_right]
  rw [mdot_comm z x, mdot_comm w y]
  ring

/-- The induction step of `mdot_momRange_bgCurrent`. -/
lemma mdot_momRange_bgVertexSum_step {a b : ℕ} (hab : a < b)
    (hD : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a →
      mdot (momRange p c d) (bgCurrent p e c d) = -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * currentPairSum p e c d)
    (hS : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a →
      mdot (momRange p c d) (momRange p c d) • bgCurrent p e c d = bgVertexSum (bgCurrent p e) p c d) :
    mdot (momRange p a b) (bgVertexSum (bgCurrent p e) p a b) =
      -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot (momRange p a b) (momRange p a b) * currentPairSum p e a b := by
  have hr := sqrt_two_ne_zero_complex
  have hr2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hrdef
  set J := bgCurrent p e with hJ
  set P := momRange p with hP
  set VS := bgVertexSum J p with hVS
  -- the three-gluon vertices of the last step
  have h3 : ∀ c ∈ Finset.Ico a b, mdot (P a b) (vertex3 (J a c) (P a c) (J (c + 1) b) (P (c + 1) b)) =
      -(1 / r) * mdot (P a b) (P a b) * mdot (J a c) (J (c + 1) b) -
        (1 / r) * (mdot (J (c + 1) b) (VS a c) - mdot (J a c) (VS (c + 1) b)) -
          currentPairSum p e a c * mdot (J (c + 1) b) (P a b) := by
    intro c hc
    have hc := Finset.mem_Ico.1 hc
    have hsplit : P a b = P a c + P (c + 1) b := momRange_split p hc.1 hc.2
    rw [← hS a c le_rfl hc.1 (by omega) (by omega), ← hS (c + 1) b (by omega) (by omega) le_rfl (by omega),
      mdot_smul_right, mdot_smul_right, hsplit, mdot_vertex3_add, mdot_add_self_left,
      hD a c le_rfl hc.1 (by omega) (by omega)]
    rw [mdot_comm (J (c + 1) b) (J a c)]
    field_simp
    linear_combination (-(mdot (J a c) (J (c + 1) b)) *
      (mdot (P a c + P (c + 1) b) (P a c + P (c + 1) b) + mdot (P a c) (P a c) -
        mdot (P (c + 1) b) (P (c + 1) b))) * hr2
  -- the sums over the splittings into three and four consecutive intervals
  have hswap : ∀ F : ℕ → ℕ → ℂ, ∑ c ∈ Finset.Ico a b, ∑ u ∈ Finset.Ico a c, F u c =
      ∑ u ∈ Finset.Ico a b, ∑ c ∈ Finset.Ico (u + 1) b, F u c := by
    intro F
    exact Finset.sum_comm' fun c u => by simp only [Finset.mem_Ico]; omega
  have hswap' : ∀ (u : ℕ) (G : ℕ → ℕ → ℂ), ∑ c ∈ Finset.Ico (u + 1) b, ∑ w ∈ Finset.Ico (u + 1) c, G w c =
      ∑ w ∈ Finset.Ico (u + 1) b, ∑ c ∈ Finset.Ico (w + 1) b, G w c := by
    intro u G
    exact Finset.sum_comm' fun c w => by simp only [Finset.mem_Ico]; omega
  set A13 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b,
    mdot (J (v + 1) b) (vertex3 (J a u) (P a u) (J (u + 1) v) (P (u + 1) v)) with hA13
  set A14 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b, ∑ w ∈ Finset.Ico (v + 1) b,
    mdot (J (w + 1) b) (vertex4 (J a u) (J (u + 1) v) (J (v + 1) w)) with hA14
  set A23 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b,
    mdot (J a u) (vertex3 (J (u + 1) v) (P (u + 1) v) (J (v + 1) b) (P (v + 1) b)) with hA23
  set A24 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b, ∑ w ∈ Finset.Ico (v + 1) b,
    mdot (J a u) (vertex4 (J (u + 1) v) (J (v + 1) w) (J (w + 1) b)) with hA24
  set A33 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b,
    mdot (J a u) (J (u + 1) v) * mdot (J (v + 1) b) (P a b) with hA33
  set A43 := ∑ u ∈ Finset.Ico a b, ∑ v ∈ Finset.Ico (u + 1) b,
    mdot (P a b) (vertex4 (J a u) (J (u + 1) v) (J (v + 1) b)) with hA43
  have hX1 : ∑ c ∈ Finset.Ico a b, mdot (J (c + 1) b) (VS a c) = A13 + A14 := by
    have : ∀ c, mdot (J (c + 1) b) (VS a c) =
        ∑ u ∈ Finset.Ico a c, mdot (J (c + 1) b) (vertex3 (J a u) (P a u) (J (u + 1) c) (P (u + 1) c)) +
          ∑ u ∈ Finset.Ico a c, ∑ w ∈ Finset.Ico (u + 1) c,
            mdot (J (c + 1) b) (vertex4 (J a u) (J (u + 1) w) (J (w + 1) c)) := by
      intro c
      simp only [hVS, bgVertexSum, mdot_add_right, mdot_sum_right]
      rfl
    simp only [this, Finset.sum_add_distrib]
    rw [hswap, hswap]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact hswap' u fun w c => mdot (J (c + 1) b) (vertex4 (J a u) (J (u + 1) w) (J (w + 1) c))
  have hX2 : ∑ c ∈ Finset.Ico a b, mdot (J a c) (VS (c + 1) b) = A23 + A24 := by
    simp only [hVS, bgVertexSum, mdot_add_right, mdot_sum_right, Finset.sum_add_distrib]
    rfl
  have hX3 : ∑ c ∈ Finset.Ico a b, currentPairSum p e a c * mdot (J (c + 1) b) (P a b) = A33 := by
    simp only [currentPairSum, Finset.sum_mul]
    exact hswap fun u c => mdot (J a u) (J (u + 1) c) * mdot (J (c + 1) b) (P a b)
  have hS3 : -(1 / r) * A13 + (1 / r) * A23 - A33 + A43 = 0 := by
    simp only [hA13, hA23, hA33, hA43, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => ?_
    have hu := Finset.mem_Ico.1 hu
    have hv := Finset.mem_Ico.1 hv
    have hsplit : P a b = P a u + P (u + 1) v + P (v + 1) b := by
      have h1 := momRange_split p hu.1 hu.2
      have h2 := momRange_split p (by omega : u + 1 ≤ v) hv.2
      simp only [hP]
      rw [h1, h2, add_assoc]
    have h4 : mdot (P a b) (vertex4 (J a u) (J (u + 1) v) (J (v + 1) b)) =
        mdot (J a u) (J (v + 1) b) * mdot (P a b) (J (u + 1) v) := by
      simp only [vertex4, mdot_smul_right]
    rw [h4, hsplit]
    exact split3_cancel _ _ _ _ _ _
  have hS4 : -(1 / r) * A14 + (1 / r) * A24 = 0 := by
    simp only [hA14, hA24, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ =>
      split4_cancel _ _ _ _
  -- assemble
  have hVab : VS a b = (∑ c ∈ Finset.Ico a b, vertex3 (J a c) (P a c) (J (c + 1) b) (P (c + 1) b)) +
      ∑ c ∈ Finset.Ico a b, ∑ d ∈ Finset.Ico (c + 1) b, vertex4 (J a c) (J (c + 1) d) (J (d + 1) b) := rfl
  rw [hVab, mdot_add_right, mdot_sum_right, Finset.sum_congr rfl h3]
  have hX4 : mdot (P a b) (∑ c ∈ Finset.Ico a b, ∑ d ∈ Finset.Ico (c + 1) b,
      vertex4 (J a c) (J (c + 1) d) (J (d + 1) b)) = A43 := by
    simp only [hA43, mdot_sum_right]
  rw [hX4, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hX1, hX2, hX3,
    show currentPairSum p e a b = ∑ c ∈ Finset.Ico a b, mdot (J a c) (J (c + 1) b) from rfl]
  linear_combination hS3 + hS4

/-- **The off-shell identity of the Gervais-Neveu currents** (derived here; the source's Feynman-gauge analogue is
current conservation, Dixon hep-ph/9601359 (57), p. 22): for null momenta, transverse polarizations and nonvanishing
propagators, `P_{a,b} · J(a, …, b) = −(1/√2) Σ_c J(a, …, c) · J(c+1, …, b)`. -/
theorem mdot_momRange_bgCurrent :
    ∀ n a b, b - a = n → a ≤ b →
      (∀ t, a ≤ t → t ≤ b → mdot (p t) (p t) = 0) → (∀ t, a ≤ t → t ≤ b → mdot (e t) (p t) = 0) →
      (∀ c d, a ≤ c → c < d → d ≤ b → mdot (momRange p c d) (momRange p c d) ≠ 0) →
      mdot (momRange p a b) (bgCurrent p e a b) = -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * currentPairSum p e a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab hnull htr hprop
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · have hm : momRange p a a = p a := by simp [momRange]
      rw [hm, bgCurrent_self, mdot_comm, htr a le_rfl le_rfl]
      simp [currentPairSum]
    · have key := mdot_momRange_bgVertexSum_step p e hlt
        (fun c d h1 h2 h3 h4 => ih (d - c) (by omega) c d rfl h2
          (fun t ht1 ht2 => hnull t (by omega) (by omega)) (fun t ht1 ht2 => htr t (by omega) (by omega))
          (fun c' d' k1 k2 k3 => hprop c' d' (by omega) k2 (by omega)))
        (fun c d h1 h2 h3 h4 => smul_bgCurrent p e h2 (hnull c h1 (by omega))
          (fun h => hprop c d h1 h h3))
      have hs := hprop a b le_rfl hlt le_rfl
      rw [bgCurrent_of_lt p e hlt, mdot_smul_right, key]
      field_simp

/-- **The off-shell identity times `P²`**, a polynomial identity: it holds also where the propagator of `[a, b]` itself
vanishes. -/
theorem mdot_momRange_bgVertexSum {a b : ℕ} (hab : a < b)
    (hnull : ∀ t, a ≤ t → t ≤ b → mdot (p t) (p t) = 0) (htr : ∀ t, a ≤ t → t ≤ b → mdot (e t) (p t) = 0)
    (hprop : ∀ c d, a ≤ c → c < d → d ≤ b → ¬ (c = a ∧ d = b) →
      mdot (momRange p c d) (momRange p c d) ≠ 0) :
    mdot (momRange p a b) (bgVertexSum (bgCurrent p e) p a b) =
      -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * mdot (momRange p a b) (momRange p a b) * currentPairSum p e a b :=
  mdot_momRange_bgVertexSum_step p e hab
    (fun c d h1 h2 h3 h4 => mdot_momRange_bgCurrent p e (d - c) c d rfl h2
      (fun t ht1 ht2 => hnull t (by omega) (by omega)) (fun t ht1 ht2 => htr t (by omega) (by omega))
      (fun c' d' k1 k2 k3 => hprop c' d' (by omega) k2 (by omega) (by omega)))
    (fun c d h1 h2 h3 h4 => smul_bgCurrent p e h2 (hnull c h1 (by omega))
      (fun h => hprop c d h1 h h3 (by omega)))

end Ward

/-- **The Ward identity at the last gluon, for every number of gluons** (Elvang-Huang p. 17): from the off-shell identity,
`p_n · (amputated current) = (1/√2) P² Σ J·J = 0` on shell. -/
theorem ward_last (m : ℕ) : WardIdentity m (m + 2) := by
  intro p e hnull hcons hprop htr
  have hp : p (m + 2) = -momRange p 0 (m + 1) := by
    have : momRange p 0 (m + 2) = momRange p 0 (m + 1) + p (m + 2) := by
      rw [momRange, momRange, Finset.sum_Ico_succ_top (by omega)]
    rw [this] at hcons
    exact eq_neg_of_add_eq_zero_right hcons
  have hcur : ∀ c d, c ≤ d → d ≤ m + 1 →
      bgCurrent p (Function.update e (m + 2) (p (m + 2))) c d = bgCurrent p e c d :=
    fun c d h1 h2 => bgCurrent_congr (d - c) c d rfl h1 fun t _ ht =>
      ⟨rfl, Function.update_of_ne (by omega) _ _⟩
  rw [bgAmplitude, Function.update_self,
    bgVertexSum_congr' (p' := p) (T' := bgCurrent p e) (fun _ _ _ => rfl)
      fun c d _ h2 h3 _ => hcur c d h2 h3]
  have hnull' := hnull (m + 2) le_rfl
  rw [hp] at hnull' ⊢
  rw [mdot_neg_left, mdot_momRange_bgVertexSum p e (by omega)
    (fun t _ ht => hnull t (by omega)) (fun t _ ht => htr t (by omega) (by omega))
    (fun c d h1 h2 h3 h4 => hprop c d h2 h3 (by omega))]
  rw [mdot_neg_left, mdot_neg_right, neg_neg] at hnull'
  rw [hnull']
  ring

end Lightlike.SpinorHelicity
