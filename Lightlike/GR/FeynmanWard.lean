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

The planar sum does not depend on which gluon is last (`mdot_bgVertexSum_rotate`, `bgAmplitude_rotLabels`; the cyclic
property of Elvang-Huang p. 25): counting the vertices on the path from the first to the last gluon of every planar tree
by the line on their left and by the line on their right gives the two amplitudes plus the same sum over the path
propagators. Hence the Ward identity holds at every gluon (`ward_all`), and the factorization (3.5) and the recursion
(3.7) hold without the Ward hypotheses (`residue_factorization'`, `bgAmplitude_eq_sum_channels'`).

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


/-! ### Cyclic invariance of the planar sum (W2) -/

lemma mdot_vertex3_cyc (x px y py z : Fin 4 → ℂ) :
    mdot x (vertex3 y py z (-(px + py))) = mdot (vertex3 x px y py) z := by
  simp only [vertex3, mdot, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma mdot_vertex4_cyc (x y z w : Fin 4 → ℂ) : mdot x (vertex4 y z w) = mdot (vertex4 x y z) w := by
  simp only [vertex4, mdot_smul_right, mdot_smul_left]
  rw [mdot_comm x z]
  ring

section Cyclic

variable (p e : ℕ → Fin 4 → ℂ)

/-- **The planar sum does not depend on the gluon chosen last**: for momenta with `p_0 + ⋯ + p_N = 0` and nonvanishing
channel propagators, `ε_N · V(0, …, N−1) = ε_0 · V(1, …, N)`. Both sides are the sum over the vertices on the path
from gluon `0` to gluon `N` of the planar trees, counted by the line on the left and by the line on the right. -/
theorem mdot_bgVertexSum_rotate (N : ℕ) (hN : 2 ≤ N) (hcons : momRange p 0 N = 0)
    (hprop : ∀ d, 1 ≤ d → d + 2 ≤ N → mdot (momRange p 0 d) (momRange p 0 d) ≠ 0) :
    mdot (e N) (bgVertexSum (bgCurrent p e) p 0 (N - 1)) = mdot (e 0) (bgVertexSum (bgCurrent p e) p 1 N) := by
  set J := bgCurrent p e with hJ
  set P := momRange p with hP
  set VS := bgVertexSum J p with hVS
  have hswap : ∀ F : ℕ → ℕ → ℂ, ∑ d ∈ Finset.Ico 0 N, ∑ c ∈ Finset.Ico 0 d, F c d =
      ∑ c ∈ Finset.Ico 0 N, ∑ d ∈ Finset.Ico (c + 1) N, F c d := by
    intro F
    exact Finset.sum_comm' fun d c => by simp only [Finset.mem_Ico]; omega
  have hswap' : ∀ (c : ℕ) (G : ℕ → ℕ → ℂ), ∑ d ∈ Finset.Ico (c + 1) N, ∑ e ∈ Finset.Ico (c + 1) d, G e d =
      ∑ e ∈ Finset.Ico (c + 1) N, ∑ d ∈ Finset.Ico (e + 1) N, G e d := by
    intro c G
    exact Finset.sum_comm' fun d e => by simp only [Finset.mem_Ico]; omega
  have hconsP : ∀ c f, c < f → f < N → P (f + 1) N = -(P 0 c + P (c + 1) f) := by
    intro c f hcf hfN
    have h1 := momRange_split p (a := 0) (c := c) (b := N) (Nat.zero_le c) (by omega)
    have h2 := momRange_split p (a := c + 1) (c := f) (b := N) (by omega) hfN
    have : P 0 N = P 0 c + P (c + 1) f + P (f + 1) N := by simp only [hP]; rw [h1, h2, add_assoc]
    rw [hcons] at this
    simp only [hP] at this ⊢
    linear_combination -this
  -- counting the path vertices by the line on the left and by the line on the right
  have hcount : ∑ c ∈ Finset.Ico 0 N, mdot (J 0 c) (VS (c + 1) N) =
      ∑ d ∈ Finset.Ico 0 N, mdot (VS 0 d) (J (d + 1) N) := by
    simp only [hVS, bgVertexSum, mdot_add_right, mdot_add_left, mdot_sum_right, mdot_sum_left,
      Finset.sum_add_distrib]
    rw [hswap, hswap]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun f hf => ?_
      have hf := Finset.mem_Ico.1 hf
      have hc := Finset.mem_Ico.1 hc
      show mdot (J 0 c) (vertex3 (J (c + 1) f) (P (c + 1) f) (J (f + 1) N) (P (f + 1) N)) =
        mdot (vertex3 (J 0 c) (P 0 c) (J (c + 1) f) (P (c + 1) f)) (J (f + 1) N)
      rw [hconsP c f (by omega) hf.2]
      exact mdot_vertex3_cyc _ _ _ _ _
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [hswap' c fun e d => mdot (vertex4 (J 0 c) (J (c + 1) e) (J (e + 1) d)) (J (d + 1) N)]
      refine Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl fun g hg => ?_
      exact mdot_vertex4_cyc _ _ _ _
  -- the terms of the two counts
  have hsym : ∀ c, 1 ≤ c → c + 2 ≤ N →
      mdot (P (c + 1) N) (P (c + 1) N) = mdot (P 0 c) (P 0 c) := by
    intro c h1 h2
    have h := momRange_split p (a := 0) (c := c) (b := N) (Nat.zero_le c) (by omega)
    have : P (c + 1) N = -P 0 c := by
      have hc' : momRange p 0 N = 0 := hcons
      simp only [hP]; rw [h] at hc'; exact eq_neg_of_add_eq_zero_right hc'
    rw [this, mdot_neg_left, mdot_neg_right, neg_neg]
  have hS : ∀ c d, c < d → mdot (P c d) (P c d) ≠ 0 → mdot (P c d) (P c d) • J c d = VS c d := by
    intro c d hcd hs
    show mdot (momRange p c d) (momRange p c d) • bgCurrent p e c d = bgVertexSum (bgCurrent p e) p c d
    rw [bgCurrent_of_lt p e hcd, smul_smul, mul_one_div_cancel hs, one_smul]
  have hJ00 : J 0 0 = e 0 := bgCurrent_self p e 0
  have hJNN : J N N = e N := bgCurrent_self p e N
  have hVNN : VS N N = 0 := by simp [hVS, bgVertexSum]
  have hV00 : VS 0 0 = 0 := by simp [hVS, bgVertexSum]
  have htop : ∀ F : ℕ → ℂ, ∑ c ∈ Finset.Ico 1 N, F c = ∑ c ∈ Finset.Ico 1 (N - 1), F c + F (N - 1) := by
    intro F
    have h := Finset.sum_Ico_succ_top (a := 1) (b := N - 1) (by omega) F
    rwa [show N - 1 + 1 = N by omega] at h
  have htop0 : ∀ F : ℕ → ℂ, ∑ c ∈ Finset.Ico 0 N, F c = ∑ c ∈ Finset.Ico 0 (N - 1), F c + F (N - 1) := by
    intro F
    have h := Finset.sum_Ico_succ_top (a := 0) (b := N - 1) (by omega) F
    rwa [show N - 1 + 1 = N by omega] at h
  have hleft : ∑ c ∈ Finset.Ico 0 N, mdot (J 0 c) (VS (c + 1) N) =
      mdot (e 0) (VS 1 N) + ∑ c ∈ Finset.Ico 1 (N - 1), mdot (P 0 c) (P 0 c) * mdot (J 0 c) (J (c + 1) N) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N), htop, show N - 1 + 1 = N by omega, hVNN,
      mdot_zero_right, add_zero, hJ00]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    rw [← hS (c + 1) N (by omega) (by rw [hsym c hc.1 (by omega)]; exact hprop c hc.1 (by omega)),
      mdot_smul_right, hsym c hc.1 (by omega)]
  have hright : ∑ d ∈ Finset.Ico 0 N, mdot (VS 0 d) (J (d + 1) N) =
      mdot (e N) (VS 0 (N - 1)) + ∑ c ∈ Finset.Ico 1 (N - 1), mdot (P 0 c) (P 0 c) * mdot (J 0 c) (J (c + 1) N) := by
    rw [htop0, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N - 1), show N - 1 + 1 = N by omega, hV00,
      mdot_zero_left, zero_add, hJNN, mdot_comm (VS 0 (N - 1)) (e N), add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    rw [← hS 0 c (by omega) (hprop c hc.1 (by omega)), mdot_smul_left]
  have := hcount
  rw [hleft, hright] at this
  linear_combination -this

end Cyclic

/-- The labels rotated by one: gluon `t + 1` becomes `t`, and gluon `0` becomes the last gluon `N` (labels beyond `N`
are kept). -/
def rotLabels {X : Type*} (f : ℕ → X) (N : ℕ) : ℕ → X :=
  fun t => if t < N then f (t + 1) else if t = N then f 0 else f t

lemma momRange_rotLabels (p : ℕ → Fin 4 → ℂ) {N c d : ℕ} (hd : d < N) :
    momRange (rotLabels p N) c d = momRange p (c + 1) (d + 1) := by
  rw [← momRange_shift]
  exact momRange_congr fun t _ ht => by simp [rotLabels, show t < N by omega]

lemma momRange_rotLabels_total (p : ℕ → Fin 4 → ℂ) (N : ℕ) :
    momRange (rotLabels p N) 0 N = momRange p 0 N := by
  unfold momRange
  rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)]
  have h1 : ∑ t ∈ Finset.Ico 0 N, rotLabels p N t = ∑ t ∈ Finset.Ico (0 + 1) (N + 1), p t := by
    rw [← Finset.sum_Ico_add' (fun t => p t) 0 N 1]
    exact Finset.sum_congr rfl fun t ht => by simp [rotLabels, (Finset.mem_Ico.1 ht).2]
  rw [h1]
  simp [rotLabels]
  abel

/-- **Cyclic invariance of the colour-ordered Feynman amplitude** (Elvang-Huang p. 25, property 1): for conserved
momenta and nonvanishing channel propagators, rotating the labels by one does not change the planar sum. -/
theorem bgAmplitude_rotLabels (m : ℕ) (p e : ℕ → Fin 4 → ℂ) (hcons : momRange p 0 (m + 2) = 0)
    (hprop : ∀ d, 1 ≤ d → d ≤ m → mdot (momRange p 0 d) (momRange p 0 d) ≠ 0) :
    bgAmplitude m (rotLabels p (m + 2)) (rotLabels e (m + 2)) = bgAmplitude m p e := by
  have key := mdot_bgVertexSum_rotate p e (m + 2) (by omega) hcons fun d h1 h2 => hprop d h1 (by omega)
  rw [show m + 2 - 1 = m + 1 by omega] at key
  have he0 : rotLabels e (m + 2) (m + 2) = e 0 := by simp [rotLabels]
  rw [bgAmplitude, bgAmplitude, key, he0]
  congr 1
  rw [show (1 : ℕ) = 0 + 1 from rfl, show m + 2 = m + 1 + 1 from rfl, ← bgVertexSum_shift]
  refine bgVertexSum_congr' (fun t _ ht => by simp [rotLabels, show t < m + 2 by omega])
    fun c d _ h2 h3 _ => ?_
  rw [← bgCurrent_shift p e 1 (d - c) c d rfl]
  exact bgCurrent_congr (d - c) c d rfl h2 fun t _ ht =>
    ⟨by simp [rotLabels, show t < m + 2 by omega], by simp [rotLabels, show t < m + 2 by omega]⟩

/-- The rotated position of the gluon `j`. -/
def rotPos (N j : ℕ) : ℕ := if j = 0 then N else j - 1

lemma rotLabels_update {X : Type*} (f : ℕ → X) {N j : ℕ} (hj : j ≤ N) (v : X) :
    rotLabels (Function.update f j v) N = Function.update (rotLabels f N) (rotPos N j) v := by
  funext t
  simp only [rotLabels, rotPos, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A Ward identity at the rotated position gives the Ward identity at the gluon. -/
theorem wardIdentity_of_rotPos (m : ℕ) {j : ℕ} (hj : j ≤ m + 2) (h : WardIdentity m (rotPos (m + 2) j)) :
    WardIdentity m j := by
  intro p e hnull hcons hprop htr
  have hprop0 : ∀ d, 1 ≤ d → d ≤ m → mdot (momRange p 0 d) (momRange p 0 d) ≠ 0 :=
    fun d h1 h2 => hprop 0 d (by omega) (by omega) (by omega)
  rw [← bgAmplitude_rotLabels m p _ hcons hprop0, rotLabels_update _ hj]
  have hpj : p j = rotLabels p (m + 2) (rotPos (m + 2) j) := by
    unfold rotLabels rotPos
    by_cases hj0 : j = 0
    · subst hj0; simp
    · simp only [hj0, ↓reduceIte, show j - 1 < m + 2 by omega]
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0)]
  rw [hpj]
  refine h _ _ ?_ ?_ ?_ ?_
  · intro t ht
    unfold rotLabels
    split_ifs with h1 h2
    · exact hnull _ (by omega)
    · exact hnull 0 (by omega)
    · exact hnull t ht
  · rw [momRange_rotLabels_total]; exact hcons
  · intro c d h1 h2 h3
    rw [momRange_rotLabels p (by omega : d < m + 2)]
    rcases Nat.lt_or_ge d (m + 1) with hd | hd
    · exact hprop _ _ (by omega) (by omega) (by omega)
    · have hc : 1 ≤ c := by omega
      have hsplit := momRange_split p (a := 0) (c := c) (b := m + 2) (Nat.zero_le c) (by omega)
      have hneg : momRange p (c + 1) (d + 1) = -momRange p 0 c := by
        rw [show d + 1 = m + 2 by omega]
        rw [hsplit] at hcons
        exact eq_neg_of_add_eq_zero_right hcons
      rw [hneg, mdot_neg_left, mdot_neg_right, neg_neg]
      exact hprop 0 c hc (by omega) (by omega)
  · intro t ht htj
    unfold rotLabels
    split_ifs with h1 h2
    · refine htr _ (by omega) fun hje => htj ?_
      unfold rotPos
      split_ifs with hj0 <;> omega
    · refine htr 0 (by omega) fun hje => htj ?_
      unfold rotPos
      simp only [← hje, ↓reduceIte]
      omega
    · exact absurd ht (by omega)

/-- **The Ward identity at every gluon, for every number of gluons** (Elvang-Huang p. 17): from the Ward identity at
the last gluon (`ward_last`) and cyclic invariance (`bgAmplitude_rotLabels`). -/
theorem ward_all (m : ℕ) : ∀ j ≤ m + 2, WardIdentity m j := by
  have h0 : WardIdentity m 0 := wardIdentity_of_rotPos m (by omega) (by simpa [rotPos] using ward_last m)
  intro j
  induction j with
  | zero => exact fun _ => h0
  | succ j ih =>
    intro hj
    exact wardIdentity_of_rotPos m hj (by simpa [rotPos] using ih (by omega))


/-! ### The factorization and the recursion without the Ward hypotheses -/

/-- **Elvang-Huang (3.5) on the pole, with the Ward identities proved** (`ward_all`): the merged amplitude with the
amputated current of the channel is `Σ_h A_L(…, −P^{−h}) A_R(P^h, …)`. -/
theorem residue_factorization' (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i < j) (hj : j ≤ m + 1)
    (hk : j - i ≤ m) (lP ltP lq ltq : Fin 2 → ℂ) (hP : momRange p i j = nullMom lP ltP)
    (hq1 : angleBr ltq ltP ≠ 0) (hq2 : squareBr lq lP ≠ 0)
    (hnull : ∀ t ≤ m + 2, mdot (p t) (p t) = 0) (hcons : momRange p 0 (m + 2) = 0)
    (htr : ∀ t ≤ m + 2, mdot (e t) (p t) = 0)
    (hother : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) → ¬ (c = i ∧ d = j) →
      mdot (momRange p c d) (momRange p c d) ≠ 0) :
    bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j))
        (collapse e i j (bgVertexSum (bgCurrent p e) p i j)) =
      bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsMinus lP (-ltP) lq)) *
          bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsPlus lP ltP ltq)) +
        bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsPlus lP (-ltP) ltq)) *
          bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsMinus lP ltP lq)) :=
  residue_factorization m p e hij hj hk lP ltP lq ltq hP hq1 hq2 hnull hcons htr hother
    (ward_all _ _ (by omega)) (ward_all _ _ (by omega))

/-- **The on-shell recursion (3.7) for the colour-ordered Feynman amplitudes, with the Ward identities proved**
(`ward_all`); the large-`z` falloff (3.6) remains the input under which Elvang-Huang state it (p. 36). -/
theorem bgAmplitude_eq_sum_channels' (m : ℕ) (p e : ℂ → ℕ → Fin 4 → ℂ)
    (hp : ∀ t, Differentiable ℂ fun z => p z t) (he : ∀ t, Differentiable ℂ fun z => e z t)
    (C : Finset (ℕ × ℕ)) (hC : ∀ x ∈ C, x.1 < x.2 ∧ x.2 ≤ m + 1 ∧ ¬ (x.1 = 0 ∧ x.2 = m + 1))
    (s zI : ℕ × ℕ → ℂ) (hs : ∀ x ∈ C, s x ≠ 0)
    (hlin : ∀ x ∈ C, ∀ z, mdot (momRange (p z) x.1 x.2) (momRange (p z) x.1 x.2) =
      mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) + z * s x)
    (hP0 : ∀ x ∈ C, mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) ≠ 0)
    (hzI : ∀ x ∈ C, mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) + zI x * s x = 0)
    (hinj : ∀ x ∈ C, ∀ y ∈ C, zI x = zI y → x = y)
    (hfix : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) → (c, d) ∉ C → ∀ z,
      mdot (momRange (p z) c d) (momRange (p z) c d) ≠ 0)
    (hinf : LargeZFalloff m p e)
    (lP ltP lq ltq : ℕ × ℕ → Fin 2 → ℂ)
    (hP : ∀ x ∈ C, momRange (p (zI x)) x.1 x.2 = nullMom (lP x) (ltP x))
    (hq1 : ∀ x ∈ C, angleBr (ltq x) (ltP x) ≠ 0) (hq2 : ∀ x ∈ C, squareBr (lq x) (lP x) ≠ 0)
    (hnull : ∀ x ∈ C, ∀ t ≤ m + 2, mdot (p (zI x) t) (p (zI x) t) = 0)
    (hcons : ∀ x ∈ C, momRange (p (zI x)) 0 (m + 2) = 0)
    (htr : ∀ x ∈ C, ∀ t ≤ m + 2, mdot (e (zI x) t) (p (zI x) t) = 0) :
    bgAmplitude m (p 0) (e 0) = ∑ x ∈ C,
      (1 / mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2)) *
        channelTerm m (p (zI x)) (e (zI x)) x.1 x.2 (lP x) (ltP x) (lq x) (ltq x) :=
  bgAmplitude_eq_sum_channels m p e hp he C hC s zI hs hlin hP0 hzI hinj hfix hinf lP ltP lq ltq hP hq1 hq2
    hnull hcons htr fun m' _ j hj => ward_all m' j hj

end Lightlike.SpinorHelicity
