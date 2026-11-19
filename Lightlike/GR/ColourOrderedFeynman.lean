import Lightlike.GR.Polarization

/-!
# Colour-ordered gluon tree amplitudes from the Feynman rules

Elvang-Huang p. 22 give the colour-ordered Feynman rules of Yang-Mills theory in Gervais-Neveu gauge: the
three-gluon vertex `V^{μ₁μ₂μ₃} = −√2 (η^{μ₁μ₂} p₁^{μ₃} + η^{μ₂μ₃} p₂^{μ₁} + η^{μ₃μ₁} p₃^{μ₂})` (`vertex3`), the
four-gluon vertex `V^{μ₁μ₂μ₃μ₄} = η^{μ₁μ₃} η^{μ₂μ₄}` (`vertex4`), the propagator `η_{μν}/p²` (p. 21), and the
colour-ordered amplitude `A_n[1 2 ⋯ n]` is the sum of the planar diagrams ("diagrams with no lines crossing and the
ordering of the external lines fixed"), with the polarization vectors (2.49)–(2.50) on the external lines.

Here the planar sum is organized as the recursion over consecutive intervals of gluons (`bgCurrent`): the current
of the gluons `a, …, b` is the propagator `1/P²` times the sum over the ways of joining two (three) consecutive
sub-currents at a three-gluon (four-gluon) vertex (`bgVertexSum`), and the amplitude is the last polarization
dotted into the amputated current of the other gluons (`bgAmplitude`).

* `bgCurrent_of_lt`: the recursion.
* `bgAmplitude_three`: the three-gluon amplitude is the vertex rule (Elvang-Huang (2.72)).
* `WardIdentity`, `ward_three`: the on-shell Ward identity `p_μ A^μ = 0` (Elvang-Huang p. 17), and its proof for three
  gluons at each leg.

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §2.5: the gauge-fixed Lagrangian (2.64) and the
  propagator, p. 21; the colour-ordered vertex rules and the planar diagrams, p. 22; the three-gluon amplitude
  (2.72), p. 23; the Ward identity, p. 17.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-! ### Bilinearity of the Minkowski product -/

lemma mdot_comm (u v : Fin 4 → ℂ) : mdot u v = mdot v u := by simp only [mdot]; ring

@[simp] lemma mdot_add_left (u v w : Fin 4 → ℂ) : mdot (u + v) w = mdot u w + mdot v w := by
  simp only [mdot, Pi.add_apply]; ring

@[simp] lemma mdot_add_right (u v w : Fin 4 → ℂ) : mdot u (v + w) = mdot u v + mdot u w := by
  simp only [mdot, Pi.add_apply]; ring

@[simp] lemma mdot_smul_left (c : ℂ) (u v : Fin 4 → ℂ) : mdot (c • u) v = c * mdot u v := by
  simp only [mdot, Pi.smul_apply, smul_eq_mul]; ring

@[simp] lemma mdot_smul_right (c : ℂ) (u v : Fin 4 → ℂ) : mdot u (c • v) = c * mdot u v := by
  simp only [mdot, Pi.smul_apply, smul_eq_mul]; ring

@[simp] lemma mdot_neg_left (u v : Fin 4 → ℂ) : mdot (-u) v = -mdot u v := by
  simp only [mdot, Pi.neg_apply]; ring

@[simp] lemma mdot_neg_right (u v : Fin 4 → ℂ) : mdot u (-v) = -mdot u v := by
  simp only [mdot, Pi.neg_apply]; ring

@[simp] lemma mdot_sub_left (u v w : Fin 4 → ℂ) : mdot (u - v) w = mdot u w - mdot v w := by
  simp only [mdot, Pi.sub_apply]; ring

@[simp] lemma mdot_sub_right (u v w : Fin 4 → ℂ) : mdot u (v - w) = mdot u v - mdot u w := by
  simp only [mdot, Pi.sub_apply]; ring

@[simp] lemma mdot_zero_left (v : Fin 4 → ℂ) : mdot 0 v = 0 := by simp [mdot]

@[simp] lemma mdot_zero_right (u : Fin 4 → ℂ) : mdot u 0 = 0 := by simp [mdot]

lemma mdot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin 4 → ℂ) (v : Fin 4 → ℂ) :
    mdot (∑ i ∈ s, f i) v = ∑ i ∈ s, mdot (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mdot_add_left, ih]

lemma mdot_sum_right {ι : Type*} (s : Finset ι) (u : Fin 4 → ℂ) (f : ι → Fin 4 → ℂ) :
    mdot u (∑ i ∈ s, f i) = ∑ i ∈ s, mdot u (f i) := by
  rw [mdot_comm, mdot_sum_left]; simp only [mdot_comm u]

/-! ### The colour-ordered Feynman rules and the planar currents -/

/-- The colour-ordered three-gluon vertex (Elvang-Huang p. 22) with the legs `(a, pa)`, `(b, pb)` and the open leg of
outgoing momentum `p₃ = −(pa + pb)`: `−√2 [(a·b) pa^μ + (a·pb) b^μ + (b·p₃) a^μ]`. -/
def vertex3 (a pa b pb : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (-((Real.sqrt 2 : ℝ) : ℂ)) • (mdot a b • pa + mdot a pb • b + mdot b (-(pa + pb)) • a)

/-- The colour-ordered four-gluon vertex (Elvang-Huang p. 22) with three legs and the open leg: `(a·c) b^μ`. -/
def vertex4 (a b c : Fin 4 → ℂ) : Fin 4 → ℂ := mdot a c • b

/-- The momentum `P = p_a + ⋯ + p_b` of the gluons `a, …, b`. -/
def momRange (p : ℕ → Fin 4 → ℂ) (a b : ℕ) : Fin 4 → ℂ := ∑ t ∈ Finset.Ico a (b + 1), p t

/-- The sum over the planar vertices joining consecutive sub-currents of the gluons `a, …, b` (the amputated
current), for a table `T a b` of currents: `[a, c] [c+1, b]` at a three-gluon vertex, `[a, c] [c+1, d] [d+1, b]` at a
four-gluon vertex. -/
def bgVertexSum (T : ℕ → ℕ → Fin 4 → ℂ) (p : ℕ → Fin 4 → ℂ) (a b : ℕ) : Fin 4 → ℂ :=
  (∑ c ∈ Finset.Ico a b, vertex3 (T a c) (momRange p a c) (T (c + 1) b) (momRange p (c + 1) b)) +
    ∑ c ∈ Finset.Ico a b, ∑ d ∈ Finset.Ico (c + 1) b, vertex4 (T a c) (T (c + 1) d) (T (d + 1) b)

/-- The table of the currents of the intervals of length at most `L + 1`. -/
def bgTable (p e : ℕ → Fin 4 → ℂ) : ℕ → ℕ → ℕ → Fin 4 → ℂ
  | 0, a, _ => e a
  | L + 1, a, b =>
    if b - a ≤ L then bgTable p e L a b
    else (1 / mdot (momRange p a b) (momRange p a b)) • bgVertexSum (bgTable p e L) p a b

/-- **The colour-ordered current** of the gluons `a, …, b` with momenta `p` and polarizations `e`: the sum of the
planar diagrams with one off-shell leg (the Feynman rules of Elvang-Huang p. 22, with the propagator `η_{μν}/P²`). -/
def bgCurrent (p e : ℕ → Fin 4 → ℂ) (a b : ℕ) : Fin 4 → ℂ := bgTable p e (b - a) a b

lemma bgTable_eq (p e : ℕ → Fin 4 → ℂ) : ∀ L a b, b - a ≤ L → bgTable p e L a b = bgCurrent p e a b
  | 0, a, b, h => by
    rw [bgCurrent, show b - a = 0 by omega]
  | L + 1, a, b, h => by
    rcases Nat.lt_or_ge (b - a) (L + 1) with h' | h'
    · rw [bgTable]
      simp only [show b - a ≤ L by omega, ↓reduceIte]
      exact bgTable_eq p e L a b (by omega)
    · rw [bgCurrent, show b - a = L + 1 by omega]

@[simp] lemma bgCurrent_self (p e : ℕ → Fin 4 → ℂ) (a : ℕ) : bgCurrent p e a a = e a := by
  simp [bgCurrent, bgTable]

lemma bgVertexSum_congr {T T' : ℕ → ℕ → Fin 4 → ℂ} (p : ℕ → Fin 4 → ℂ) (a b : ℕ)
    (h : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a → T c d = T' c d) :
    bgVertexSum T p a b = bgVertexSum T' p a b := by
  unfold bgVertexSum
  congr 1
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    rw [h a c le_rfl hc.1 (by omega) (by omega), h (c + 1) b (by omega) (by omega) le_rfl (by omega)]
  · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    have hc := Finset.mem_Ico.1 hc
    have hd := Finset.mem_Ico.1 hd
    rw [h a c le_rfl hc.1 (by omega) (by omega), h (c + 1) d (by omega) (by omega) (by omega) (by omega),
      h (d + 1) b (by omega) (by omega) le_rfl (by omega)]

/-- **The recursion** of the colour-ordered currents: for `a < b`,
`J(a, …, b) = (1/P²) Σ (planar vertices of sub-currents)`. -/
theorem bgCurrent_of_lt (p e : ℕ → Fin 4 → ℂ) {a b : ℕ} (hab : a < b) :
    bgCurrent p e a b =
      (1 / mdot (momRange p a b) (momRange p a b)) • bgVertexSum (bgCurrent p e) p a b := by
  obtain ⟨L, hL⟩ : ∃ L, b - a = L + 1 := ⟨b - a - 1, by omega⟩
  rw [bgCurrent, hL, bgTable]
  simp only [show ¬ (b - a ≤ L) by omega, ↓reduceIte]
  congr 1
  exact bgVertexSum_congr p a b fun c d _ _ _ hcd => bgTable_eq p e L c d (by omega)

/-- **The colour-ordered amplitude** `A_n[1 2 ⋯ n]` of `n = m + 3` gluons (Elvang-Huang p. 22): the polarization of
the last gluon dotted into the amputated current of the others. -/
def bgAmplitude (m : ℕ) (p e : ℕ → Fin 4 → ℂ) : ℂ :=
  mdot (e (m + 2)) (bgVertexSum (bgCurrent p e) p 0 (m + 1))

/-- **The three-gluon amplitude** is the vertex rule (Elvang-Huang (2.72)):
`A₃[1 2 3] = −√2 [(ε₁·ε₂)(ε₃·p₁) + (ε₂·ε₃)(ε₁·p₂) + (ε₃·ε₁)(ε₂·p₃)]` with `p₃ = −(p₁ + p₂)`. -/
theorem bgAmplitude_three (p e : ℕ → Fin 4 → ℂ) :
    bgAmplitude 0 p e = -((Real.sqrt 2 : ℝ) : ℂ) * (mdot (e 0) (e 1) * mdot (e 2) (p 0) +
      mdot (e 1) (e 2) * mdot (e 0) (p 1) + mdot (e 2) (e 0) * mdot (e 1) (-(p 0 + p 1))) := by
  have hv : bgVertexSum (bgCurrent p e) p 0 1 = vertex3 (e 0) (p 0) (e 1) (p 1) := by
    simp [bgVertexSum, momRange]
  rw [bgAmplitude, hv, vertex3]
  simp only [mdot_smul_right, mdot_add_right]
  rw [mdot_comm (e 2) (e 0), mdot_comm (e 2) (e 1)]
  ring

/-- **The on-shell Ward identity** `p_μ A^μ_n = 0` (Elvang-Huang p. 17, after (2.50)) for `n = m + 3` gluons at the
leg `j`: for null momenta with `Σ p = 0` and transverse polarizations of the other legs, replacing the polarization
of the leg `j` by its momentum gives zero. Elvang-Huang state it as an input ("as encoded in the familiar Ward
identity"); it is a hypothesis of the factorization theorems. -/
def WardIdentity (m j : ℕ) : Prop :=
  ∀ p e : ℕ → Fin 4 → ℂ, (∀ t ≤ m + 2, mdot (p t) (p t) = 0) → momRange p 0 (m + 2) = 0 →
    (∀ t ≤ m + 2, t ≠ j → mdot (e t) (p t) = 0) → bgAmplitude m p (Function.update e j (p j)) = 0

/-- **The Ward identity for three gluons**, at each leg. -/
theorem ward_three {j : ℕ} (hj : j ≤ 2) : WardIdentity 0 j := by
  intro p e hnull hcons htr
  have h0 := hnull 0 (by omega)
  have h1 := hnull 1 (by omega)
  have hp2 : p 2 = -(p 0 + p 1) := by
    have : momRange p 0 2 = p 0 + p 1 + p 2 := by
      simp [momRange, Finset.sum_range_succ]
    rw [this] at hcons
    rw [← sub_eq_zero, sub_neg_eq_add]; rw [← hcons]; abel
  have h2 := hnull 2 (by omega)
  rw [hp2] at h2
  rw [bgAmplitude_three]
  interval_cases j
  · have he1 := htr 1 (by omega) (by omega)
    have he2 := htr 2 (by omega) (by omega)
    rw [hp2] at he2
    simp only [Function.update_self, Function.update_of_ne (show (1 : ℕ) ≠ 0 by omega),
      Function.update_of_ne (show (2 : ℕ) ≠ 0 by omega)]
    linear_combination (norm := (simp only [mdot, Pi.add_apply, Pi.neg_apply]; ring))
      (-((Real.sqrt 2 : ℝ) : ℂ)) * ((mdot (e 1) (e 2) / 2) * (h2 - h0 - h1) - mdot (e 2) (p 0) * he1)
  · have he0 := htr 0 (by omega) (by omega)
    have he2 := htr 2 (by omega) (by omega)
    rw [hp2] at he2
    simp only [Function.update_self, Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega),
      Function.update_of_ne (show (2 : ℕ) ≠ 1 by omega)]
    linear_combination (norm := (simp only [mdot, Pi.add_apply, Pi.neg_apply]; ring))
      (-((Real.sqrt 2 : ℝ) : ℂ)) * (-(mdot (e 0) (p 1)) * he2 - (mdot (e 2) (e 0) / 2) * (h2 - h0 + h1))
  · have he0 := htr 0 (by omega) (by omega)
    have he1 := htr 1 (by omega) (by omega)
    simp only [Function.update_self, Function.update_of_ne (show (0 : ℕ) ≠ 2 by omega),
      Function.update_of_ne (show (1 : ℕ) ≠ 2 by omega)]
    rw [hp2]
    linear_combination (norm := (simp only [mdot, Pi.add_apply, Pi.neg_apply]; ring))
      (-((Real.sqrt 2 : ℝ) : ℂ)) * ((mdot (e 0) (e 1) / 2) * (h1 - h0 - h2) +
        (mdot (e 1) (p 0) + mdot (e 1) (p 1)) * he0)

end Lightlike.SpinorHelicity
