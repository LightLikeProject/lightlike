import Lightlike.GR.ColourOrderedFeynman

/-!
# Factorization of the colour-ordered Feynman amplitudes on planar poles

For the colour-ordered gluon amplitudes of `ColourOrderedFeynman.lean` (the planar sum of the Feynman diagrams of
Elvang-Huang p. 22) and a planar channel `I = {i, …, j}` with momentum `P = p_i + ⋯ + p_j`:

* `bgAmplitude_split`: **the amplitude is affine in the propagator `1/P²`**,
  `A_n = A_n^{(no I)} + (1/P²) A_R(V_I)`, where `A_n^{(no I)}` is the planar sum without the diagrams of the
  channel `I`, `V_I` is the amputated current of the gluons in `I`, and `A_R(v)` is the amplitude of the other gluons
  and one merged gluon of momentum `P` and polarization `v` (every planar diagram contains the propagator of `I` at
  most once, and the diagrams that contain it are the diagrams of the merged amplitude);
* `residue_factorization`: **on the pole** (`P² = 0`), with the Ward identity of the two lower-point amplitudes as
  the input that Elvang-Huang state (p. 17), the completeness relation of the polarization vectors turns
  `A_R(V_I)` into `Σ_h A_L(…, −P^{−h}) A_R(P^h, …)`, the factorization (3.5).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: the colour-ordered Feynman rules, p. 22; the Ward
  identity, p. 17; the factorization of the residues (3.5), p. 35; the spinors of `−p` (3.14)–(3.15), p. 38.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-! ### Linearity of the vertices -/

lemma vertex3_sub_left (a a' pa b pb : Fin 4 → ℂ) :
    vertex3 a pa b pb - vertex3 a' pa b pb = vertex3 (a - a') pa b pb := by
  funext μ
  simp only [vertex3, mdot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma vertex3_sub_right (a pa b b' pb : Fin 4 → ℂ) :
    vertex3 a pa b pb - vertex3 a pa b' pb = vertex3 a pa (b - b') pb := by
  funext μ
  simp only [vertex3, mdot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma vertex4_sub_one (a a' b c : Fin 4 → ℂ) : vertex4 a b c - vertex4 a' b c = vertex4 (a - a') b c := by
  funext μ
  simp only [vertex4, mdot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma vertex4_sub_two (a b b' c : Fin 4 → ℂ) : vertex4 a b c - vertex4 a b' c = vertex4 a (b - b') c := by
  funext μ
  simp only [vertex4, mdot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma vertex4_sub_three (a b c c' : Fin 4 → ℂ) : vertex4 a b c - vertex4 a b c' = vertex4 a b (c - c') := by
  funext μ
  simp only [vertex4, mdot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma vertex3_lin_left (x y : ℂ) (a a' pa b pb : Fin 4 → ℂ) :
    vertex3 (x • a + y • a') pa b pb = x • vertex3 a pa b pb + y • vertex3 a' pa b pb := by
  funext μ
  simp only [vertex3, mdot, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma vertex3_lin_right (x y : ℂ) (a pa b b' pb : Fin 4 → ℂ) :
    vertex3 a pa (x • b + y • b') pb = x • vertex3 a pa b pb + y • vertex3 a pa b' pb := by
  funext μ
  simp only [vertex3, mdot, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

lemma vertex4_lin_one (x y : ℂ) (a a' b c : Fin 4 → ℂ) :
    vertex4 (x • a + y • a') b c = x • vertex4 a b c + y • vertex4 a' b c := by
  funext μ
  simp only [vertex4, mdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma vertex4_lin_two (x y : ℂ) (a b b' c : Fin 4 → ℂ) :
    vertex4 a (x • b + y • b') c = x • vertex4 a b c + y • vertex4 a b' c := by
  funext μ
  simp only [vertex4, mdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma vertex4_lin_three (x y : ℂ) (a b c c' : Fin 4 → ℂ) :
    vertex4 a b (x • c + y • c') = x • vertex4 a b c + y • vertex4 a b c' := by
  funext μ
  simp only [vertex4, mdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Momenta of intervals -/

lemma momRange_congr {p p' : ℕ → Fin 4 → ℂ} {a b : ℕ} (h : ∀ t, a ≤ t → t ≤ b → p t = p' t) :
    momRange p a b = momRange p' a b :=
  Finset.sum_congr rfl fun t ht => by
    have := Finset.mem_Ico.1 ht
    exact h t this.1 (by omega)

lemma momRange_shift (p : ℕ → Fin 4 → ℂ) (k a b : ℕ) :
    momRange (fun t => p (t + k)) a b = momRange p (a + k) (b + k) := by
  rw [momRange, Finset.sum_Ico_add' (fun t => p t) a (b + 1) k, momRange, show b + 1 + k = b + k + 1 by omega]

/-! ### Congruence and translation of the currents -/

lemma bgVertexSum_congr' {T T' : ℕ → ℕ → Fin 4 → ℂ} {p p' : ℕ → Fin 4 → ℂ} {a b : ℕ}
    (hp : ∀ t, a ≤ t → t ≤ b → p t = p' t)
    (h : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a → T c d = T' c d) :
    bgVertexSum T p a b = bgVertexSum T' p' a b := by
  unfold bgVertexSum
  congr 1
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    rw [h a c le_rfl hc.1 (by omega) (by omega), h (c + 1) b (by omega) (by omega) le_rfl (by omega),
      momRange_congr (p' := p') fun t h1 h2 => hp t h1 (by omega),
      momRange_congr (p := p) (p' := p') (a := c + 1) fun t h1 h2 => hp t (by omega) h2]
  · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    have hc := Finset.mem_Ico.1 hc
    have hd := Finset.mem_Ico.1 hd
    rw [h a c le_rfl hc.1 (by omega) (by omega), h (c + 1) d (by omega) (by omega) (by omega) (by omega),
      h (d + 1) b (by omega) (by omega) le_rfl (by omega)]

/-- The current of `a, …, b` depends only on the momenta and polarizations of these gluons. -/
theorem bgCurrent_congr {p p' e e' : ℕ → Fin 4 → ℂ} :
    ∀ n a b, b - a = n → a ≤ b → (∀ t, a ≤ t → t ≤ b → p t = p' t ∧ e t = e' t) →
      bgCurrent p e a b = bgCurrent p' e' a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab h
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · simp [(h a le_rfl le_rfl).2]
    · rw [bgCurrent_of_lt p e hlt, bgCurrent_of_lt p' e' hlt,
        momRange_congr (p' := p') fun t h1 h2 => (h t h1 h2).1]
      congr 1
      exact bgVertexSum_congr' (fun t h1 h2 => (h t h1 h2).1) fun c d h1 h2 h3 h4 =>
        ih (d - c) (by omega) c d rfl h2 fun t ht1 ht2 => h t (by omega) (by omega)

/-- **Translation**: the currents of the gluons `a + k, …, b + k` are the currents of the translated labels. -/
theorem bgCurrent_shift (p e : ℕ → Fin 4 → ℂ) (k : ℕ) :
    ∀ n a b, b - a = n →
      bgCurrent (fun t => p (t + k)) (fun t => e (t + k)) a b = bgCurrent p e (a + k) (b + k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn
    rcases Nat.lt_or_ge a b with hlt | hge
    · rw [bgCurrent_of_lt _ _ hlt, bgCurrent_of_lt p e (by omega : a + k < b + k), momRange_shift]
      congr 1
      unfold bgVertexSum
      congr 1
      · rw [← Finset.sum_Ico_add']
        refine Finset.sum_congr rfl fun c hc => ?_
        have hc := Finset.mem_Ico.1 hc
        rw [ih (c - a) (by omega) a c rfl, ih (b - (c + 1)) (by omega) (c + 1) b rfl, momRange_shift,
          momRange_shift, show c + 1 + k = c + k + 1 by omega]
      · rw [← Finset.sum_Ico_add']
        refine Finset.sum_congr rfl fun c hc => ?_
        have hc := Finset.mem_Ico.1 hc
        rw [show c + k + 1 = c + 1 + k by omega, ← Finset.sum_Ico_add']
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd := Finset.mem_Ico.1 hd
        rw [ih (c - a) (by omega) a c rfl, ih (d - (c + 1)) (by omega) (c + 1) d rfl,
          ih (b - (d + 1)) (by omega) (d + 1) b rfl, show c + 1 + k = c + k + 1 by omega,
          show d + 1 + k = d + k + 1 by omega]
    · simp only [bgCurrent, show b - a = 0 by omega, show b + k - (a + k) = 0 by omega, bgTable]

/-! ### The currents with the current of one interval replaced -/

/-- The table of the currents in which the current of the interval `[i, j]` is replaced by `v`. -/
def bgTableO (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (v : Fin 4 → ℂ) : ℕ → ℕ → ℕ → Fin 4 → ℂ
  | 0, a, b => if a = i ∧ b = j then v else e a
  | L + 1, a, b =>
    if a = i ∧ b = j then v
    else if b - a ≤ L then bgTableO p e i j v L a b
    else (1 / mdot (momRange p a b) (momRange p a b)) • bgVertexSum (bgTableO p e i j v L) p a b

/-- The currents of the planar diagrams in which the current of the gluons `i, …, j` is replaced by `v`; for `v = 0`
these are the planar diagrams without the propagator of the channel `{i, …, j}`. -/
def bgCurrentO (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (v : Fin 4 → ℂ) (a b : ℕ) : Fin 4 → ℂ :=
  bgTableO p e i j v (b - a) a b

lemma bgTableO_eq (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (v : Fin 4 → ℂ) :
    ∀ L a b, b - a ≤ L → bgTableO p e i j v L a b = bgCurrentO p e i j v a b
  | 0, a, b, h => by
    rw [bgCurrentO, show b - a = 0 by omega]
  | L + 1, a, b, h => by
    rcases Nat.lt_or_ge (b - a) (L + 1) with h' | h'
    · rw [bgTableO]
      by_cases hab : a = i ∧ b = j
      · simp only [hab, and_self, ↓reduceIte]
        rw [bgCurrentO]
        obtain ⟨rfl, rfl⟩ := hab
        cases hL : b - a with
        | zero => simp [bgTableO]
        | succ L' => simp [bgTableO]
      · simp only [hab, ↓reduceIte, show b - a ≤ L by omega]
        exact bgTableO_eq p e i j v L a b (by omega)
    · rw [bgCurrentO, show b - a = L + 1 by omega]

lemma bgCurrentO_override (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (v : Fin 4 → ℂ) :
    bgCurrentO p e i j v i j = v := by
  rw [bgCurrentO]
  cases j - i with
  | zero => simp [bgTableO]
  | succ L => simp [bgTableO]

lemma bgCurrentO_self (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (v : Fin 4 → ℂ) {a : ℕ} (h : ¬ (a = i ∧ a = j)) :
    bgCurrentO p e i j v a a = e a := by
  simp [bgCurrentO, bgTableO, h]

lemma bgCurrentO_of_lt (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (v : Fin 4 → ℂ) {a b : ℕ} (hab : a < b)
    (h : ¬ (a = i ∧ b = j)) :
    bgCurrentO p e i j v a b =
      (1 / mdot (momRange p a b) (momRange p a b)) • bgVertexSum (bgCurrentO p e i j v) p a b := by
  obtain ⟨L, hL⟩ : ∃ L, b - a = L + 1 := ⟨b - a - 1, by omega⟩
  rw [bgCurrentO, hL, bgTableO]
  simp only [h, show ¬ (b - a ≤ L) by omega, ↓reduceIte]
  congr 1
  exact bgVertexSum_congr p a b fun c d _ _ _ hcd => bgTableO_eq p e i j v L c d (by omega)

/-- Away from the intervals that contain `[i, j]` the replacement changes nothing. -/
theorem bgCurrentO_of_not_contains (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (v : Fin 4 → ℂ) :
    ∀ n a b, b - a = n → a ≤ b → ¬ (a ≤ i ∧ j ≤ b) → bgCurrentO p e i j v a b = bgCurrent p e a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab h
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · rw [bgCurrentO_self p e v (by omega), bgCurrent_self]
    · rw [bgCurrentO_of_lt p e v hlt (by omega), bgCurrent_of_lt p e hlt]
      congr 1
      exact bgVertexSum_congr p a b fun c d h1 h2 h3 h4 =>
        ih (d - c) (by omega) c d rfl h2 (by omega)

/-- Replacing the current of `[i, j]` by itself changes nothing. -/
theorem bgCurrentO_current (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i ≤ j) :
    ∀ n a b, b - a = n → a ≤ b → bgCurrentO p e i j (bgCurrent p e i j) a b = bgCurrent p e a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      exact bgCurrentO_override p e a b _
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · rw [bgCurrentO_self p e _ (by omega), bgCurrent_self]
    · rw [bgCurrentO_of_lt p e _ hlt h, bgCurrent_of_lt p e hlt]
      congr 1
      exact bgVertexSum_congr p a b fun c d h1 h2 h3 h4 => ih (d - c) (by omega) c d rfl h2

/-! ### Collapsing the channel `[i, j]` to one gluon -/

/-- The labels with the gluons `i, …, j` replaced by one gluon `x` at the position `i`. -/
def collapse {X : Type*} (f : ℕ → X) (i j : ℕ) (x : X) : ℕ → X :=
  fun t => if t < i then f t else if t = i then x else f (t + (j - i))

lemma collapse_of_lt {X : Type*} (f : ℕ → X) {i j t : ℕ} (x : X) (h : t < i) : collapse f i j x t = f t := by
  simp [collapse, h]

@[simp] lemma collapse_self {X : Type*} (f : ℕ → X) (i j : ℕ) (x : X) : collapse f i j x i = x := by
  simp [collapse]

lemma collapse_of_gt {X : Type*} (f : ℕ → X) {i j t : ℕ} (x : X) (h : i < t) :
    collapse f i j x t = f (t + (j - i)) := by
  simp [collapse, show ¬ t < i by omega, show t ≠ i by omega]

lemma update_collapse {X : Type*} (f : ℕ → X) (i j : ℕ) (x y : X) :
    Function.update (collapse f i j x) i y = collapse f i j y := by
  funext t
  by_cases h : t = i
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [collapse, h]

/-- The momentum of an interval through the merged gluon of momentum `P = p_i + ⋯ + p_j`. -/
lemma momRange_collapse (p : ℕ → Fin 4 → ℂ) {i j a b : ℕ} (hij : i ≤ j) (hai : a ≤ i) (hib : i ≤ b) :
    momRange (collapse p i j (momRange p i j)) a b = momRange p a (b + (j - i)) := by
  generalize hP : momRange p i j = P
  have hR : ∑ t ∈ Finset.Ico (i + 1) (b + 1), collapse p i j P t =
      ∑ t ∈ Finset.Ico (j + 1) (b + (j - i) + 1), p t := by
    rw [show j + 1 = (i + 1) + (j - i) by omega, show b + (j - i) + 1 = (b + 1) + (j - i) by omega,
      ← Finset.sum_Ico_add' (fun t => p t) (i + 1) (b + 1) (j - i)]
    exact Finset.sum_congr rfl fun t ht => collapse_of_gt p _ (by have := Finset.mem_Ico.1 ht; omega)
  have hL : ∑ t ∈ Finset.Ico a i, collapse p i j P t = ∑ t ∈ Finset.Ico a i, p t :=
    Finset.sum_congr rfl fun t ht => collapse_of_lt p _ (Finset.mem_Ico.1 ht).2
  unfold momRange
  rw [← Finset.sum_Ico_consecutive _ hai (by omega : i ≤ b + 1),
    ← Finset.sum_Ico_consecutive _ hai (by omega : i ≤ b + (j - i) + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : i < b + 1), collapse_self, hR, hL,
    ← Finset.sum_Ico_consecutive _ (by omega : i ≤ j + 1) (by omega : j + 1 ≤ b + (j - i) + 1), ← hP,
    momRange, add_assoc]

/-- Left of the merged gluon the currents are unchanged. -/
lemma bgCurrent_collapse_left (p e : ℕ → Fin 4 → ℂ) {i j a b : ℕ} (P v : Fin 4 → ℂ) (hab : a ≤ b)
    (hb : b < i) : bgCurrent (collapse p i j P) (collapse e i j v) a b = bgCurrent p e a b :=
  bgCurrent_congr (b - a) a b rfl hab fun t _ ht =>
    ⟨collapse_of_lt p _ (by omega), collapse_of_lt e _ (by omega)⟩

/-- Right of the merged gluon the currents are those of the gluons `j − i` places further on. -/
lemma bgCurrent_collapse_right (p e : ℕ → Fin 4 → ℂ) {i j a b : ℕ} (P v : Fin 4 → ℂ) (hab : a ≤ b)
    (ha : i < a) :
    bgCurrent (collapse p i j P) (collapse e i j v) a b = bgCurrent p e (a + (j - i)) (b + (j - i)) := by
  rw [← bgCurrent_shift p e (j - i) (b - a) a b rfl]
  exact bgCurrent_congr (b - a) a b rfl hab fun t ht _ =>
    ⟨collapse_of_gt p _ (by omega), collapse_of_gt e _ (by omega)⟩

lemma momRange_collapse_left (p : ℕ → Fin 4 → ℂ) {i j a b : ℕ} (P : Fin 4 → ℂ) (hb : b < i) :
    momRange (collapse p i j P) a b = momRange p a b :=
  momRange_congr fun t _ ht => collapse_of_lt p _ (by omega)

lemma momRange_collapse_right (p : ℕ → Fin 4 → ℂ) {i j a b : ℕ} (P : Fin 4 → ℂ) (ha : i < a) :
    momRange (collapse p i j P) a b = momRange p (a + (j - i)) (b + (j - i)) := by
  rw [← momRange_shift]
  exact momRange_congr fun t ht _ => collapse_of_gt p _ (by omega)

/-! ### The planar sum through the channel `[i, j]` is the sum of the merged diagrams -/

lemma sum_Ico_split3 {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a i j b : ℕ} (hai : a ≤ i) (hij : i ≤ j)
    (hjb : j ≤ b) :
    ∑ c ∈ Finset.Ico a b, f c =
      ∑ c ∈ Finset.Ico a i, f c + ∑ c ∈ Finset.Ico i j, f c + ∑ c ∈ Finset.Ico j b, f c := by
  rw [Finset.sum_Ico_consecutive _ hai hij, Finset.sum_Ico_consecutive _ (hai.trans hij) hjb]

lemma sum_Ico_sub_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    ∑ x ∈ Finset.Ico (m - k) (n - k), f x = ∑ x ∈ Finset.Ico m n, f (x - k) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + k := ⟨m - k, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + k := ⟨n - k, by omega⟩
  rw [Finset.sum_Ico_add_right_sub_eq, Nat.add_sub_cancel, Nat.add_sub_cancel]

lemma sum_Ico_collapsed {M : Type*} [AddCommMonoid M] (g : ℕ → M) {a i j b : ℕ} (hai : a ≤ i) (hij : i ≤ j)
    (hjb : j ≤ b) :
    ∑ c ∈ Finset.Ico a (b - (j - i)), g c =
      ∑ c ∈ Finset.Ico a i, g c + ∑ c ∈ Finset.Ico j b, g (c - (j - i)) := by
  rw [← Finset.sum_Ico_consecutive _ hai (by omega : i ≤ b - (j - i))]
  congr 1
  rw [← sum_Ico_sub_shift g (by omega : j - i ≤ j) hjb, show j - (j - i) = i by omega]

/-- **The collapse of the vertex sums**: if the currents `Tv`, `T0` differ only on the intervals that contain
`[i, j]`, by the currents `J` of the merged labels, then so do their vertex sums. -/
theorem bgVertexSum_collapse {Tv T0 J : ℕ → ℕ → Fin 4 → ℂ} {p p' : ℕ → Fin 4 → ℂ} {a i j b : ℕ}
    (hai : a ≤ i) (hij : i ≤ j) (hjb : j ≤ b)
    (hin : ∀ c d, a ≤ c → c ≤ i → j ≤ d → d ≤ b → d - c < b - a → Tv c d - T0 c d = J c (d - (j - i)))
    (hout : ∀ c d, a ≤ c → c ≤ d → d ≤ b → ¬ (c ≤ i ∧ j ≤ d) → Tv c d = T0 c d)
    (hleft : ∀ c d, a ≤ c → c ≤ d → d < i → J c d = T0 c d)
    (hright : ∀ c d, j < c → c ≤ d → d ≤ b → J (c - (j - i)) (d - (j - i)) = T0 c d)
    (hmL : ∀ c d, d < i → momRange p' c d = momRange p c d)
    (hmM : ∀ c d, c ≤ i → j ≤ d → momRange p' c (d - (j - i)) = momRange p c d)
    (hmR : ∀ c d, j < c → c ≤ d → momRange p' (c - (j - i)) (d - (j - i)) = momRange p c d) :
    bgVertexSum Tv p a b - bgVertexSum T0 p a b = bgVertexSum J p' a (b - (j - i)) := by
  unfold bgVertexSum
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  · -- the three-gluon vertices
    rw [sum_Ico_split3 _ hai hij hjb, sum_Ico_collapsed _ hai hij hjb]
    have hmid : ∑ c ∈ Finset.Ico i j,
        (vertex3 (Tv a c) (momRange p a c) (Tv (c + 1) b) (momRange p (c + 1) b) -
          vertex3 (T0 a c) (momRange p a c) (T0 (c + 1) b) (momRange p (c + 1) b)) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [hout a c le_rfl (by omega) (by omega) (by omega),
        hout (c + 1) b (by omega) (by omega) le_rfl (by omega), sub_self]
    rw [hmid, add_zero]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [hout a c le_rfl hc.1 (by omega) (by omega), vertex3_sub_right,
        hin (c + 1) b (by omega) (by omega) hjb le_rfl (by omega), hleft a c le_rfl hc.1 hc.2,
        hmL a c hc.2, hmM (c + 1) b (by omega) hjb]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [hout (c + 1) b (by omega) (by omega) le_rfl (by omega), vertex3_sub_left,
        hin a c le_rfl hai hc.1 (by omega) (by omega), show c - (j - i) + 1 = c + 1 - (j - i) by omega,
        hright (c + 1) b (by omega) (by omega) le_rfl, hmM a c hai hc.1, hmR (c + 1) b (by omega) (by omega)]
  · -- the four-gluon vertices
    rw [sum_Ico_split3 _ hai hij hjb, sum_Ico_collapsed _ hai hij hjb]
    have hmid : ∑ c ∈ Finset.Ico i j,
        (∑ d ∈ Finset.Ico (c + 1) b, vertex4 (Tv a c) (Tv (c + 1) d) (Tv (d + 1) b) -
          ∑ d ∈ Finset.Ico (c + 1) b, vertex4 (T0 a c) (T0 (c + 1) d) (T0 (d + 1) b)) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd := Finset.mem_Ico.1 hd
      rw [hout a c le_rfl (by omega) (by omega) (by omega),
        hout (c + 1) d (by omega) (by omega) (by omega) (by omega),
        hout (d + 1) b (by omega) (by omega) le_rfl (by omega), sub_self]
    rw [hmid, add_zero]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [← Finset.sum_sub_distrib, sum_Ico_split3 _ (by omega : c + 1 ≤ i) hij hjb,
        sum_Ico_collapsed _ (by omega : c + 1 ≤ i) hij hjb]
      have hmid' : ∑ d ∈ Finset.Ico i j, (vertex4 (Tv a c) (Tv (c + 1) d) (Tv (d + 1) b) -
          vertex4 (T0 a c) (T0 (c + 1) d) (T0 (d + 1) b)) = 0 := by
        refine Finset.sum_eq_zero fun d hd => ?_
        have hd := Finset.mem_Ico.1 hd
        rw [hout a c le_rfl (by omega) (by omega) (by omega),
          hout (c + 1) d (by omega) (by omega) (by omega) (by omega),
          hout (d + 1) b (by omega) (by omega) le_rfl (by omega), sub_self]
      rw [hmid', add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun d hd => ?_
        have hd := Finset.mem_Ico.1 hd
        rw [hout a c le_rfl (by omega) (by omega) (by omega),
          hout (c + 1) d (by omega) (by omega) (by omega) (by omega), vertex4_sub_three,
          hin (d + 1) b (by omega) (by omega) hjb le_rfl (by omega), hleft a c le_rfl (by omega) hc.2,
          hleft (c + 1) d (by omega) (by omega) hd.2]
      · refine Finset.sum_congr rfl fun d hd => ?_
        have hd := Finset.mem_Ico.1 hd
        rw [hout a c le_rfl (by omega) (by omega) (by omega),
          hout (d + 1) b (by omega) (by omega) le_rfl (by omega), vertex4_sub_two,
          hin (c + 1) d (by omega) (by omega) hd.1 (by omega) (by omega), hleft a c le_rfl (by omega) hc.2,
          show d - (j - i) + 1 = d + 1 - (j - i) by omega, hright (d + 1) b (by omega) (by omega) le_rfl]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hc := Finset.mem_Ico.1 hc
      rw [← Finset.sum_sub_distrib, show c - (j - i) + 1 = c + 1 - (j - i) by omega,
        sum_Ico_sub_shift _ (by omega : j - i ≤ c + 1) (by omega : c + 1 ≤ b)]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd := Finset.mem_Ico.1 hd
      rw [hout (c + 1) d (by omega) (by omega) (by omega) (by omega),
        hout (d + 1) b (by omega) (by omega) le_rfl (by omega), vertex4_sub_one,
        hin a c le_rfl hai hc.1 (by omega) (by omega),
        hright (c + 1) d (by omega) (by omega) (by omega),
        show d - (j - i) + 1 = d + 1 - (j - i) by omega, hright (d + 1) b (by omega) (by omega) le_rfl]

/-- **The currents through the channel `[i, j]`**: replacing the current of `[i, j]` by `v` changes the current of an
interval `[a, b] ⊇ [i, j]` by the current of the merged labels, with one gluon of momentum `P = p_i + ⋯ + p_j` and
polarization `v` in place of `i, …, j`. -/
theorem bgCurrentO_collapse (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i ≤ j) (v : Fin 4 → ℂ) :
    ∀ n a b, b - a = n → a ≤ i → j ≤ b →
      bgCurrentO p e i j v a b - bgCurrentO p e i j 0 a b =
        bgCurrent (collapse p i j (momRange p i j)) (collapse e i j v) a (b - (j - i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hai hjb
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [bgCurrentO_override, bgCurrentO_override, sub_zero, show b - (b - a) = a by omega,
        bgCurrent_self, collapse_self]
    have hlt : a < b := by omega
    have hlt' : a < b - (j - i) := by omega
    rw [bgCurrentO_of_lt p e v hlt h, bgCurrentO_of_lt p e 0 hlt h, ← smul_sub,
      bgCurrent_of_lt _ _ hlt', momRange_collapse p hij hai (by omega), show b - (j - i) + (j - i) = b by omega]
    congr 1
    refine bgVertexSum_collapse hai hij hjb (fun c d h1 h2 h3 h4 h5 => ih (d - c) (by omega) c d rfl h2 h3)
      (fun c d h1 h2 h3 h4 => by
        rw [bgCurrentO_of_not_contains p e v (d - c) c d rfl h2 h4,
          bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 h4])
      (fun c d h1 h2 h3 => by
        rw [bgCurrent_collapse_left p e _ _ h2 h3,
          bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 (by omega)])
      (fun c d h1 h2 h3 => by
        rw [bgCurrent_collapse_right p e _ _ (by omega) (by omega), show c - (j - i) + (j - i) = c by omega,
          show d - (j - i) + (j - i) = d by omega,
          bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 (by omega)])
      (fun c d h => momRange_collapse_left p _ h)
      (fun c d h1 h2 => by
        rw [momRange_collapse p hij h1 (by omega), show d - (j - i) + (j - i) = d by omega])
      (fun c d h1 h2 => by
        rw [momRange_collapse_right p _ (by omega), show c - (j - i) + (j - i) = c by omega,
          show d - (j - i) + (j - i) = d by omega])

/-- The planar sum of `n = m + 3` gluons with the current of `[i, j]` replaced by `v`; for `v = 0`, **the planar
diagrams without the propagator of the channel `{i, …, j}`**. -/
def bgAmplitudeO (m : ℕ) (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (v : Fin 4 → ℂ) : ℂ :=
  mdot (e (m + 2)) (bgVertexSum (bgCurrentO p e i j v) p 0 (m + 1))

lemma bgAmplitude_eq_bgAmplitudeO (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i ≤ j) :
    bgAmplitude m p e = bgAmplitudeO m p e i j (bgCurrent p e i j) := by
  rw [bgAmplitude, bgAmplitudeO]
  congr 1
  exact bgVertexSum_congr p 0 (m + 1) fun c d _ h2 _ _ => (bgCurrentO_current p e hij (d - c) c d rfl h2).symm

/-- **The diagrams through the channel `{i, …, j}` are the diagrams of the merged amplitude.** -/
theorem bgAmplitudeO_sub (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1)
    (hk : j - i ≤ m) (v : Fin 4 → ℂ) :
    bgAmplitudeO m p e i j v - bgAmplitudeO m p e i j 0 =
      bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j v) := by
  rw [bgAmplitudeO, bgAmplitudeO, ← mdot_sub_right, bgAmplitude,
    collapse_of_gt e _ (by omega : i < m - (j - i) + 2), show m - (j - i) + 2 + (j - i) = m + 2 by omega,
    show m - (j - i) + 1 = m + 1 - (j - i) by omega]
  congr 1
  refine bgVertexSum_collapse (Nat.zero_le i) hij hj
    (fun c d h1 h2 h3 h4 h5 => bgCurrentO_collapse p e hij v (d - c) c d rfl h2 h3)
    (fun c d h1 h2 h3 h4 => by
      rw [bgCurrentO_of_not_contains p e v (d - c) c d rfl h2 h4,
        bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 h4])
    (fun c d h1 h2 h3 => by
      rw [bgCurrent_collapse_left p e _ _ h2 h3,
        bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 (by omega)])
    (fun c d h1 h2 h3 => by
      rw [bgCurrent_collapse_right p e _ _ (by omega) (by omega), show c - (j - i) + (j - i) = c by omega,
        show d - (j - i) + (j - i) = d by omega,
        bgCurrentO_of_not_contains p e 0 (d - c) c d rfl h2 (by omega)])
    (fun c d h => momRange_collapse_left p _ h)
    (fun c d h1 h2 => by
      rw [momRange_collapse p hij h1 (by omega), show d - (j - i) + (j - i) = d by omega])
    (fun c d h1 h2 => by
      rw [momRange_collapse_right p _ (by omega), show c - (j - i) + (j - i) = c by omega,
        show d - (j - i) + (j - i) = d by omega])

/-! ### Linearity in the polarization of one gluon -/

lemma bgVertexSum_lin {T Tv Tw : ℕ → ℕ → Fin 4 → ℂ} (p : ℕ → Fin 4 → ℂ) {a i b : ℕ} (x y : ℂ)
    (hin : ∀ c d, a ≤ c → c ≤ i → i ≤ d → d ≤ b → d - c < b - a → T c d = x • Tv c d + y • Tw c d)
    (hout : ∀ c d, a ≤ c → c ≤ d → d ≤ b → ¬ (c ≤ i ∧ i ≤ d) → T c d = Tv c d ∧ Tw c d = Tv c d)
    (hai : a ≤ i) (hib : i ≤ b) :
    bgVertexSum T p a b = x • bgVertexSum Tv p a b + y • bgVertexSum Tw p a b := by
  unfold bgVertexSum
  rw [smul_add, smul_add, add_add_add_comm]
  congr 1
  · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    by_cases hci : i ≤ c
    · obtain ⟨h1, h2⟩ := hout (c + 1) b (by omega) (by omega) le_rfl (by omega)
      rw [hin a c le_rfl hai hci (by omega) (by omega), h1, h2, vertex3_lin_left]
    · obtain ⟨h1, h2⟩ := hout a c le_rfl hc.1 (by omega) (by omega)
      rw [hin (c + 1) b (by omega) (by omega) hib le_rfl (by omega), h1, h2, vertex3_lin_right]
  · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd := Finset.mem_Ico.1 hd
    by_cases hci : i ≤ c
    · obtain ⟨h1, h2⟩ := hout (c + 1) d (by omega) (by omega) (by omega) (by omega)
      obtain ⟨h3, h4⟩ := hout (d + 1) b (by omega) (by omega) le_rfl (by omega)
      rw [hin a c le_rfl hai hci (by omega) (by omega), h1, h2, h3, h4, vertex4_lin_one]
    by_cases hdi : i ≤ d
    · obtain ⟨h1, h2⟩ := hout a c le_rfl hc.1 (by omega) (by omega)
      obtain ⟨h3, h4⟩ := hout (d + 1) b (by omega) (by omega) le_rfl (by omega)
      rw [hin (c + 1) d (by omega) (by omega) hdi (by omega) (by omega), h1, h2, h3, h4, vertex4_lin_two]
    · obtain ⟨h1, h2⟩ := hout a c le_rfl hc.1 (by omega) (by omega)
      obtain ⟨h3, h4⟩ := hout (c + 1) d (by omega) (by omega) (by omega) (by omega)
      rw [hin (d + 1) b (by omega) (by omega) hib le_rfl (by omega), h1, h2, h3, h4, vertex4_lin_three]

lemma bgCurrent_update_of_not_mem (p e : ℕ → Fin 4 → ℂ) {i : ℕ} (u : Fin 4 → ℂ) {a b : ℕ} (hab : a ≤ b)
    (h : ¬ (a ≤ i ∧ i ≤ b)) : bgCurrent p (Function.update e i u) a b = bgCurrent p e a b :=
  bgCurrent_congr (b - a) a b rfl hab fun t h1 h2 => ⟨rfl, Function.update_of_ne (by omega) _ _⟩

/-- **The currents are linear in the polarization of each gluon.** -/
theorem bgCurrent_lin (p e : ℕ → Fin 4 → ℂ) (i : ℕ) (x y : ℂ) (v w : Fin 4 → ℂ) :
    ∀ n a b, b - a = n → a ≤ i → i ≤ b →
      bgCurrent p (Function.update e i (x • v + y • w)) a b =
        x • bgCurrent p (Function.update e i v) a b + y • bgCurrent p (Function.update e i w) a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hai hib
    rcases Nat.eq_or_lt_of_le (hai.trans hib) with rfl | hlt
    · have : i = a := by omega
      subst this
      simp
    · rw [bgCurrent_of_lt _ _ hlt, bgCurrent_of_lt _ _ hlt, bgCurrent_of_lt _ _ hlt, smul_smul, smul_smul,
        mul_comm x, mul_comm y, ← smul_smul, ← smul_smul, ← smul_add]
      congr 1
      exact bgVertexSum_lin p x y (fun c d h1 h2 h3 h4 h5 => ih (d - c) (by omega) c d rfl h2 h3)
        (fun c d h1 h2 h3 h4 => ⟨by rw [bgCurrent_update_of_not_mem p e _ h2 h4,
            bgCurrent_update_of_not_mem p e _ h2 h4],
          by rw [bgCurrent_update_of_not_mem p e _ h2 h4, bgCurrent_update_of_not_mem p e _ h2 h4]⟩)
        hai hib

/-- **The amplitude is linear in the polarization of each non-final gluon.** -/
theorem bgAmplitude_lin (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i : ℕ} (hi : i ≤ m + 1) (x y : ℂ)
    (v w : Fin 4 → ℂ) :
    bgAmplitude m p (Function.update e i (x • v + y • w)) =
      x * bgAmplitude m p (Function.update e i v) + y * bgAmplitude m p (Function.update e i w) := by
  simp only [bgAmplitude, Function.update_of_ne (show m + 2 ≠ i by omega)]
  rw [← mdot_smul_right, ← mdot_smul_right, ← mdot_add_right]
  congr 1
  exact bgVertexSum_lin p x y (fun c d h1 h2 h3 h4 h5 => bgCurrent_lin p e i x y v w (d - c) c d rfl h2 h3)
    (fun c d h1 h2 h3 h4 => ⟨by rw [bgCurrent_update_of_not_mem p e _ h2 h4,
        bgCurrent_update_of_not_mem p e _ h2 h4],
      by rw [bgCurrent_update_of_not_mem p e _ h2 h4, bgCurrent_update_of_not_mem p e _ h2 h4]⟩)
    (Nat.zero_le i) hi

/-- **Every planar diagram contains the propagator of a channel at most once**: for the channel `I = {i, …, j}` of
`n = m + 3` gluons (`i < j ≤ m + 1`, `j − i ≤ m`), with `P = p_i + ⋯ + p_j`,
`A_n = A_n^{(no I)} + (1/P²) A_R(V_I)`: the diagrams without the propagator of `I`, plus the amplitude of the merged
gluons with the amputated current `V_I` of `I` as the polarization of the merged gluon. -/
theorem bgAmplitude_split (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i < j) (hj : j ≤ m + 1)
    (hk : j - i ≤ m) :
    bgAmplitude m p e = bgAmplitudeO m p e i j 0 +
      (1 / mdot (momRange p i j) (momRange p i j)) *
        bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j))
          (collapse e i j (bgVertexSum (bgCurrent p e) p i j)) := by
  rw [bgAmplitude_eq_bgAmplitudeO m p e hij.le, ← sub_eq_iff_eq_add', bgAmplitudeO_sub m p e hij.le hj hk,
    bgCurrent_of_lt p e hij]
  have hlin := bgAmplitude_lin (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j 0)
    (i := i) (by omega) (1 / mdot (momRange p i j) (momRange p i j)) 0
    (bgVertexSum (bgCurrent p e) p i j) 0
  simp only [zero_smul, add_zero, zero_mul, update_collapse] at hlin
  exact hlin

/-! ### The residue on the pole: completeness and the Ward identity -/

lemma bgVertexSum_shift (T : ℕ → ℕ → Fin 4 → ℂ) (p : ℕ → Fin 4 → ℂ) (k a b : ℕ) :
    bgVertexSum (fun c d => T (c + k) (d + k)) (fun t => p (t + k)) a b = bgVertexSum T p (a + k) (b + k) := by
  unfold bgVertexSum
  congr 1
  · rw [← Finset.sum_Ico_add']
    refine Finset.sum_congr rfl fun c hc => ?_
    dsimp only
    rw [momRange_shift, momRange_shift, show c + 1 + k = c + k + 1 by omega]
  · rw [← Finset.sum_Ico_add']
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [show c + k + 1 = c + 1 + k by omega, ← Finset.sum_Ico_add']
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [show c + 1 + k = c + k + 1 by omega, show d + 1 + k = d + k + 1 by omega]

/-- The momenta of the left amplitude of the channel `{i, …, j}`: the gluons `i, …, j`, then a gluon of momentum
`P'` (`= −P`). -/
def leftMom (p : ℕ → Fin 4 → ℂ) (i j : ℕ) (P' : Fin 4 → ℂ) : ℕ → Fin 4 → ℂ :=
  fun t => if t ≤ j - i then p (t + i) else P'

/-- The polarizations of the left amplitude: those of `i, …, j`, then `ε`. -/
def leftPol (e : ℕ → Fin 4 → ℂ) (i j : ℕ) (ε : Fin 4 → ℂ) : ℕ → Fin 4 → ℂ :=
  fun t => if t ≤ j - i then e (t + i) else ε

/-- **The left amplitude is the amputated current of the channel**: `A_L(…, ε) = ε · V_I`. -/
theorem bgAmplitude_left (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i < j) (P' ε : Fin 4 → ℂ) :
    bgAmplitude (j - i - 1) (leftMom p i j P') (leftPol e i j ε) =
      mdot ε (bgVertexSum (bgCurrent p e) p i j) := by
  rw [bgAmplitude, show j - i - 1 + 2 = j - i + 1 by omega, show j - i - 1 + 1 = j - i by omega]
  simp only [leftPol, show ¬ (j - i + 1 ≤ j - i) by omega, ↓reduceIte]
  congr 1
  have key : bgVertexSum (bgCurrent (leftMom p i j P') (leftPol e i j ε)) (leftMom p i j P') 0 (j - i) =
      bgVertexSum (fun c d => bgCurrent p e (c + i) (d + i)) (fun t => p (t + i)) 0 (j - i) := by
    refine bgVertexSum_congr' (fun t _ ht => by simp [leftMom, ht]) fun c d _ h2 h3 _ => ?_
    rw [← bgCurrent_shift p e i (d - c) c d rfl]
    exact bgCurrent_congr (d - c) c d rfl h2 fun t _ ht => ⟨by simp [leftMom, show t ≤ j - i by omega],
      by simp [leftPol, show t ≤ j - i by omega]⟩
  rw [key, bgVertexSum_shift, Nat.zero_add, Nat.sub_add_cancel hij.le]

/-- **The residue of the planar amplitude on the pole of the channel `{i, …, j}` factorizes** (Elvang-Huang (3.5)):
on the pole, `P = p_i + ⋯ + p_j = −|P]⟨P|` null, the merged amplitude with the amputated current `V_I` as the
polarization of the merged gluon is `Σ_h A_L(…, −P^{−h}) A_R(P^h, …)`, with the polarization vectors (2.49) of
reference `q` and the spinors `|−P⟩ = −|P⟩`, `|−P] = |P]` of `−P` ((3.14)–(3.15)). The inputs are the Ward
identities (Elvang-Huang p. 17) of the left amplitude at its gluon `−P` and of the merged amplitude at the merged
gluon. -/
theorem residue_factorization (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {i j : ℕ} (hij : i < j) (hj : j ≤ m + 1)
    (hk : j - i ≤ m) (lP ltP lq ltq : Fin 2 → ℂ) (hP : momRange p i j = nullMom lP ltP)
    (hq1 : angleBr ltq ltP ≠ 0) (hq2 : squareBr lq lP ≠ 0)
    (hnull : ∀ t ≤ m + 2, mdot (p t) (p t) = 0) (hcons : momRange p 0 (m + 2) = 0)
    (htr : ∀ t ≤ m + 2, mdot (e t) (p t) = 0)
    (hWL : WardIdentity (j - i - 1) (j - i + 1)) (hWR : WardIdentity (m - (j - i)) i) :
    bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j))
        (collapse e i j (bgVertexSum (bgCurrent p e) p i j)) =
      bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsMinus lP (-ltP) lq)) *
          bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsPlus lP ltP ltq)) +
        bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsPlus lP (-ltP) ltq)) *
          bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsMinus lP ltP lq)) := by
  set P := momRange p i j with hPdef
  set V := bgVertexSum (bgCurrent p e) p i j with hV
  set AR : (Fin 4 → ℂ) → ℂ := fun u => bgAmplitude (m - (j - i)) (collapse p i j P) (collapse e i j u)
    with hAR
  have hlin : ∀ (x y : ℂ) (v w : Fin 4 → ℂ), AR (x • v + y • w) = x * AR v + y * AR w := by
    intro x y v w
    simp only [hAR]
    have := bgAmplitude_lin (m - (j - i)) (collapse p i j P) (collapse e i j 0) (i := i) (by omega) x y v w
    simpa only [update_collapse] using this
  have hPP : mdot P P = 0 := by rw [hP]; exact mdot_nullMom_self lP ltP
  -- the Ward identity of the merged amplitude at the merged gluon: `A_R(P) = 0`
  have hWR' : AR P = 0 := by
    have := hWR (collapse p i j P) (collapse e i j 0)
      (fun t ht => by
        rcases lt_trichotomy t i with h | rfl | h
        · rw [collapse_of_lt p _ h]; exact hnull t (by omega)
        · rw [collapse_self]; exact hPP
        · rw [collapse_of_gt p _ h]; exact hnull _ (by omega))
      (by rw [hPdef, momRange_collapse p hij.le (Nat.zero_le i) (by omega),
            show m - (j - i) + 2 + (j - i) = m + 2 by omega]; exact hcons)
      (fun t ht hti => by
        rcases lt_or_gt_of_ne hti with h | h
        · rw [collapse_of_lt p _ h, collapse_of_lt e _ h]; exact htr t (by omega)
        · rw [collapse_of_gt p _ h, collapse_of_gt e _ h]; exact htr _ (by omega))
    simpa only [hAR, update_collapse, collapse_self] using this
  -- the Ward identity of the left amplitude at the gluon `−P`: `V · P = 0`
  have hWL' : mdot V P = 0 := by
    have := hWL (leftMom p i j (-P)) (leftPol e i j (-P))
      (fun t ht => by
        by_cases h : t ≤ j - i
        · simp only [leftMom, h, ↓reduceIte]; exact hnull _ (by omega)
        · simp only [leftMom, h, ↓reduceIte, mdot_neg_left, mdot_neg_right, neg_neg]; exact hPP)
      (by
        rw [show j - i - 1 + 2 = j - i + 1 by omega, momRange, Finset.sum_Ico_succ_top (by omega)]
        have h1 : ∑ t ∈ Finset.Ico 0 (j - i + 1), leftMom p i j (-P) t =
            ∑ t ∈ Finset.Ico 0 (j - i + 1), p (t + i) :=
          Finset.sum_congr rfl fun t ht => by
            simp [leftMom, show t ≤ j - i by have := Finset.mem_Ico.1 ht; omega]
        have h2 : ∑ t ∈ Finset.Ico 0 (j - i + 1), leftMom p i j (-P) t = P := by
          rw [h1, Finset.sum_Ico_add' (fun t => p t) 0 (j - i + 1) i, Nat.zero_add,
            show j - i + 1 + i = j + 1 by omega, hPdef, momRange]
        rw [h2]
        simp [leftMom])
      (fun t ht hti => by
        have ht' : t ≤ j - i := by omega
        simp only [leftMom, leftPol, ht', ↓reduceIte]; exact htr _ (by omega))
    have hupd : Function.update (leftPol e i j (-P)) (j - i + 1) (leftMom p i j (-P) (j - i + 1)) =
        leftPol e i j (-P) := by
      funext t
      by_cases h : t = j - i + 1
      · subst h; simp [leftMom, leftPol]
      · rw [Function.update_of_ne h]
    rw [hupd, bgAmplitude_left p e hij] at this
    rw [mdot_comm]
    simpa using this
  -- completeness
  have hc := completeness_vec lP ltP lq ltq hq1 hq2 V
  rw [← hP] at hc
  set ep := epsPlus lP ltP ltq
  set em := epsMinus lP ltP lq
  set Q := nullMom lq ltq
  have hdecomp : V = ((-(mdot V em)) • ep + (-(mdot V ep)) • em) +
      ((1 / mdot P Q * mdot V Q) • P + (1 / mdot P Q * mdot V P) • Q) := by
    conv_lhs => rw [hc]
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hAV : AR V = -(mdot V em) * AR ep - mdot V ep * AR em := by
    conv_lhs => rw [hdecomp]
    rw [show ((-(mdot V em)) • ep + (-(mdot V ep)) • em) +
        ((1 / mdot P Q * mdot V Q) • P + (1 / mdot P Q * mdot V P) • Q) =
        (1 : ℂ) • ((-(mdot V em)) • ep + (-(mdot V ep)) • em) +
        (1 : ℂ) • ((1 / mdot P Q * mdot V Q) • P + (1 / mdot P Q * mdot V P) • Q) by simp,
      hlin, hlin, hlin, hWR', hWL']
    ring
  change AR V = _ * AR ep + _ * AR em
  rw [hAV, bgAmplitude_left p e hij, bgAmplitude_left p e hij, epsMinus_neg_right, epsPlus_neg_right,
    mdot_neg_left, mdot_neg_left, mdot_comm (em) V, mdot_comm ep V]
  ring

end Lightlike.SpinorHelicity
