import Lightlike.GR.KruskalMetric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The four regions of the Kruskal–Szekeres extension, the horizon and the radial null directions

Gap row G1-020, the parts after the metric. Source read: S. M. Carroll, *Lecture Notes on General Relativity*,
arXiv:gr-qc/9712019, chapter 7, eqs. (7.82)-(7.84) and the text on the four regions (printed pages 187-190).
Carroll's `(v, u)` are our `(T, X) = (y 0, y 1)`, `G = 1`.

* (7.83) "the event horizon `r = 2GM` ... is defined by `v = ±u`": `kr_eq_two_mul_iff`; also `r > 2M` iff
  `X² > T²` and `r < 2M` iff `X² < T²`.
* (7.84) the surfaces `r = constant` are `u² - v² = constant`: `kr_eq_kr_iff`.
* "Note that `v` is the timelike coordinate": `kruskalQuad_dT_neg`, `kruskalQuad_dX_pos`.
* (7.82) the radial null curves are `v = ±u + constant`: a radial vector `(a, b, 0, 0)` is null iff `a² = b²`
  (`kruskalQuad_radial_eq_zero_iff`), so the tangent `(1, ±1, 0, 0)` of the line `T = ±X + c` is null.
* The four regions of the Kruskal diagram, `I: X > |T|`, `II: T > |X|`, `III: T < -|X|`, `IV: X < -|T|`
  (the source gives them by a figure; the inequalities are read off it), cover the domain together with the
  horizon, `r > 2M` exactly in `I ∪ IV` and `r < 2M` exactly in `II ∪ III`, and the reflection
  `(T, X) ↦ (-T, -X)` exchanges `I` with `IV` and `II` with `III`.
* "Once anything travels from region I into II, it can never return ... you cannot even stop yourself from moving
  in the direction of decreasing `r`": along a differentiable curve in the domain with future-directed causal
  velocity, `T + X` and `T - X` do not decrease, so a curve that is in region II stays in it
  (`kruskalII_of_futureCausal`), and `r` strictly decreases along it (`kr_lt_of_futureCausal_kruskalII`).

**Difference from the source (kind: representation).** Causal curves are stated in the chart: a differentiable
curve `γ : ℝ → (Fin 4 → ℝ)` in the domain whose velocity `v` satisfies `g(v, v) ≤ 0` and `0 < v⁰` (future-directed
for the time orientation `∂_T`). The manifold notions `IsFutureCausalCurve` and the event horizon as the boundary
of the past of future null infinity are not used here.
-/

open Matrix Real Set

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-! ### The radius and the horizon -/

lemma kF_two_mul (hM : M ≠ 0) : kF M (2 * M) = 0 := by
  have h2 : (2 * M) ≠ 0 := mul_ne_zero two_ne_zero hM
  simp [kF, div_self h2]

/-- `r > 2M` iff `X² - T² > 0`. -/
lemma two_mul_lt_kr_iff (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    2 * M < kr M y ↔ 0 < y 1 ^ 2 - y 0 ^ 2 := by
  have hr := kr_pos M hM hy
  have h1 := (kF_strictMonoOn M hM).lt_iff_lt (mem_Ici.2 (by positivity : (0 : ℝ) ≤ 2 * M))
    (mem_Ici.2 hr.le)
  rw [kF_two_mul M hM.ne'] at h1
  unfold kr at h1 ⊢
  rw [kF_kG M hM hy.1] at h1
  exact h1.symm

/-- `r < 2M` iff `X² - T² < 0`. -/
lemma kr_lt_two_mul_iff (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    kr M y < 2 * M ↔ y 1 ^ 2 - y 0 ^ 2 < 0 := by
  have hr := kr_pos M hM hy
  have h1 := (kF_strictMonoOn M hM).lt_iff_lt (mem_Ici.2 hr.le)
    (mem_Ici.2 (by positivity : (0 : ℝ) ≤ 2 * M))
  rw [kF_two_mul M hM.ne'] at h1
  unfold kr at h1 ⊢
  rw [kF_kG M hM hy.1] at h1
  exact h1.symm

/-- **The horizon `r = 2M` is `T = ±X`** (Carroll (7.83)), stated as `X² = T²`. -/
theorem kr_eq_two_mul_iff (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    kr M y = 2 * M ↔ y 1 ^ 2 = y 0 ^ 2 := by
  have h1 := two_mul_lt_kr_iff M hM hy
  have h2 := kr_lt_two_mul_iff M hM hy
  constructor
  · intro h
    have h3 : ¬ (0 < y 1 ^ 2 - y 0 ^ 2) := fun h' => absurd (h1.2 h') (by rw [h]; exact lt_irrefl _)
    have h4 : ¬ (y 1 ^ 2 - y 0 ^ 2 < 0) := fun h' => absurd (h2.2 h') (by rw [h]; exact lt_irrefl _)
    linarith [not_lt.1 h3, not_lt.1 h4]
  · intro h
    have h3 : ¬ (2 * M < kr M y) := fun h' => by have := h1.1 h'; rw [h] at this; linarith
    have h4 : ¬ (kr M y < 2 * M) := fun h' => by have := h2.1 h'; rw [h] at this; linarith
    exact le_antisymm (not_lt.1 h3) (not_lt.1 h4)

/-- `kG` is strictly increasing on `(-1, ∞)`. -/
lemma kG_strictMonoOn (hM : 0 < M) : StrictMonoOn (kG M) (Ioi (-1)) := by
  intro s hs t ht hst
  have h1 := (kF_strictMonoOn M hM).lt_iff_lt (mem_Ici.2 (kG_pos M hM hs).le)
    (mem_Ici.2 (kG_pos M hM ht).le)
  rw [kF_kG M hM hs, kF_kG M hM ht] at h1
  exact h1.1 hst

/-- **The surfaces `r = constant` are `X² - T² = constant`** (Carroll (7.84)). -/
theorem kr_eq_kr_iff (hM : 0 < M) {y z : Fin 4 → ℝ} (hy : y ∈ kruskalU) (hz : z ∈ kruskalU) :
    kr M y = kr M z ↔ y 1 ^ 2 - y 0 ^ 2 = z 1 ^ 2 - z 0 ^ 2 :=
  ⟨fun h => (kG_strictMonoOn M hM).injOn hy.1 hz.1 h, fun h => by unfold kr; rw [h]⟩

/-! ### The four regions -/

/-- Region I of the Kruskal diagram: `X > |T|` (the exterior from which the extension starts). -/
def kruskalI : Set (Fin 4 → ℝ) := {y | y ∈ kruskalU ∧ |y 0| < y 1}

/-- Region II: `T > |X|` (the black hole). -/
def kruskalII : Set (Fin 4 → ℝ) := {y | y ∈ kruskalU ∧ |y 1| < y 0}

/-- Region III: `T < -|X|` (the white hole). -/
def kruskalIII : Set (Fin 4 → ℝ) := {y | y ∈ kruskalU ∧ y 0 < -|y 1|}

/-- Region IV: `X < -|T|` (the second exterior). -/
def kruskalIV : Set (Fin 4 → ℝ) := {y | y ∈ kruskalU ∧ y 1 < -|y 0|}

/-- The horizon `T = ±X`. -/
def kruskalHorizon : Set (Fin 4 → ℝ) := {y | y ∈ kruskalU ∧ y 1 ^ 2 = y 0 ^ 2}

/-- The domain is the union of the four regions and the horizon. -/
theorem kruskalU_eq_union :
    kruskalU = kruskalI ∪ kruskalII ∪ kruskalIII ∪ kruskalIV ∪ kruskalHorizon := by
  ext y
  simp only [kruskalI, kruskalII, kruskalIII, kruskalIV, kruskalHorizon, mem_union, mem_ofPred_eq]
  constructor
  · intro hy
    by_cases h : y 1 ^ 2 = y 0 ^ 2
    · exact Or.inr ⟨hy, h⟩
    · rcases lt_or_gt_of_ne h with h1 | h1
      · -- `|X| < |T|`
        have h2 : |y 1| < |y 0| := sq_lt_sq.1 h1
        rcases le_or_gt 0 (y 0) with h0 | h0
        · rw [abs_of_nonneg h0] at h2
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hy, h2⟩)))
        · rw [abs_of_neg h0] at h2
          exact Or.inl (Or.inl (Or.inr ⟨hy, by linarith⟩))
      · have h2 : |y 0| < |y 1| := sq_lt_sq.1 h1
        rcases le_or_gt 0 (y 1) with h0 | h0
        · rw [abs_of_nonneg h0] at h2
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hy, h2⟩)))
        · rw [abs_of_neg h0] at h2
          exact Or.inl (Or.inr ⟨hy, by linarith⟩)
  · rintro ((((h | h) | h) | h) | h) <;> exact h.1

/-- **`r > 2M` exactly in the two exterior regions `I` and `IV`.** -/
theorem two_mul_lt_kr_iff_mem (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    2 * M < kr M y ↔ y ∈ kruskalI ∪ kruskalIV := by
  rw [two_mul_lt_kr_iff M hM hy]
  simp only [kruskalI, kruskalIV, mem_union, mem_ofPred_eq]
  constructor
  · intro h
    have h2 : |y 0| < |y 1| := sq_lt_sq.1 (by linarith)
    rcases le_or_gt 0 (y 1) with h0 | h0
    · rw [abs_of_nonneg h0] at h2; exact Or.inl ⟨hy, h2⟩
    · rw [abs_of_neg h0] at h2; exact Or.inr ⟨hy, by linarith⟩
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · have : |y 0| < |y 1| := lt_of_lt_of_le h (le_abs_self _)
      linarith [sq_lt_sq.2 this]
    · have : |y 0| < |y 1| := by
        have := neg_le_abs (y 1)
        linarith
      linarith [sq_lt_sq.2 this]

/-- **`r < 2M` exactly in the black hole `II` and the white hole `III`.** -/
theorem kr_lt_two_mul_iff_mem (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    kr M y < 2 * M ↔ y ∈ kruskalII ∪ kruskalIII := by
  rw [kr_lt_two_mul_iff M hM hy]
  simp only [kruskalII, kruskalIII, mem_union, mem_ofPred_eq]
  constructor
  · intro h
    have h2 : |y 1| < |y 0| := sq_lt_sq.1 (by linarith)
    rcases le_or_gt 0 (y 0) with h0 | h0
    · rw [abs_of_nonneg h0] at h2; exact Or.inl ⟨hy, h2⟩
    · rw [abs_of_neg h0] at h2; exact Or.inr ⟨hy, by linarith⟩
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · have : |y 1| < |y 0| := lt_of_lt_of_le h (le_abs_self _)
      linarith [sq_lt_sq.2 this]
    · have : |y 1| < |y 0| := by
        have := neg_le_abs (y 0)
        linarith
      linarith [sq_lt_sq.2 this]

/-- The reflection `(T, X) ↦ (-T, -X)` maps region I to region IV. -/
lemma kruskalNeg_mem_IV {y : Fin 4 → ℝ} (hy : y ∈ kruskalI) : kruskalNeg y ∈ kruskalIV := by
  refine ⟨kruskalNeg_mem hy.1, ?_⟩
  have := hy.2
  simp [kruskalNeg]
  linarith

/-- The reflection `(T, X) ↦ (-T, -X)` maps region II to region III. -/
lemma kruskalNeg_mem_III {y : Fin 4 → ℝ} (hy : y ∈ kruskalII) : kruskalNeg y ∈ kruskalIII := by
  refine ⟨kruskalNeg_mem hy.1, ?_⟩
  have := hy.2
  simp [kruskalNeg]
  linarith

/-! ### The quadratic form: timelike coordinate, radial null directions -/

/-- The quadratic form `g(v, v)` of the Kruskal metric at `y`. -/
def kruskalQuad (y v : Fin 4 → ℝ) : ℝ := v ⬝ᵥ kruskalMetric M y *ᵥ v

lemma kruskalQuad_eq (y v : Fin 4 → ℝ) :
    kruskalQuad M y v = kh M (kr M y) * (v 1 ^ 2 - v 0 ^ 2) +
      kr M y ^ 2 * (v 2 ^ 2 + sin (y 2) ^ 2 * v 3 ^ 2) := by
  simp [kruskalQuad, kruskalMetric, dotProduct, mulVec, Fin.sum_univ_four]
  ring

lemma kh_pos (hM : 0 < M) {r : ℝ} (hr : 0 < r) : 0 < kh M r := by
  unfold kh; positivity

/-- **`T` is the timelike coordinate**: `g(∂_T, ∂_T) < 0`. -/
theorem kruskalQuad_dT_neg (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    kruskalQuad M y ![1, 0, 0, 0] < 0 := by
  rw [kruskalQuad_eq]
  have := kh_pos M hM (kr_pos M hM hy)
  simp
  linarith

/-- `X` is a spacelike coordinate: `0 < g(∂_X, ∂_X)`. -/
theorem kruskalQuad_dX_pos (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    0 < kruskalQuad M y ![0, 1, 0, 0] := by
  rw [kruskalQuad_eq]
  have := kh_pos M hM (kr_pos M hM hy)
  simp
  linarith

/-- **The radial null directions are `T = ±X`** (Carroll (7.82)): a radial vector `(a, b, 0, 0)` is null iff
`a² = b²`. In particular the tangent `(1, ±1, 0, 0)` of the line `T = ±X + c` is null. -/
theorem kruskalQuad_radial_eq_zero_iff (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) (a b : ℝ) :
    kruskalQuad M y ![a, b, 0, 0] = 0 ↔ a ^ 2 = b ^ 2 := by
  rw [kruskalQuad_eq]
  have h := kh_pos M hM (kr_pos M hM hy)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  constructor
  · intro h1
    have h2 : kh M (kr M y) * (b ^ 2 - a ^ 2) = 0 := by
      have : kr M y ^ 2 * ((0 : ℝ) ^ 2 + sin (y 2) ^ 2 * (0 : ℝ) ^ 2) = 0 := by ring
      linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 h.ne'
    · linarith
  · intro h1
    rw [h1]; ring

/-! ### Future-directed causal vectors and region II -/

/-- A vector `v` at `y` is **future-directed causal** for the Kruskal metric and the time orientation `∂_T`:
`g(v, v) ≤ 0` and `0 < v⁰`. -/
def IsKruskalFutureCausal (y v : Fin 4 → ℝ) : Prop := kruskalQuad M y v ≤ 0 ∧ 0 < v 0

/-- A future-directed causal vector has `|v¹| ≤ v⁰`. -/
lemma abs_le_of_isKruskalFutureCausal (hM : 0 < M) {y v : Fin 4 → ℝ} (hy : y ∈ kruskalU)
    (hv : IsKruskalFutureCausal M y v) : |v 1| ≤ v 0 := by
  obtain ⟨h1, h2⟩ := hv
  rw [kruskalQuad_eq] at h1
  have h := kh_pos M hM (kr_pos M hM hy)
  have h3 : 0 ≤ kr M y ^ 2 * (v 2 ^ 2 + sin (y 2) ^ 2 * v 3 ^ 2) := by positivity
  have h4 : kh M (kr M y) * (v 1 ^ 2 - v 0 ^ 2) ≤ 0 := by linarith
  have h5 : v 1 ^ 2 - v 0 ^ 2 ≤ 0 := by
    by_contra h6
    have := mul_pos h (not_le.1 h6)
    linarith
  exact abs_le_of_sq_le_sq (by linarith) h2.le

variable {M}

/-- Along a curve with future-directed causal velocity, `T + X` and `T - X` do not decrease. -/
lemma monotone_add_sub_of_futureCausal (hM : 0 < M) {γ : ℝ → Fin 4 → ℝ} (hγ : Differentiable ℝ γ)
    (hU : ∀ t, γ t ∈ kruskalU) (hc : ∀ t, IsKruskalFutureCausal M (γ t) (deriv γ t)) :
    Monotone (fun t => γ t 0 + γ t 1) ∧ Monotone (fun t => γ t 0 - γ t 1) := by
  have hd : ∀ t i, HasDerivAt (fun t => γ t i) (deriv γ t i) t := fun t i =>
    hasDerivAt_pi.1 (hγ t).hasDerivAt i
  have habs : ∀ t, |deriv γ t 1| ≤ deriv γ t 0 := fun t =>
    abs_le_of_isKruskalFutureCausal M hM (hU t) (hc t)
  constructor
  · refine monotone_of_deriv_nonneg (fun t => ((hd t 0).add (hd t 1)).differentiableAt) fun t => ?_
    rw [show (fun t => γ t 0 + γ t 1) = (fun t => γ t 0) + fun t => γ t 1 from rfl,
      ((hd t 0).add (hd t 1)).deriv]
    linarith [neg_abs_le (deriv γ t 1), habs t]
  · refine monotone_of_deriv_nonneg (fun t => ((hd t 0).sub (hd t 1)).differentiableAt) fun t => ?_
    rw [show (fun t => γ t 0 - γ t 1) = (fun t => γ t 0) - fun t => γ t 1 from rfl,
      ((hd t 0).sub (hd t 1)).deriv]
    linarith [le_abs_self (deriv γ t 1), habs t]

/-- **Nothing leaves the black hole** (Carroll, chapter 7, on region II: "it can never return"): a curve in
the Kruskal domain with future-directed causal velocity that is in region II at a time `t₀` is in region II at
every later time. -/
theorem kruskalII_of_futureCausal (hM : 0 < M) {γ : ℝ → Fin 4 → ℝ} (hγ : Differentiable ℝ γ)
    (hU : ∀ t, γ t ∈ kruskalU) (hc : ∀ t, IsKruskalFutureCausal M (γ t) (deriv γ t)) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (h0 : γ t₀ ∈ kruskalII) : γ t ∈ kruskalII := by
  obtain ⟨h1, h2⟩ := monotone_add_sub_of_futureCausal hM hγ hU hc
  have h3 := h1 ht
  have h4 := h2 ht
  have h5 := abs_lt.1 h0.2
  refine ⟨hU t, abs_lt.2 ⟨?_, ?_⟩⟩
  · simp only at h3; linarith [h5.1]
  · simp only at h4; linarith [h5.2]

/-- **In the black hole the radius decreases** (Carroll, chapter 7: "you cannot even stop yourself from moving
in the direction of decreasing `r`"): along a curve in the Kruskal domain with future-directed causal velocity
that is in region II at `t₀`, the radius at every later time is strictly smaller. -/
theorem kr_lt_of_futureCausal_kruskalII (hM : 0 < M) {γ : ℝ → Fin 4 → ℝ} (hγ : Differentiable ℝ γ)
    (hU : ∀ t, γ t ∈ kruskalU) (hc : ∀ t, IsKruskalFutureCausal M (γ t) (deriv γ t)) {t₀ t : ℝ}
    (ht : t₀ < t) (h0 : γ t₀ ∈ kruskalII) : kr M (γ t) < kr M (γ t₀) := by
  have hd : ∀ t i, HasDerivAt (fun t => γ t i) (deriv γ t i) t := fun t i =>
    hasDerivAt_pi.1 (hγ t).hasDerivAt i
  have hs : ∀ s, HasDerivAt (fun t => γ t 1 ^ 2 - γ t 0 ^ 2)
      (2 * γ s 1 ^ (2 - 1) * deriv γ s 1 - 2 * γ s 0 ^ (2 - 1) * deriv γ s 0) s := fun s =>
    ((hd s 1).pow 2).sub ((hd s 0).pow 2)
  have hanti : StrictAntiOn (fun t => γ t 1 ^ 2 - γ t 0 ^ 2) (Ici t₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici t₀)
      (continuous_iff_continuousAt.2 fun s => (hs s).continuousAt).continuousOn fun s hs' => ?_
    rw [interior_Ici] at hs'
    rw [(hs s).deriv]
    have hII := kruskalII_of_futureCausal hM hγ hU hc (le_of_lt hs') h0
    have habs := abs_le_of_isKruskalFutureCausal M hM (hU s) (hc s)
    have hv0 := (hc s).2
    have h5 := abs_lt.1 hII.2
    have h6 := abs_le.1 habs
    simp only [Nat.add_one_sub_one, pow_one]
    -- `X v¹ < T v⁰`
    have h7 : γ s 1 * deriv γ s 1 < γ s 0 * deriv γ s 0 := by
      have h8 : γ s 1 * deriv γ s 1 ≤ |γ s 1| * deriv γ s 0 := by
        calc γ s 1 * deriv γ s 1 ≤ |γ s 1 * deriv γ s 1| := le_abs_self _
          _ = |γ s 1| * |deriv γ s 1| := abs_mul _ _
          _ ≤ |γ s 1| * deriv γ s 0 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      have h9 : |γ s 1| * deriv γ s 0 < γ s 0 * deriv γ s 0 := mul_lt_mul_of_pos_right hII.2 hv0
      linarith
    linarith
  have hlt := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
  exact kG_strictMonoOn M hM (hU t).1 (hU t₀).1 hlt

end Lightlike
