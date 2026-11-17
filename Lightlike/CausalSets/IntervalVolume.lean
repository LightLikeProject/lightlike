import Lightlike.CausalSets.Sprinkling

/-!
# The volume of a causal interval in `d + 1` dimensions

The volume of the causal interval `{z | 0 ≼ z ≼ w}` between `0` and a future causal vector `w` of
Minkowski space `ℝ^{d+1}` is the volume of the unit causal diamond times the power `d + 1` of the
proper time `τ(w) = √(w⁰² - |w⃗|²)` (`volume_interval_all`). The proof moves `w` to `τ e₀` by a Lorentz
boost along the spatial direction of `w` (`boost`): the boost is linear, preserves the Minkowski form
(`boost_form`) and the future cone (`coneLE_boost`), and has determinant of absolute value `1`
because a linear map preserving the form has `det² = 1` (`det_sq_of_mSq`), so it preserves
Lebesgue measure; then a rescaling by `τ` gives the unit diamond. A lightlike `w` is approached from
above. This is part of a bridge between Lorentzian geometry and causal sets: the interval volume is
the input of the Myrheim–Meyer count of `Lightlike/CausalSets/Myrheim4D.lean`.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open Matrix MeasureTheory
open Lightlike
open scoped Pointwise

namespace Lightlike.CausalSets

variable {d : ℕ}

/-- The **Lorentz boost** of `ℝ^{d+1}` along the unit vector `n` of space, with Lorentz factor `g`
and `h = g β` (`g² - h² = 1`): `t ↦ g t - h n·x`, `x ↦ x + ((g - 1) n·x - h t) n`. -/
def boost (n : Fin d → ℝ) (g h : ℝ) (z : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (g * z 0 - h * ∑ i, n i * z i.succ)
    (fun i => z i.succ + ((g - 1) * ∑ j, n j * z j.succ - h * z 0) * n i)

lemma boost_zero (n : Fin d → ℝ) (g h : ℝ) (z : Fin (d + 1) → ℝ) :
    boost n g h z 0 = g * z 0 - h * ∑ i, n i * z i.succ := by simp [boost]

lemma boost_succ (n : Fin d → ℝ) (g h : ℝ) (z : Fin (d + 1) → ℝ) (i : Fin d) :
    boost n g h z i.succ = z i.succ + ((g - 1) * ∑ j, n j * z j.succ - h * z 0) * n i := by
  simp [boost]

lemma spatialSq_eq_sum (v : Fin (d + 1) → ℝ) : spatialSq v = ∑ i : Fin d, v i.succ ^ 2 := rfl

/-- The boost preserves the Minkowski form. -/
lemma boost_form (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (z : Fin (d + 1) → ℝ) :
    (boost n g h z 0) ^ 2 - spatialSq (boost n g h z) = z 0 ^ 2 - spatialSq z := by
  set s := ∑ j, n j * z j.succ with hs
  set c := (g - 1) * s - h * z 0 with hc
  have h1 : spatialSq (boost n g h z) = spatialSq z + 2 * c * s + c ^ 2 := by
    simp only [spatialSq_eq_sum, boost_succ, add_sq, Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum, hn]
    rw [← hc]
    have : ∑ i : Fin d, 2 * z i.succ * (c * n i) = 2 * c * s := by
      rw [hs, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  rw [h1, boost_zero]
  rw [← hs]
  have hc' : c = (g - 1) * s - h * z 0 := hc
  rw [hc']
  linear_combination (z 0 ^ 2 - s ^ 2) * hg

lemma boost_inv (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (z : Fin (d + 1) → ℝ) : boost n g (-h) (boost n g h z) = z := by
  set s := ∑ j, n j * z j.succ with hs
  have hs' : ∑ j, n j * boost n g h z j.succ = s + ((g - 1) * s - h * z 0) := by
    simp only [boost_succ]
    have : ∀ j, n j * (z j.succ + ((g - 1) * s - h * z 0) * n j) =
        n j * z j.succ + ((g - 1) * s - h * z 0) * n j ^ 2 := fun j => by ring
    rw [← hs]
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hn]; rw [← hs]; ring
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [boost_zero, boost_zero, hs']
    rw [← hs]
    linear_combination (z 0) * hg
  · rw [boost_succ, boost_succ, boost_zero, hs']
    rw [← hs]
    linear_combination (s * n j) * hg

lemma boost_fut (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (hg0 : 0 < g) {z : Fin (d + 1) → ℝ} (hz0 : 0 ≤ z 0) (hz : spatialSq z ≤ z 0 ^ 2) :
    0 ≤ boost n g h z 0 ∧ spatialSq (boost n g h z) ≤ boost n g h z 0 ^ 2 := by
  have hform := boost_form n g h hn hg z
  refine ⟨?_, by nlinarith [hform]⟩
  rw [boost_zero]
  have hS : (∑ i, n i * z i.succ) ^ 2 ≤ spatialSq z := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ n (fun i => z i.succ)
    simpa [hn, spatialSq_eq_sum] using this
  have hs : |∑ i, n i * z i.succ| ≤ z 0 := abs_le.2 (abs_le_of_sq_le_sq' (hS.trans hz) hz0)
  have hh : |h| ≤ g := abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith) hg0.le)
  nlinarith [mul_nonneg hz0 hg0.le, mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 (le_abs_self h)),
    mul_nonneg (sub_nonneg.2 hh) hz0, abs_nonneg h, neg_abs_le h, mul_nonneg (sub_nonneg.2 hh) (abs_nonneg (∑ i, n i * z i.succ)),
    le_abs_self (∑ i, n i * z i.succ), neg_abs_le (∑ i, n i * z i.succ)]

lemma form_polar {D : ℕ} (u v : Fin D → ℝ) :
    minkowskiForm D u v = (mSq (u + v) - mSq u - mSq v) / 2 := by
  simp only [mSq, minkowskiForm_apply, Pi.add_apply]
  rw [← sub_eq_zero]
  have : ∑ i, etaDiag i * (u i + v i) * (u i + v i) - ∑ i, etaDiag i * u i * u i -
      ∑ i, etaDiag i * v i * v i = 2 * ∑ i, etaDiag i * u i * v i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

lemma det_sq_of_mSq {D : ℕ} (f : (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ)) (hf : ∀ z, mSq (f z) = mSq z) :
    (LinearMap.det f) ^ 2 = 1 := by
  have hη : ∀ u v, minkowskiForm D (f u) (f v) = minkowskiForm D u v := by
    intro u v
    rw [form_polar, form_polar u v, ← map_add, hf, hf, hf]
  set M := LinearMap.toMatrix' f with hM
  have hMat : Mᵀ * eta D * M = eta D := by
    ext i j
    have h1 := hη (fun k => if k = i then 1 else 0) (fun k => if k = j then 1 else 0)
    simp only [minkowskiForm_apply] at h1
    simp only [eta, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, hM,
      LinearMap.toMatrix'_apply]
    have hsingle : ∀ i : Fin D, (Pi.single i (1 : ℝ) : Fin D → ℝ) = fun k => if k = i then 1 else 0 := by
      intro i; funext k; simp [Pi.single_apply]
    simp only [hsingle]
    have e1 : ∀ j1 : Fin D, (∑ j, f (fun k => if k = i then 1 else 0) j * if j = j1 then etaDiag j else 0) =
        f (fun k => if k = i then 1 else 0) j1 * etaDiag j1 := by
      intro j1; simp [Finset.sum_ite_eq']
    simp only [e1]
    have e2 : ∑ k : Fin D, (etaDiag k * (if k = i then (1 : ℝ) else 0)) * (if k = j then (1 : ℝ) else 0) =
        if i = j then etaDiag i else 0 := by
      by_cases hij : i = j
      · subst hij
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [hk]
        · simp
      · rw [ite_eq_right_iff.2 (fun h => absurd h hij)]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = i
        · subst hk; simp [hij]
        · simp [hk]
    rw [e2] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hd := congrArg Matrix.det hMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hne : (eta D).det ≠ 0 := by
    rw [eta, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    unfold etaDiag; split_ifs <;> norm_num
  rw [← LinearMap.det_toMatrix' f, ← hM]
  have : (M.det ^ 2 - 1) * (eta D).det = 0 := by linear_combination hd
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hne

/-- The boost as a linear map. -/
def boostLin (n : Fin d → ℝ) (g h : ℝ) : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun := boost n g h
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [boost_zero, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    · simp only [boost_succ, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c x := by
    have hsum : ∑ j, n j * (c * x j.succ) = c * ∑ j, n j * x j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [boost_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hsum]; ring
    · simp only [boost_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hsum]; ring

lemma boostLin_apply (n : Fin d → ℝ) (g h : ℝ) (z : Fin (d + 1) → ℝ) :
    boostLin n g h z = boost n g h z := rfl

/-- The boost has determinant of absolute value `1`. -/
lemma abs_det_boost (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1) :
    |LinearMap.det (boostLin n g h)| = 1 := by
  have := det_sq_of_mSq (boostLin n g h) (fun z => by
    rw [boostLin_apply, mSq_eq, mSq_eq]
    have := boost_form n g h hn hg z
    linarith)
  have h2 : |LinearMap.det (boostLin n g h)| ^ 2 = 1 := by rw [sq_abs]; exact this
  nlinarith [abs_nonneg (LinearMap.det (boostLin n g h))]

/-- `v` is in the closed future light cone of `ℝ^{d+1}`: `0 ≤ v⁰` and `|v⃗|² ≤ (v⁰)²`. -/
def Fut (v : Fin (d + 1) → ℝ) : Prop := 0 ≤ v 0 ∧ spatialSq v ≤ v 0 ^ 2

lemma Fut_iff_coneLE (x y : Fin (d + 1) → ℝ) : Fut (y - x) ↔ coneLE x y := by
  rw [coneLE_iff_spatial]; rfl

lemma boost_sub (n : Fin d → ℝ) (g h : ℝ) (x y : Fin (d + 1) → ℝ) :
    boost n g h (y - x) = boost n g h y - boost n g h x := (boostLin n g h).map_sub y x

lemma coneLE_boost (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (hg0 : 0 < g) (x y : Fin (d + 1) → ℝ) :
    coneLE (boost n g h x) (boost n g h y) ↔ coneLE x y := by
  rw [← Fut_iff_coneLE, ← Fut_iff_coneLE, ← boost_sub]
  constructor
  · intro hf
    have := boost_fut n g (-h) hn (by linarith [hg]) hg0 hf.1 hf.2
    rwa [boost_inv n g h hn hg] at this
  · intro hf; exact boost_fut n g h hn hg hg0 hf.1 hf.2

/-- The **causal interval** between `0` and `w` in `ℝ^{d+1}`: the points `z` with `0 ≼ z ≼ w`. -/
def intervalSet (w : Fin (d + 1) → ℝ) : Set (Fin (d + 1) → ℝ) := {z | coneLE 0 z ∧ coneLE z w}

lemma boost_zero_vec (n : Fin d → ℝ) (g h : ℝ) : boost n g h (0 : Fin (d + 1) → ℝ) = 0 :=
  (boostLin n g h).map_zero

lemma boost_image_interval (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (hg0 : 0 < g) (w : Fin (d + 1) → ℝ) :
    boost n g h '' intervalSet w = intervalSet (boost n g h w) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← boost_zero_vec n g h]; exact (coneLE_boost n g h hn hg hg0 _ _).2 hx1
    · exact (coneLE_boost n g h hn hg hg0 _ _).2 hx2
  · rintro ⟨hz1, hz2⟩
    have hg' : g ^ 2 - (-h) ^ 2 = 1 := by linarith [hg]
    have e : boost n g h (boost n g (-h) z) = z := by
      simpa using boost_inv n g (-h) hn hg' z
    refine ⟨boost n g (-h) z, ⟨?_, ?_⟩, e⟩
    · have := (coneLE_boost n g (-h) hn hg' hg0 0 z).2 hz1
      rwa [boost_zero_vec] at this
    · have := (coneLE_boost n g (-h) hn hg' hg0 z (boost n g h w)).2 hz2
      rwa [boost_inv n g h hn hg] at this

lemma volume_boost_image (n : Fin d → ℝ) (g h : ℝ) (hn : ∑ i, n i ^ 2 = 1) (hg : g ^ 2 - h ^ 2 = 1)
    (s : Set (Fin (d + 1) → ℝ)) :
    MeasureTheory.volume (boost n g h '' s) = MeasureTheory.volume s := by
  have := MeasureTheory.Measure.addHaar_image_linearMap (MeasureTheory.volume : Measure (Fin (d + 1) → ℝ))
    (boostLin n g h) s
  have himg : (⇑(boostLin n g h) : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ)) = boost n g h := rfl
  rw [himg] at this
  rw [this, abs_det_boost n g h hn hg]
  simp

lemma spatialSq_smul (c : ℝ) (v : Fin (d + 1) → ℝ) : spatialSq (c • v) = c ^ 2 * spatialSq v := by
  simp [spatialSq, mul_pow, Finset.mul_sum]

lemma coneLE_smul {c : ℝ} (hc : 0 < c) (x y : Fin (d + 1) → ℝ) :
    coneLE (c • x) (c • y) ↔ coneLE x y := by
  rw [coneLE_iff_spatial, coneLE_iff_spatial, ← smul_sub, spatialSq_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨by nlinarith, ?_⟩
    have : c ^ 2 * spatialSq (y - x) ≤ c ^ 2 * ((y - x) 0) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · rintro ⟨a, b⟩
    exact ⟨by positivity, by nlinarith [b, sq_nonneg c]⟩

lemma interval_smul {c : ℝ} (hc : 0 < c) (w : Fin (d + 1) → ℝ) :
    intervalSet (c • w) = c • intervalSet w := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c⁻¹ • z, ⟨?_, ?_⟩, by simp [smul_smul, hc.ne']⟩
    · have := (coneLE_smul (inv_pos.2 hc) 0 z).2 h1
      simpa using this
    · have := (coneLE_smul (inv_pos.2 hc) z (c • w)).2 h2
      simpa [smul_smul, hc.ne'] using this
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have := (coneLE_smul hc 0 x).2 h1; simpa using this
    · exact (coneLE_smul hc x w).2 h2

lemma diamond_eq_interval (d : ℕ) : diamond d = intervalSet (diamondTop d) := rfl

lemma exists_dir (hd : 0 < d) (w : Fin (d + 1) → ℝ) :
    ∃ n : Fin d → ℝ, ∑ i, n i ^ 2 = 1 ∧ ∀ i : Fin d, w i.succ = √(spatialSq w) * n i := by
  set c := √(spatialSq w) with hc
  have hc2 : c ^ 2 = spatialSq w := Real.sq_sqrt (spatialSq_nonneg w)
  by_cases hc0 : c = 0
  · have h0 : spatialSq w = 0 := by rw [← hc2, hc0]; norm_num
    refine ⟨Pi.single ⟨0, hd⟩ 1, ?_, fun i => ?_⟩
    · simp [Pi.single_apply]
    · have : ∀ j : Fin d, w j.succ ^ 2 = 0 := by
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (w k.succ))).1
          (by simpa [spatialSq_eq_sum] using h0) j (Finset.mem_univ j)
        exact this
      have := pow_eq_zero_iff (two_ne_zero) |>.1 (this i)
      simp [hc0, this]
  · refine ⟨fun i => w i.succ / c, ?_, fun i => by field_simp⟩
    have : ∑ i : Fin d, (w i.succ / c) ^ 2 = spatialSq w / c ^ 2 := by
      simp [spatialSq_eq_sum, div_pow, Finset.sum_div]
    rw [this, ← hc2]; field_simp

/-- The volume of a causal interval with a timelike endpoint: a Lorentz boost moves the endpoint onto
the time axis and a rescaling gives the unit diamond. -/
lemma volume_interval (hd : 0 < d) {w : Fin (d + 1) → ℝ} (hw : Fut w)
    (hτ : 0 < w 0 ^ 2 - spatialSq w) :
    MeasureTheory.volume (intervalSet w) =
      ENNReal.ofReal (√(w 0 ^ 2 - spatialSq w) ^ (d + 1)) * MeasureTheory.volume (diamond d) := by
  set τ := √(w 0 ^ 2 - spatialSq w) with hτdef
  have hτ0 : 0 < τ := Real.sqrt_pos.2 hτ
  have hτ2 : τ ^ 2 = w 0 ^ 2 - spatialSq w := Real.sq_sqrt hτ.le
  obtain ⟨n, hn, hnw⟩ := exists_dir hd w
  set c := √(spatialSq w) with hc
  have hc2 : c ^ 2 = spatialSq w := Real.sq_sqrt (spatialSq_nonneg w)
  have hw0 : 0 < w 0 := by
    rcases hw.1.eq_or_lt with h | h
    · exfalso; nlinarith [spatialSq_nonneg w]
    · exact h
  have hg : (w 0 / τ) ^ 2 - (c / τ) ^ 2 = 1 := by
    field_simp; nlinarith [hτ2, hc2]
  have hg0 : 0 < w 0 / τ := by positivity
  have hsw : ∑ j, n j * w j.succ = c := by
    have : ∀ j, n j * w j.succ = c * n j ^ 2 := fun j => by rw [hnw j]; ring
    simp only [this, ← Finset.mul_sum, hn]; ring
  have hBw : boost n (w 0 / τ) (c / τ) w = τ • diamondTop d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [boost_zero, hsw]
      simp [diamondTop]
      field_simp
      nlinarith [hτ2, hc2]
    · rw [boost_succ, hsw, hnw j]
      simp [diamondTop, Fin.succ_ne_zero]
      field_simp; ring
  calc MeasureTheory.volume (intervalSet w)
      = MeasureTheory.volume (boost n (w 0 / τ) (c / τ) '' intervalSet w) :=
        (volume_boost_image n _ _ hn hg _).symm
    _ = MeasureTheory.volume (intervalSet (τ • diamondTop d)) := by
        rw [boost_image_interval n _ _ hn hg hg0, hBw]
    _ = _ := by
        rw [interval_smul hτ0, MeasureTheory.Measure.addHaar_smul, ← diamond_eq_interval]
        simp only [Module.finrank_fin_fun]
        rw [abs_of_pos (by positivity)]

lemma interval_mono {w w' : Fin (d + 1) → ℝ} (h : coneLE w w') : intervalSet w ⊆ intervalSet w' :=
  fun _ hz => ⟨hz.1, coneLE_trans hz.2 h⟩

lemma spatialSq_add_top (w : Fin (d + 1) → ℝ) (ε : ℝ) :
    spatialSq (w + ε • diamondTop d) = spatialSq w := by
  simp [spatialSq_eq_sum, diamondTop, Fin.succ_ne_zero]

/-- **The volume of a causal interval of `ℝ^{d+1}`** (`d ≥ 1`): for a future causal vector `w`, the
interval between `0` and `w` has volume `τ^{d+1}` times the volume of the unit causal diamond, with
`τ² = (w⁰)² - |w⃗|²`; for a lightlike `w` the value is `0`. -/
lemma volume_interval_all (hd : 0 < d) {w : Fin (d + 1) → ℝ} (hw : Fut w) :
    MeasureTheory.volume (intervalSet w) =
      ENNReal.ofReal (√(w 0 ^ 2 - spatialSq w) ^ (d + 1)) * MeasureTheory.volume (diamond d) := by
  have hτ0 : 0 ≤ w 0 ^ 2 - spatialSq w := by linarith [hw.2]
  rcases hτ0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [Real.sqrt_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, ENNReal.ofReal_zero, zero_mul]
    set V := MeasureTheory.volume (diamond d) with hV
    have hle : ∀ ε : ℝ, 0 < ε → MeasureTheory.volume (intervalSet w) ≤
        ENNReal.ofReal (√((w 0 + ε) ^ 2 - spatialSq w) ^ (d + 1)) * V := by
      intro ε hε
      have hsp := spatialSq_add_top w ε
      have hw0' : (w + ε • diamondTop d) 0 = w 0 + ε := by simp [diamondTop]
      have hF : Fut (w + ε • diamondTop d) := by
        refine ⟨by rw [hw0']; linarith [hw.1], ?_⟩
        rw [hsp, hw0']; nlinarith [hw.1, hw.2]
      have hsub : intervalSet w ⊆ intervalSet (w + ε • diamondTop d) := by
        apply interval_mono
        rw [coneLE_iff_spatial]
        have e : (w + ε • diamondTop d) - w = ε • diamondTop d := by abel
        rw [e, spatialSq_smul]
        have : spatialSq (diamondTop d) = 0 := by simp [spatialSq_eq_sum, diamondTop, Fin.succ_ne_zero]
        rw [this]
        simp [diamondTop]; exact ⟨hε.le, sq_nonneg ε⟩
      have hτ' : 0 < (w + ε • diamondTop d) 0 ^ 2 - spatialSq (w + ε • diamondTop d) := by
        rw [hsp, hw0']; nlinarith [hw.1, hw.2]
      refine (measure_mono hsub).trans ?_
      rw [volume_interval hd hF hτ', hsp, hw0']
    have hT : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (√((w 0 + ε) ^ 2 - spatialSq w) ^ (d + 1)) * V)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : Continuous fun ε : ℝ => ENNReal.ofReal (√((w 0 + ε) ^ 2 - spatialSq w) ^ (d + 1)) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      have h1 := hc.tendsto 0
      have h2 : ENNReal.ofReal (√((w 0 + 0) ^ 2 - spatialSq w) ^ (d + 1)) = 0 := by
        rw [add_zero, ← h0]; simp
      rw [h2] at h1
      have h3 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (√((w 0 + ε) ^ 2 - spatialSq w) ^ (d + 1)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := h1.mono_left nhdsWithin_le_nhds
      have := ENNReal.Tendsto.mul_const h3 (Or.inr (volume_diamond_lt_top d).ne)
      simpa using this
    have := ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
    exact le_antisymm this bot_le
  · exact volume_interval hd hw hpos

end Lightlike.CausalSets
