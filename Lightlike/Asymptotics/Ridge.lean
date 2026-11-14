import Lightlike.Asymptotics.Valley

/-!
# The vertical line through the saddle is a ridge

Let `ψ = phaseC A B` with `ΣAᵢ = ΣBₖ`, and let `x + iy₀` (`y₀ > 0`) be a critical point of `ψ`.
Along the vertical line `x + iy`, `y > 0`, the real part of `ψ` has a strict minimum at `y = y₀`
(`re_phaseC_vertical_gt`). For a Euclidean tetrahedron this applies to the saddle point
(`IsEuclid.re_phaseC_vertical_gt`): every other point of the open upper half-plane with the same
real part as the saddle has `Re ψ > Re ψ(s)` (`IsEuclid.re_phaseC_saddle_lt_of_re_eq`). A path on
which `Re ψ < Re ψ(s)`, such as a descent path from the saddle, therefore never crosses this line.

## The argument

Write `Θ(y) = Im ψ'(x + iy)`, so that `d/dy Re ψ(x + iy) = −Θ(y)`
(`hasDerivAt_re_phaseC_vertical`). It suffices that `Θ > 0` on `(0, y₀)` and `Θ < 0` on `(y₀, ∞)`
(`im_dphaseC_vertical_sign`).

* `exp ψ'(z) = z ∏ₖ (z − Bₖ) / ∏ᵢ (z − Aᵢ)` gives
  `sin Θ(y) · e^{Re ψ'} |∏ᵢ (z − Aᵢ)|² = y C(y²)` for an explicit polynomial `C = ridgePoly`
  (`sin_im_dphaseC_vertical`). Its `t³` coefficient is `ΣAᵢ − ΣBₖ`, so under the balance `C` is
  a quadratic (`ridgePoly_eq`).
* `Θ(y₀) = 0`, so `C(y₀²) = 0`. As `y → ∞` every argument tends to `π/2` and `Θ(y) → −2π`
  (`tendsto_im_dphaseC_vertical`), so `Θ` takes the value `−π` at some `y₁ > y₀`, and `C(y₁²) = 0`.
  Between them `Θ` takes the value `−π/2`, where `sin Θ < 0`; this forces the leading coefficient
  of `C = c₂ (t − y₀²)(t − y₁²)` to be positive.
* Hence `sin Θ > 0` on `(0, y₀)`, `sin Θ < 0` on `(y₀, y₁)` and `sin Θ > 0` on `(y₁, ∞)`, and the
  intermediate value theorem turns these into the signs of `Θ`.

No bound on `Θ` beyond its limit at infinity is needed.
-/

open Complex Filter Topology Set
open scoped Real

namespace Lightlike.Asymptotics

/-! ## The polynomial `C` -/

/-- First elementary symmetric function of four reals. -/
def esym1 (p : Fin 4 → ℝ) : ℝ := p 0 + p 1 + p 2 + p 3

/-- Second elementary symmetric function of four reals. -/
def esym2 (p : Fin 4 → ℝ) : ℝ :=
  p 0 * p 1 + p 0 * p 2 + p 0 * p 3 + p 1 * p 2 + p 1 * p 3 + p 2 * p 3

/-- Third elementary symmetric function of four reals. -/
def esym3 (p : Fin 4 → ℝ) : ℝ :=
  p 0 * p 1 * p 2 + p 0 * p 1 * p 3 + p 0 * p 2 * p 3 + p 1 * p 2 * p 3

/-- Fourth elementary symmetric function of four reals. -/
def esym4 (p : Fin 4 → ℝ) : ℝ := p 0 * p 1 * p 2 * p 3

/-- `∏ⱼ (pⱼ + iy)` has real part `e₄ − e₂y² + y⁴` and imaginary part `e₃y − e₁y³`. -/
lemma prod_add_mul_I (p : Fin 4 → ℝ) (y : ℝ) :
    (∏ j, ((p j : ℂ) + y * I)).re = esym4 p - esym2 p * y ^ 2 + y ^ 4 ∧
      (∏ j, ((p j : ℂ) + y * I)).im = esym3 p * y - esym1 p * y ^ 3 := by
  simp only [Fin.prod_univ_four, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    esym1, esym2, esym3, esym4]
  constructor <;> ring

/-- The atoms `x, x − B₀, x − B₁, x − B₂` of the numerator `z ∏ₖ (z − Bₖ)` at `z = x + iy`. -/
def ridgeNum (B : Fin 3 → ℝ) (x : ℝ) : Fin 4 → ℝ := ![x, x - B 0, x - B 1, x - B 2]

/-- The atoms `x − Aᵢ` of the denominator `∏ᵢ (z − Aᵢ)` at `z = x + iy`. -/
def ridgeDen (A : Fin 4 → ℝ) (x : ℝ) : Fin 4 → ℝ := fun i => x - A i

/-- The polynomial `C(t)` with `sin Θ · e^{Re ψ'} |∏ᵢ (z − Aᵢ)|² = y C(y²)` at `z = x + iy`, where
`Θ = Im ψ'(z)` (`sin_im_dphaseC_vertical`). In terms of the atoms `p = ridgeNum B x` and
`a = ridgeDen A x` it is `(e₃(p) − e₁(p) t)(e₄(a) − e₂(a) t + t²) − (e₄(p) − e₂(p) t + t²)(e₃(a) − e₁(a) t)`. -/
def ridgePoly (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x t : ℝ) : ℝ :=
  (esym3 (ridgeNum B x) - esym1 (ridgeNum B x) * t) *
      (esym4 (ridgeDen A x) - esym2 (ridgeDen A x) * t + t ^ 2) -
    (esym4 (ridgeNum B x) - esym2 (ridgeNum B x) * t + t ^ 2) *
      (esym3 (ridgeDen A x) - esym1 (ridgeDen A x) * t)

/-- The `t²` coefficient of `ridgePoly` (its leading coefficient when `ΣAᵢ = ΣBₖ`). -/
def ridgeC2 (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) : ℝ :=
  esym3 (ridgeNum B x) + esym1 (ridgeNum B x) * esym2 (ridgeDen A x) - esym3 (ridgeDen A x) -
    esym2 (ridgeNum B x) * esym1 (ridgeDen A x)

/-- The `t` coefficient of `ridgePoly`. -/
def ridgeC1 (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) : ℝ :=
  esym2 (ridgeNum B x) * esym3 (ridgeDen A x) + esym4 (ridgeNum B x) * esym1 (ridgeDen A x) -
    esym2 (ridgeDen A x) * esym3 (ridgeNum B x) - esym1 (ridgeNum B x) * esym4 (ridgeDen A x)

/-- The constant coefficient of `ridgePoly`. -/
def ridgeC0 (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) : ℝ :=
  esym3 (ridgeNum B x) * esym4 (ridgeDen A x) - esym4 (ridgeNum B x) * esym3 (ridgeDen A x)

/-- Under the balance the two families of atoms have the same sum: `x + Σₖ (x − Bₖ) = Σᵢ (x − Aᵢ)`. -/
lemma esym1_ridgeNum {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k) (x : ℝ) :
    esym1 (ridgeNum B x) = esym1 (ridgeDen A x) := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_three] at hbal
  simp only [esym1, ridgeNum, ridgeDen, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  linarith

/-- Under the balance `ΣAᵢ = ΣBₖ` the `t³` term of `ridgePoly` cancels and `C` is a quadratic. -/
theorem ridgePoly_eq {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k) (x t : ℝ) :
    ridgePoly A B x t = ridgeC2 A B x * t ^ 2 + ridgeC1 A B x * t + ridgeC0 A B x := by
  have h := esym1_ridgeNum hbal x
  simp only [ridgePoly, ridgeC2, ridgeC1, ridgeC0]
  linear_combination (-(t ^ 3)) * h

/-! ## The sign of `sin Θ` -/

/-- `sin (Im ψ'(z)) · e^{Re ψ'(z)} |∏ᵢ (z − Aᵢ)|² = Im (u · conj v)` on the open upper half-plane,
with `u = z ∏ₖ (z − Bₖ)` and `v = ∏ᵢ (z − Aᵢ)`, from `exp ψ' = u / v`. -/
lemma sin_im_dphaseC_mul (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    Real.sin (dphaseC A B z).im * (Real.exp (dphaseC A B z).re * normSq (∏ i, (z - A i))) =
      (z * ∏ k, (z - B k)).im * (∏ i, (z - A i)).re -
        (z * ∏ k, (z - B k)).re * (∏ i, (z - A i)).im := by
  have hv : ∏ i, (z - A i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => slitPlane_ne_zero (mem_slitPlane_sub hz (A i))
  have hN : normSq (∏ i, (z - A i)) ≠ 0 := (normSq_pos.2 hv).ne'
  have h := congrArg Complex.im (exp_dphaseC A B hz)
  rw [exp_im, div_im] at h
  rw [← mul_assoc, mul_comm (Real.sin _), h, sub_mul, div_mul_cancel₀ _ hN, div_mul_cancel₀ _ hN]

/-- **The sign link.** On the vertical line `z = x + iy`, `y > 0`,
`sin Θ · e^{Re ψ'(z)} |∏ᵢ (z − Aᵢ)|² = y C(y²)` with `Θ = Im ψ'(z)` and `C = ridgePoly A B x`. -/
theorem sin_im_dphaseC_vertical (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Real.sin (dphaseC A B (x + y * I)).im *
        (Real.exp (dphaseC A B (x + y * I)).re * normSq (∏ i, ((x : ℂ) + y * I - A i))) =
      y * ridgePoly A B x (y ^ 2) := by
  have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  rw [sin_im_dphaseC_mul A B hz]
  have hnum : ((x : ℂ) + y * I) * ∏ k, ((x : ℂ) + y * I - B k) =
      ∏ j, ((ridgeNum B x j : ℂ) + y * I) := by
    simp only [Fin.prod_univ_four, Fin.prod_univ_three, ridgeNum, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    push_cast
    ring
  have hden : ∏ i, ((x : ℂ) + y * I - A i) = ∏ j, ((ridgeDen A x j : ℂ) + y * I) :=
    Finset.prod_congr rfl fun i _ => by simp only [ridgeDen]; push_cast; ring
  obtain ⟨hn1, hn2⟩ := prod_add_mul_I (ridgeNum B x) y
  obtain ⟨hd1, hd2⟩ := prod_add_mul_I (ridgeDen A x) y
  rw [hnum, hden, hn1, hn2, hd1, hd2]
  simp only [ridgePoly]
  ring

/-! ## `Θ` along the vertical line: continuity, limit, and the derivative of `Re ψ` -/

/-- `Im ψ'(z) = arg z − Σᵢ arg (z − Aᵢ) + Σₖ arg (z − Bₖ) − 2π`. -/
lemma im_dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) :
    (dphaseC A B z).im = arg z - ∑ i, arg (z - A i) + ∑ k, arg (z - B k) - 2 * π := by
  simp [dphaseC, log_im, im_sum]

/-- `arg (x + iy − c) → π/2` as `y → ∞`. -/
lemma tendsto_arg_vertical (x c : ℝ) :
    Tendsto (fun y : ℝ => arg ((x : ℂ) + y * I - c)) atTop (𝓝 (π / 2)) := by
  have h0 : Tendsto (fun y : ℝ => (x - c) / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun y : ℝ => (((x - c) / y : ℝ) : ℂ) + I) atTop (𝓝 I) := by
    have := ((continuous_ofReal.tendsto 0).comp h0).add_const I
    simpa using this
  have h2 := (continuousAt_arg (mem_slitPlane_of_im_pos (by simp))).tendsto.comp h1
  rw [arg_I] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hxy : (x : ℂ) + y * I - c = (y : ℝ) * ((((x - c) / y : ℝ) : ℂ) + I) := by
    push_cast
    rw [mul_add, mul_div_cancel₀ _ hy']
    ring
  simp only [Function.comp_apply]
  rw [hxy, arg_real_mul _ hy]

/-- `Im ψ'(x + iy) → −2π` as `y → ∞`: each of the eight arguments tends to `π/2`. -/
theorem tendsto_im_dphaseC_vertical (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) :
    Tendsto (fun y : ℝ => (dphaseC A B (x + y * I)).im) atTop (𝓝 (-2 * π)) := by
  have h0 : Tendsto (fun y : ℝ => arg ((x : ℂ) + y * I)) atTop (𝓝 (π / 2)) := by
    simpa using tendsto_arg_vertical x 0
  have h := ((h0.sub (tendsto_finsetSum (f := fun i (y : ℝ) => arg ((x : ℂ) + y * I - A i))
    Finset.univ fun i _ => tendsto_arg_vertical x (A i))).add
    (tendsto_finsetSum (f := fun k (y : ℝ) => arg ((x : ℂ) + y * I - B k))
      Finset.univ fun k _ => tendsto_arg_vertical x (B k))).sub_const (2 * π)
  have hlim : π / 2 - ∑ _i : Fin 4, π / 2 + ∑ _k : Fin 3, π / 2 - 2 * π = -2 * π := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hlim] at h
  exact h.congr fun y => (im_dphaseC A B _).symm

/-- `y ↦ Im ψ'(x + iy)` is continuous on `y > 0`. -/
lemma continuousOn_im_dphaseC_vertical (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) :
    ContinuousOn (fun y : ℝ => (dphaseC A B (x + y * I)).im) (Ioi 0) := fun y hy => by
  have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  have h1 : ContinuousAt (fun t : ℝ => (x : ℂ) + t * I) y := by fun_prop
  have h2 : ContinuousAt (fun t : ℝ => dphaseC A B ((x : ℂ) + t * I)) y :=
    ContinuousAt.comp (g := dphaseC A B) (f := fun t : ℝ => (x : ℂ) + t * I)
      (hasDerivAt_dphaseC A B hz).continuousAt h1
  exact (continuous_im.continuousAt.comp h2).continuousWithinAt

/-- `d/dy Re ψ(x + iy) = −Im ψ'(x + iy)` for `y > 0`. -/
lemma hasDerivAt_re_phaseC_vertical (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (phaseC A B (x + t * I)).re) (-(dphaseC A B (x + y * I)).im) y := by
  have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  have hp : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_phaseC A B hz).comp y hp)
  convert h using 1 <;> simp [Function.comp_def]

/-! ## The sign of `Θ` and the ridge -/

/-- **The sign of `Im ψ'` on the vertical line through a critical point.** If `ΣAᵢ = ΣBₖ` and
`ψ'(x + iy₀) = 0` with `y₀ > 0`, then `Im ψ'(x + iy) > 0` for `0 < y < y₀` and `Im ψ'(x + iy) < 0`
for `y > y₀`. -/
theorem im_dphaseC_vertical_sign {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k)
    {x y₀ : ℝ} (hy₀ : 0 < y₀) (hs : dphaseC A B (x + y₀ * I) = 0) :
    (∀ y, 0 < y → y < y₀ → 0 < (dphaseC A B (x + y * I)).im) ∧
      ∀ y, y₀ < y → (dphaseC A B (x + y * I)).im < 0 := by
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ → ℝ, Θ = fun y : ℝ => (dphaseC A B (x + y * I)).im := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ → ℝ, C = fun t => ridgeC2 A B x * t ^ 2 + ridgeC1 A B x * t +
      ridgeC0 A B x := ⟨_, rfl⟩
  have hpi := Real.pi_pos
  -- the sign link `sin Θ(y) · K = y C(y²)` with `K > 0`
  have hlink : ∀ y, 0 < y → ∃ K, 0 < K ∧ Real.sin (Θ y) * K = y * C (y ^ 2) := by
    intro y hy
    refine ⟨Real.exp (dphaseC A B (x + y * I)).re * normSq (∏ i, ((x : ℂ) + y * I - A i)),
      mul_pos (Real.exp_pos _) (normSq_pos.2 ?_), ?_⟩
    · exact Finset.prod_ne_zero_iff.2 fun i _ =>
        slitPlane_ne_zero (mem_slitPlane_sub (by simpa using hy) (A i))
    · simp only [hΘ, hC]
      rw [← ridgePoly_eq hbal]
      exact sin_im_dphaseC_vertical A B x hy
  have hzero : ∀ y, 0 < y → Real.sin (Θ y) = 0 → C (y ^ 2) = 0 := fun y hy h0 => by
    obtain ⟨K, -, hk⟩ := hlink y hy
    rw [h0, zero_mul] at hk
    exact (mul_eq_zero.1 hk.symm).resolve_left hy.ne'
  have hnegC : ∀ y, 0 < y → Real.sin (Θ y) < 0 → C (y ^ 2) < 0 := fun y hy h0 => by
    obtain ⟨K, hK, hk⟩ := hlink y hy
    by_contra hc
    nlinarith [mul_neg_of_neg_of_pos h0 hK, mul_nonneg hy.le (not_lt.1 hc)]
  have hpos : ∀ y, 0 < y → 0 < C (y ^ 2) → 0 < Real.sin (Θ y) := fun y hy h0 => by
    obtain ⟨K, hK, hk⟩ := hlink y hy
    by_contra hc
    nlinarith [mul_pos hy h0, mul_nonneg (neg_nonneg.2 (not_lt.1 hc)) hK.le]
  have hneg : ∀ y, 0 < y → C (y ^ 2) < 0 → Real.sin (Θ y) < 0 := fun y hy h0 => by
    obtain ⟨K, hK, hk⟩ := hlink y hy
    by_contra hc
    nlinarith [mul_neg_of_pos_of_neg hy h0, mul_nonneg (not_lt.1 hc) hK.le]
  have hcont : ∀ a b, 0 < a → ContinuousOn Θ (Icc a b) := fun a b ha => by
    rw [hΘ]
    exact (continuousOn_im_dphaseC_vertical A B x).mono fun t ht => lt_of_lt_of_le ha ht.1
  have hΘ0 : Θ y₀ = 0 := by simp [hΘ, hs]
  have hC0 : C (y₀ ^ 2) = 0 := hzero y₀ hy₀ (by rw [hΘ0, Real.sin_zero])
  -- a point `Y > y₀` with `Θ(Y) < −π`, from `Θ → −2π`
  have hlim : Tendsto Θ atTop (𝓝 (-2 * π)) := by
    rw [hΘ]; exact tendsto_im_dphaseC_vertical A B x
  obtain ⟨Y, hY1, hY2⟩ :=
    ((hlim.eventually (gt_mem_nhds (show -2 * π < -π by linarith))).and
      (eventually_gt_atTop y₀)).exists
  -- `y₁ ∈ (y₀, Y)` with `Θ(y₁) = −π`
  obtain ⟨y₁, ⟨hy₁a, -⟩, hy₁⟩ := intermediate_value_Icc' hY2.le (hcont y₀ Y hy₀)
    (show -π ∈ Icc (Θ Y) (Θ y₀) from ⟨hY1.le, by rw [hΘ0]; linarith⟩)
  have hy₀₁ : y₀ < y₁ := lt_of_le_of_ne hy₁a fun h => by rw [← h, hΘ0] at hy₁; linarith
  have hC1 : C (y₁ ^ 2) = 0 :=
    hzero y₁ (by linarith) (by rw [hy₁, Real.sin_neg, Real.sin_pi, neg_zero])
  -- `yh ∈ (y₀, y₁)` with `Θ(yh) = −π/2`
  obtain ⟨yh, ⟨hyha, hyhb⟩, hyh⟩ := intermediate_value_Icc' hy₀₁.le (hcont y₀ y₁ hy₀)
    (show -(π / 2) ∈ Icc (Θ y₁) (Θ y₀) from ⟨by rw [hy₁]; linarith, by rw [hΘ0]; linarith⟩)
  have hyh0 : y₀ < yh := lt_of_le_of_ne hyha fun h => by rw [← h, hΘ0] at hyh; linarith
  have hyh1 : yh < y₁ := lt_of_le_of_ne hyhb fun h => by rw [h, hy₁] at hyh; linarith
  have hCh : C (yh ^ 2) < 0 :=
    hnegC yh (by linarith) (by rw [hyh, Real.sin_neg, Real.sin_pi_div_two]; norm_num)
  -- `C = c₂ (t − y₀²)(t − y₁²)` with `c₂ > 0`
  have ht01 : y₀ ^ 2 < y₁ ^ 2 := by nlinarith
  simp only [hC] at hC0 hC1
  have e1 : ridgeC1 A B x = -ridgeC2 A B x * (y₀ ^ 2 + y₁ ^ 2) := by
    have h : (y₀ ^ 2 - y₁ ^ 2) * (ridgeC2 A B x * (y₀ ^ 2 + y₁ ^ 2) + ridgeC1 A B x) = 0 := by
      linear_combination hC0 - hC1
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (sub_ne_zero.2 ht01.ne)
    · linarith
  have e0 : ridgeC0 A B x = ridgeC2 A B x * y₀ ^ 2 * y₁ ^ 2 := by
    linear_combination hC0 - y₀ ^ 2 * e1
  have hfac : ∀ t, C t = ridgeC2 A B x * ((t - y₀ ^ 2) * (t - y₁ ^ 2)) := fun t => by
    simp only [hC]
    linear_combination t * e1 + e0
  have hc2 : 0 < ridgeC2 A B x := by
    have h1 : y₀ ^ 2 < yh ^ 2 := by nlinarith
    have h2 : yh ^ 2 < y₁ ^ 2 := by nlinarith
    rw [hfac] at hCh
    nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]
  -- the signs of `sin Θ`
  have hsin_lo : ∀ y, 0 < y → y < y₀ → 0 < Real.sin (Θ y) := fun y hy hyl =>
    hpos y hy (by
      rw [hfac]
      exact mul_pos hc2 (mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)))
  have hsin_mid : ∀ y, y₀ < y → y < y₁ → Real.sin (Θ y) < 0 := fun y hy hyl =>
    hneg y (by linarith) (by
      rw [hfac]
      exact mul_neg_of_pos_of_neg hc2 (mul_neg_of_pos_of_neg (by nlinarith) (by nlinarith)))
  have hsin_hi : ∀ y, y₁ < y → 0 < Real.sin (Θ y) := fun y hy =>
    hpos y (by linarith) (by
      rw [hfac]
      exact mul_pos hc2 (mul_pos (by nlinarith) (by nlinarith)))
  -- the signs of `Θ`
  have hlo : ∀ y, 0 < y → y < y₀ → 0 < Θ y := by
    intro y hy hyl
    by_contra hle
    have hle' := not_lt.1 hle
    have hlt : Θ y < -π := by
      by_contra h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hle' (not_lt.1 h)
      linarith [hsin_lo y hy hyl]
    obtain ⟨y', ⟨h1, h2⟩, hy'⟩ := intermediate_value_Icc hyl.le (hcont y y₀ hy)
      (show -π ∈ Icc (Θ y) (Θ y₀) from ⟨hlt.le, by rw [hΘ0]; linarith⟩)
    have hy'0 : y' < y₀ := lt_of_le_of_ne h2 fun h => by rw [h, hΘ0] at hy'; linarith
    have := hsin_lo y' (by linarith) hy'0
    rw [hy', Real.sin_neg, Real.sin_pi, neg_zero] at this
    exact lt_irrefl _ this
  have hhi : ∀ y, y₀ < y → Θ y < 0 := by
    intro y hy
    rcases lt_trichotomy y y₁ with h | h | h
    · by_contra hge
      have hge' := not_lt.1 hge
      have hgt : π < Θ y := by
        by_contra h'
        have := Real.sin_nonneg_of_nonneg_of_le_pi hge' (not_lt.1 h')
        linarith [hsin_mid y hy h]
      obtain ⟨y', ⟨h1, h2⟩, hy'⟩ := intermediate_value_Icc hy.le (hcont y₀ y hy₀)
        (show π ∈ Icc (Θ y₀) (Θ y) from ⟨by rw [hΘ0]; linarith, hgt.le⟩)
      have hy'0 : y₀ < y' := lt_of_le_of_ne h1 fun h => by rw [← h, hΘ0] at hy'; linarith
      have := hsin_mid y' hy'0 (by linarith)
      rw [hy', Real.sin_pi] at this
      exact lt_irrefl _ this
    · rw [h, hy₁]; linarith
    · by_contra hge
      have hge' := not_lt.1 hge
      obtain ⟨y', ⟨h1, -⟩, hy'⟩ := intermediate_value_Icc h.le (hcont y₁ y (by linarith))
        (show -(π / 2) ∈ Icc (Θ y₁) (Θ y) from ⟨by rw [hy₁]; linarith, by linarith⟩)
      have hy'1 : y₁ < y' := lt_of_le_of_ne h1 fun h => by rw [← h, hy₁] at hy'; linarith
      have := hsin_hi y' hy'1
      rw [hy', Real.sin_neg, Real.sin_pi_div_two] at this
      linarith
  refine ⟨fun y hy hyl => ?_, fun y hy => ?_⟩
  · have := hlo y hy hyl; rw [hΘ] at this; exact this
  · have := hhi y hy; rw [hΘ] at this; exact this

/-- **The vertical line through a critical point is a ridge.** If `ΣAᵢ = ΣBₖ` and `ψ'(x + iy₀) = 0`
with `y₀ > 0`, then `Re ψ(x + iy) > Re ψ(x + iy₀)` for every `y > 0` with `y ≠ y₀`. -/
theorem re_phaseC_vertical_gt {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k)
    {x y₀ : ℝ} (hy₀ : 0 < y₀) (hs : dphaseC A B (x + y₀ * I) = 0) {y : ℝ} (hy : 0 < y)
    (hne : y ≠ y₀) : (phaseC A B (x + y₀ * I)).re < (phaseC A B (x + y * I)).re := by
  obtain ⟨hlo, hhi⟩ := im_dphaseC_vertical_sign hbal hy₀ hs
  have hd := fun t (ht : 0 < t) => hasDerivAt_re_phaseC_vertical A B x ht
  rcases lt_or_gt_of_ne hne with h | h
  · have hanti : StrictAntiOn (fun t : ℝ => (phaseC A B (x + t * I)).re) (Ioc 0 y₀) := by
      refine strictAntiOn_of_deriv_neg (convex_Ioc 0 y₀)
        (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt) fun t ht => ?_
      rw [interior_Ioc] at ht
      rw [(hd t ht.1).deriv]
      linarith [hlo t ht.1 ht.2]
    exact hanti ⟨hy, h.le⟩ ⟨hy₀, le_rfl⟩ h
  · have hmono : StrictMonoOn (fun t : ℝ => (phaseC A B (x + t * I)).re) (Ici y₀) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici y₀)
        (fun t ht => (hd t (lt_of_lt_of_le hy₀ ht)).continuousAt.continuousWithinAt)
        fun t ht => ?_
      rw [interior_Ici] at ht
      rw [(hd t (lt_trans hy₀ ht)).deriv]
      linarith [hhi t ht]
    exact hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

/-- For a Euclidean tetrahedron with saddle point `s = x₀ + iy₀`,
`Re ψ(x₀ + iy) > Re ψ(s)` for every `y > 0` with `y ≠ y₀`. -/
theorem IsEuclid.re_phaseC_vertical_gt {l : Fin 6 → ℝ} (h : IsEuclid l) {y : ℝ} (hy : 0 < y)
    (hne : y ≠ (saddle l).im) :
    (phaseC (faceSum l) (quadSum l) (saddle l)).re <
      (phaseC (faceSum l) (quadSum l) ((saddle l).re + y * I)).re := by
  have hd := h.dphaseC_saddle
  rw [← re_add_im (saddle l)] at hd
  have := Lightlike.Asymptotics.re_phaseC_vertical_gt (sum_faceSum_eq_sum_quadSum l) h.saddle_im_pos hd
    hy hne
  rwa [re_add_im] at this

/-- **Descent paths cannot cross the vertical line through the saddle.** For a Euclidean
tetrahedron, a point `z ≠ s` of the open upper half-plane with `Re z = Re s` has `Re ψ(z) > Re ψ(s)`. -/
theorem IsEuclid.re_phaseC_saddle_lt_of_re_eq {l : Fin 6 → ℝ} (h : IsEuclid l) {z : ℂ}
    (hz : 0 < z.im) (hre : z.re = (saddle l).re) (hne : z ≠ saddle l) :
    (phaseC (faceSum l) (quadSum l) (saddle l)).re < (phaseC (faceSum l) (quadSum l) z).re := by
  have him : z.im ≠ (saddle l).im := fun him => hne (Complex.ext hre him)
  have := h.re_phaseC_vertical_gt hz him
  rwa [← hre, re_add_im] at this

end Lightlike.Asymptotics
