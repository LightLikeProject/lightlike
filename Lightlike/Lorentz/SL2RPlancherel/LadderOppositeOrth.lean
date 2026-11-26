import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KTypeOpposite

/-!
# The discrete directions of the opposite-sign blocks are orthogonal to the ladder images

For natural `l, s` and `m = min(l, s)`, the functions
`φ_i(ξ) = (cosh ξ - 1)^{i+s} / sinh^{l+s} ξ`, `l - m ≤ i ≤ l - 1`, are orthogonal in
`L²((0, ∞), sinh ξ dξ)` to every opposite-sign ladder image `hLRN s G l` of a radial generator.  In
`v = cosh ξ` the pairing is `∫₁^∞ (v - 1)^i (d/dv)^l ((v - 1)^s G^{(s)}) dv`, which vanishes by `l`
integrations by parts (`integral_pow_mul_iteratedDeriv_eq_zero`): the function vanishes to order `s`
at `v = 1` and `i ≥ l - s`.  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Repeated integration by parts against `(v - 1)^i`**: if `f` is smooth, all its derivatives
vanish at `B ≥ 1` and its derivatives of order `< s` vanish at `1`, then
`∫₁^B (v - 1)^i f^{(l)}(v) dv = 0` whenever `l - s ≤ i < l`. -/
theorem integral_pow_mul_iteratedDeriv_eq_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {B : ℝ}
    (hB : ∀ j, iteratedDeriv j f B = 0) {s : ℕ} (h1 : ∀ j, j < s → iteratedDeriv j f 1 = 0) :
    ∀ i l : ℕ, l ≤ i + s → i < l →
      ∫ v in (1 : ℝ)..B, (((v - 1) ^ i : ℝ) : ℂ) * iteratedDeriv l f v = 0 := by
  have hd : ∀ k x, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := fun k x => by
    rw [iteratedDeriv_succ]
    exact (((contDiff_iteratedDeriv_infty hf k).differentiable (by simp)) x).hasDerivAt
  have hc : ∀ k, Continuous (iteratedDeriv k f) := fun k =>
    (contDiff_iteratedDeriv_infty hf k).continuous
  intro i
  induction i with
  | zero =>
    intro l hl hl0
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [pow_zero, Complex.ofReal_one, one_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd k x)
      ((hc (k + 1)).intervalIntegrable _ _), hB k, h1 k (by omega), sub_zero]
  | succ i ih =>
    intro l hl hil
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    have hu : ∀ x ∈ uIcc (1 : ℝ) B, HasDerivAt (fun v : ℝ => (((v - 1) ^ (i + 1) : ℝ) : ℂ))
        ((((i + 1 : ℕ) : ℝ) * (x - 1) ^ i : ℝ) : ℂ) x := fun x _ => by
      have := (((hasDerivAt_id x).sub_const 1).pow (i + 1)).ofReal_comp
      simpa using this
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ => hd k x)
      ((Complex.continuous_ofReal.comp (continuous_const.mul
        ((continuous_id.sub continuous_const).pow i))).intervalIntegrable _ _)
      ((hc (k + 1)).intervalIntegrable _ _)
    rw [hibp, hB k]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero i), Complex.ofReal_zero, zero_mul, mul_zero,
      sub_zero, zero_sub]
    have hrest : ∫ x in (1 : ℝ)..B, ((((i + 1 : ℕ) : ℝ) * (x - 1) ^ i : ℝ) : ℂ) * iteratedDeriv k f x =
        (((i + 1 : ℕ) : ℝ) : ℂ) * ∫ x in (1 : ℝ)..B, (((x - 1) ^ i : ℝ) : ℂ) * iteratedDeriv k f x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast; ring
    rw [hrest, ih k (by omega) (by omega), mul_zero, neg_zero]

/-- **The moments of `f^{(l)}` against `(v - 1)^i` are boundary values**: if `f` is smooth and all
its derivatives vanish at `B ≥ 1`, then for `i < l`,
`∫₁^B (v - 1)^i f^{(l)}(v) dv = (-1)^(i+1) i! f^{(l-1-i)}(1)`. -/
theorem integral_pow_mul_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {B : ℝ}
    (hB : ∀ j, iteratedDeriv j f B = 0) :
    ∀ i l : ℕ, i < l →
      ∫ v in (1 : ℝ)..B, (((v - 1) ^ i : ℝ) : ℂ) * iteratedDeriv l f v =
        (-1) ^ (i + 1) * (i.factorial : ℂ) * iteratedDeriv (l - 1 - i) f 1 := by
  have hd : ∀ k x, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := fun k x => by
    rw [iteratedDeriv_succ]
    exact (((contDiff_iteratedDeriv_infty hf k).differentiable (by simp)) x).hasDerivAt
  have hc : ∀ k, Continuous (iteratedDeriv k f) := fun k =>
    (contDiff_iteratedDeriv_infty hf k).continuous
  intro i
  induction i with
  | zero =>
    intro l hl0
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [pow_zero, Complex.ofReal_one, one_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd k x)
      ((hc (k + 1)).intervalIntegrable _ _), hB k]
    simp
  | succ i ih =>
    intro l hil
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    have hu : ∀ x ∈ uIcc (1 : ℝ) B, HasDerivAt (fun v : ℝ => (((v - 1) ^ (i + 1) : ℝ) : ℂ))
        ((((i + 1 : ℕ) : ℝ) * (x - 1) ^ i : ℝ) : ℂ) x := fun x _ => by
      have := (((hasDerivAt_id x).sub_const 1).pow (i + 1)).ofReal_comp
      simpa using this
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ => hd k x)
      ((Complex.continuous_ofReal.comp (continuous_const.mul
        ((continuous_id.sub continuous_const).pow i))).intervalIntegrable _ _)
      ((hc (k + 1)).intervalIntegrable _ _)
    rw [hibp, hB k]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero i), Complex.ofReal_zero, zero_mul, mul_zero,
      sub_zero, zero_sub]
    have hrest : ∫ x in (1 : ℝ)..B, ((((i + 1 : ℕ) : ℝ) * (x - 1) ^ i : ℝ) : ℂ) * iteratedDeriv k f x =
        (((i + 1 : ℕ) : ℝ) : ℂ) * ∫ x in (1 : ℝ)..B, (((x - 1) ^ i : ℝ) : ℂ) * iteratedDeriv k f x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast; ring
    rw [hrest, ih k (by omega), Nat.factorial_succ]
    have e : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
    rw [e]
    push_cast
    ring

/-- **A smooth function whose `n`-th derivative vanishes on an interval is its Taylor polynomial
there**: for `c ∈ (a, b)` and `x ∈ (a, b)`, `h x = Σ_{j<n} h^{(j)}(c)/j! (x - c)^j`. -/
theorem eq_taylor_of_iteratedDeriv_eq_zero {a b c : ℝ} (hc : c ∈ Ioo a b) :
    ∀ n : ℕ, ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → (∀ x ∈ Ioo a b, iteratedDeriv n h x = 0) →
      ∀ x ∈ Ioo a b, h x = ∑ j ∈ Finset.range n,
        iteratedDeriv j h c / (j.factorial : ℂ) * ((x : ℂ) - c) ^ j := by
  intro n
  induction n with
  | zero => intro h _ hn x hx; simpa using hn x hx
  | succ n ih =>
    intro h hh hn
    have hdh : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
    have hd := ih (deriv h) hdh fun x hx => by rw [← iteratedDeriv_succ']; exact hn x hx
    set T : ℝ → ℂ := fun x => ∑ j ∈ Finset.range (n + 1),
      iteratedDeriv j h c / (j.factorial : ℂ) * ((x : ℂ) - c) ^ j with hT
    -- the derivative of the Taylor polynomial
    have hTd : ∀ x : ℝ, HasDerivAt T (∑ j ∈ Finset.range n,
        iteratedDeriv j (deriv h) c / (j.factorial : ℂ) * ((x : ℂ) - c) ^ j) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) - c) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp.sub_const (c : ℂ)
      have hsum := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun j _ =>
        (hlin.pow j).const_mul (iteratedDeriv j h c / (j.factorial : ℂ)))
      convert hsum using 1
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
        add_tsub_cancel_right, mul_one]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← iteratedDeriv_succ', Nat.factorial_succ]
      push_cast
      field_simp
    have hD : ∀ x ∈ Ioo a b, HasDerivAt (fun y => h y - T y) 0 x := by
      intro x hx
      have h1 : HasDerivAt h (deriv h x) x := ((hh.differentiable (by simp)) x).hasDerivAt
      have := h1.sub (hTd x)
      rw [hd x hx, sub_self] at this
      exact this
    have hTc : T c = h c := by
      simp only [hT, sub_self]
      rw [Finset.sum_range_succ']
      simp
    intro x hx
    have hsub : uIcc c x ⊆ Ioo a b := (convex_Ioo a b).ordConnected.uIcc_subset hc hx
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => h y - T y)
      (fun y hy => hD y (hsub hy)) (intervalIntegrable_const (c := (0 : ℂ)))
    simp only [intervalIntegral.integral_zero, hTc, sub_self] at hint
    have h2 := hint.symm
    rw [sub_zero] at h2
    exact sub_eq_zero.mp h2

/-- A continuous complex function vanishing on `[B, ∞)` is integrable on `[0, ∞)`. -/
lemma integrableOn_Ici_of_zero_complex {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : 0 < B)
    (hz : ∀ ξ : ℝ, B ≤ ξ → f ξ = 0) : IntegrableOn f (Ici (0 : ℝ)) := by
  have h1 : IntegrableOn f (Icc (0 : ℝ) B) := hf.integrableOn_Icc
  have h2 : IntegrableOn f (Ioi B) :=
    (integrableOn_zero (s := Ioi B)).congr_fun (fun ξ hξ => (hz ξ hξ.le).symm) measurableSet_Ioi
  have hset : Ici (0 : ℝ) = Icc 0 B ∪ Ioi B := by
    ext x
    simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro hx
      rcases le_or_gt x B with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, _⟩ | h)
      · exact hx
      · linarith
  rw [hset]
  exact h1.union h2

/-- **The discrete directions** `φ_i(ξ) = (cosh ξ - 1)^{i+s} / sinh^{l+s} ξ` of the opposite-sign
block `(l, -s)`. -/
def phiN (s l i : ℕ) (ξ : ℝ) : ℝ := (Real.cosh ξ - 1) ^ (i + s) / Real.sinh ξ ^ (l + s)

/-- **The opposite-sign ladder images are orthogonal to the discrete directions**: for
`l - s ≤ i < l` and `G` smooth with compact support,
`∫₀^∞ hLRN s G l · φ_i · sinh ξ dξ = 0` (`φ_i` is real). -/
theorem integral_hLRN_mul_phiN (s l i : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (hli : l ≤ i + s) (hil : i < l) :
    ∫ ξ in Ioi (0 : ℝ), hLRN s G l ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) = 0 := by
  set f : ℝ → ℂ := oppGen s G with hf
  have hfs : ContDiff ℝ ∞ f := contDiff_oppGen s hG
  set P : ℝ → ℂ := iteratedDeriv l f with hP
  set g : ℝ → ℂ := fun v => (((v - 1) ^ i : ℝ) : ℂ) * P v with hg
  -- a radius beyond which `G`, `f` and its derivatives vanish
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hGR : ∀ v, R < v → G v = 0 := fun v hv => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self v]
  have hfR : ∀ v, R < v → f v = 0 := by
    intro v hv
    have hev : G =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using hGR w hw
    simp [hf, oppGen, hev.iteratedDeriv_eq]
  have hfder : ∀ j v, R < v → iteratedDeriv j f v = 0 := by
    intro j v hv
    have hev : f =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using hfR w hw
    rw [hev.iteratedDeriv_eq]
    simp
  set B : ℝ := max R 1 + 1 with hBdef
  have hB1 : 1 ≤ B := by have := le_max_right R 1; linarith
  have hRB : R < B := by have := le_max_left R 1; linarith
  -- the integrand in `v = cosh ξ`
  have hpt : ∀ ξ ∈ Ioi (0 : ℝ), hLRN s G l ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) =
      Real.sinh ξ • g (Real.cosh ξ) := by
    intro ξ hξ
    have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.2 (ne_of_gt hξ)
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have hc0 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 hc1).ne'
    rw [hLRN_eq s hG l ξ hξ, uRecN_eq s hG l _ hc1]
    have hreal : Real.sinh ξ ^ (l + s) * (Real.cosh ξ - 1) ^ (-(s : ℤ)) * phiN s l i ξ * Real.sinh ξ =
        (Real.cosh ξ - 1) ^ i * Real.sinh ξ := by
      rw [phiN, zpow_neg, zpow_natCast]
      field_simp
      ring
    calc _ = (((Real.sinh ξ ^ (l + s) * (Real.cosh ξ - 1) ^ (-(s : ℤ)) * phiN s l i ξ *
          Real.sinh ξ : ℝ)) : ℂ) * P (Real.cosh ξ) := by push_cast; ring
      _ = _ := by rw [hreal, hg, Complex.real_smul]; push_cast; ring
  -- continuity and support of `g`
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).pow i)).mul
      (contDiff_iteratedDeriv_infty hfs l).continuous
  have hgR : ∀ v, R < v → g v = 0 := fun v hv => by simp [hg, hP, hfder l v hv]
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun v hv => ?_
    rcases not_and_or.mp hv with h | h
    · -- `v < -B`: `G`, hence `f` and `g`, vanish near `v`
      have hv' : v < -R := by have := le_max_left R 1; linarith [not_le.mp h]
      have hGv : ∀ w, w < -R → G w = 0 := fun w hw => image_eq_zero_of_notMem_tsupport fun h => by
        have := hR h
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
        linarith [neg_abs_le w]
      have hev : f =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hv'] with w hw
        have hevG : G =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
          filter_upwards [Iio_mem_nhds hw] with u hu using hGv u hu
        simp [hf, oppGen, hevG.iteratedDeriv_eq]
      simp [hg, hP, hev.iteratedDeriv_eq]
    · exact hgR v (by linarith [not_le.mp h])
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgcs
  have hcomp : Continuous (fun ξ => Real.sinh ξ • g (Real.cosh ξ)) :=
    Real.continuous_sinh.smul (hgc.comp Real.continuous_cosh)
  have hz : ∀ ξ : ℝ, 2 * B ≤ ξ → Real.sinh ξ • g (Real.cosh ξ) = 0 := by
    intro ξ hξ
    have := cosh_ge_half ξ
    rw [hgR _ (by linarith), smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hmain := integral_deriv_smul_comp_Ioi (f := Real.cosh) (f' := Real.sinh) (g := g) (a := 0)
    Real.continuous_cosh.continuousOn tendsto_cosh_atTop
    (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt) hgc.continuousOn hgi.integrableOn
    (integrableOn_Ici_of_zero_complex hcomp (by linarith) hz)
  simp only [Function.comp_def] at hmain
  rw [hmain, Real.cosh_zero]
  have hzero : ∀ v ∈ Ioi (1 : ℝ) \ Ioc 1 B, g v = 0 := by
    intro v hv
    have : B < v := by
      by_contra h
      exact hv.2 ⟨hv.1, not_lt.mp h⟩
    exact hgR v (by linarith)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero,
    ← intervalIntegral.integral_of_le hB1]
  exact integral_pow_mul_iteratedDeriv_eq_zero hfs (fun j => hfder j B hRB)
    (fun j hj => by rw [iteratedDeriv_oppGen s hG j hj.le]; simp [Nat.sub_ne_zero_of_lt hj]) i l hli hil

/-- Trust check: the discrete direction of the block `(1, -1)` is `1 / (1 + cosh ξ)` (the lowest
`K`-type profile of the discrete series `D₂`), for `ξ > 0`. -/
theorem phiN_one_one_zero {ξ : ℝ} (hξ : 0 < ξ) : phiN 1 1 0 ξ = 1 / (1 + Real.cosh ξ) := by
  have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.2 (ne_of_gt hξ)
  have hsq : Real.sinh ξ ^ 2 = (Real.cosh ξ - 1) * (Real.cosh ξ + 1) := by
    have := Real.cosh_sq_sub_sinh_sq ξ; nlinarith
  have hc0 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 hc1).ne'
  have hc2 : 1 + Real.cosh ξ ≠ 0 := by linarith
  rw [phiN, show (1 + 1 : ℕ) = 2 from rfl, hsq]
  field_simp
  ring

/-- Non-vacuity: the hypotheses of `integral_hLRN_mul_phiN` hold for the block `(1, -1)`, `i = 0`. -/
example : ∫ ξ in Ioi (0 : ℝ), hLRN 1 (fun _ => (0 : ℂ)) 1 ξ * ((phiN 1 1 0 ξ : ℝ) : ℂ) *
    (Real.sinh ξ : ℂ) = 0 :=
  integral_hLRN_mul_phiN 1 1 0 contDiff_const HasCompactSupport.zero le_rfl one_pos

end Lightlike.Lorentz.SL2RPlancherel
