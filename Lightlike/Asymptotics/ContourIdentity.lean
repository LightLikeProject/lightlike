import Lightlike.Asymptotics.Assembly
import Mathlib

/-!
# The contour identity for Racah's sum

Racah's alternating sum is the sum of the residues of a meromorphic kernel, and so a contour
integral. For face sums `a : Fin 4 → ℕ` and quadrilateral sums `b : Fin 3 → ℕ` the kernel is
  `f(z) = π T(z) / sin(π z)`,
  `T(z) = ∏_{j ≤ a₀} (z − a₀ + 1 + j) · ∏_{i ≥ 1} 1/Γ(z − aᵢ + 1) · ∏ₖ 1/Γ(bₖ − z + 1)`
(`racahKernel`, `racahT`). The polynomial factor is `Γ(z + 2)/Γ(z − a₀ + 1)` written so that `T` is
entire (`racahT_eq_Gamma` gives the Γ form on the upper half-plane). At an integer `t` the
residue of `f` is `(−1)^t T(t)` (`tendsto_mul_racahKernel`), and `(−1)^t T(t)` is Racah's term
`(−1)^t (t+1)! / (∏ᵢ (t − aᵢ)! ∏ₖ (bₖ − t)!)` (`racahT_natCast`), which vanishes unless
`max aᵢ ≤ t ≤ min bₖ`.

The identity is stated with a primitive rather than a path integral (`racahSum_eq_im_primitive`):
for real `x₁ < max aᵢ` and `x₂ > min bₖ` there is a function `Φ` with `Φ' = f` on the closed upper
half-plane minus the integers, and
  `racahSum J = −Im (Φ(x₂) − Φ(x₁)) / π`.
So `racahSum J = −(1/π) Im ∫_P f` along every path `P` from `x₁` to `x₂` through the upper
half-plane. The proof (`exists_primitive_im_sub`) subtracts the principal parts `cₙ/(z − n)`: the
remainder has removable singularities at the integers (`exists_differentiable_eq_of_tendsto`), so
it is entire and has an entire primitive `G`, whose imaginary part is constant on `ℝ` because the
remainder is real there. The principal parts are integrated by `cₙ log(−i(z − n))`, a logarithm
with its cut pointing down from `n`; its imaginary part drops by `π` from `x₁ < n` to `x₂ > n`.
This is the representation that the saddle-point analysis deforms through the saddle.

The numerical cross-check is `scripts/asymptotics/contour_identity_check.py`.
-/

open Complex Set Filter Topology Finset PhyslibAlpha.Sl2
open scoped Real

namespace Lightlike.Asymptotics

/-- `sin (π z)` vanishes only at the integers. -/
lemma sin_pi_mul_ne_zero {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : Complex.sin (π * z) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hz n
  apply mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [hn]; ring

/-- `sin (π n) = 0` at every integer `n`. -/
lemma sin_pi_mul_intCast (n : ℤ) : Complex.sin (π * n) = 0 :=
  Complex.sin_eq_zero_iff.mpr ⟨n, by ring⟩

/-- The integers form a closed subset of `ℂ`, the zero set of `sin (π z)`. -/
lemma isClosed_setOf_intCast : IsClosed {z : ℂ | ∃ n : ℤ, z = n} := by
  have e : {z : ℂ | ∃ n : ℤ, z = n} = (fun z : ℂ => Complex.sin (π * z)) ⁻¹' {0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact sin_pi_mul_intCast n
    · intro h
      by_contra hz
      exact sin_pi_mul_ne_zero (fun n hn => hz ⟨n, hn⟩) h
  rw [e]
  exact isClosed_singleton.preimage (Complex.continuous_sin.comp (continuous_const.mul continuous_id))

/-- The only integer in the disc of radius `1/2` around an integer `n` is `n`. -/
lemma eq_of_intCast_mem_ball {n k : ℤ} (h : (k : ℂ) ∈ Metric.ball (n : ℂ) (1 / 2)) : k = n := by
  have h' : ‖((k - n : ℤ) : ℂ)‖ < 1 / 2 := by
    rw [Int.cast_sub]
    rwa [Metric.mem_ball, dist_eq_norm] at h
  rw [Complex.norm_intCast] at h'
  by_contra hne
  have h1 : (1 : ℝ) ≤ |((k - n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
  linarith

/-- **Removable singularities at the integers.** A function holomorphic off the integers with
`(z − n) h(z) → 0` at every integer `n` agrees off the integers with an entire function. -/
lemma exists_differentiable_eq_of_tendsto {h : ℂ → ℂ}
    (hd : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → DifferentiableAt ℂ h z)
    (ho : ∀ n : ℤ, Tendsto (fun z => (z - n) * h z) (𝓝[≠] (n : ℂ)) (𝓝 0)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → g z = h z := by
  classical
  let Z : Set ℂ := {z | ∃ n : ℤ, z = n}
  let g : ℂ → ℂ := fun z => if z ∈ Z then limUnder (𝓝[≠] z) h else h z
  have hgo : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → g z = h z := fun z hz => by
    have : z ∉ Z := fun ⟨n, hn⟩ => hz n hn
    simp only [g, this, ite_false]
  refine ⟨g, fun z => ?_, hgo⟩
  by_cases hz : z ∈ Z
  · obtain ⟨n, rfl⟩ := hz
    have hball : ∀ w ∈ Metric.ball (n : ℂ) (1 / 2), w ≠ n → ∀ k : ℤ, w ≠ k := by
      intro w hw hwn k hk
      subst hk
      exact hwn (by rw [eq_of_intCast_mem_ball hw])
    have hB : Metric.ball (n : ℂ) (1 / 2) ∈ 𝓝 (n : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hdiff : DifferentiableOn ℂ (Function.update h n (limUnder (𝓝[≠] (n : ℂ)) h))
        (Metric.ball (n : ℂ) (1 / 2)) := by
      refine Complex.differentiableOn_update_limUnder_of_isLittleO hB
        (fun w hw => (hd w (hball w hw.1 hw.2)).differentiableWithinAt) ?_
      rw [Asymptotics.isLittleO_iff_tendsto' ?_]
      · have h1 : Tendsto (fun z => (z - n) * h n) (𝓝[≠] (n : ℂ)) (𝓝 0) := by
          have : Tendsto (fun z : ℂ => (z - n) * h n) (𝓝 (n : ℂ)) (𝓝 (((n : ℂ) - n) * h n)) :=
            ((continuous_id.sub continuous_const).mul continuous_const).tendsto _
          rw [sub_self, zero_mul] at this
          exact this.mono_left nhdsWithin_le_nhds
        have := (ho n).sub h1
        rw [sub_zero] at this
        refine this.congr fun z => ?_
        rw [div_inv_eq_mul]; ring
      · filter_upwards [self_mem_nhdsWithin] with z hz h0
        exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))
    have hev : g =ᶠ[𝓝 (n : ℂ)] Function.update h n (limUnder (𝓝[≠] (n : ℂ)) h) := by
      filter_upwards [hB] with w hw
      by_cases hwn : w = n
      · subst hwn
        have hn : (n : ℂ) ∈ Z := ⟨n, rfl⟩
        simp only [g, hn, ite_true, Function.update_self]
      · rw [Function.update_of_ne hwn]
        exact hgo w (hball w hw hwn)
    exact (hdiff.differentiableAt hB).congr_of_eventuallyEq hev
  · have hz' : ∀ n : ℤ, z ≠ n := fun n hn => hz ⟨n, hn⟩
    have hev : g =ᶠ[𝓝 z] h := by
      filter_upwards [isClosed_setOf_intCast.isOpen_compl.mem_nhds hz] with w hw
      exact hgo w fun n hn => hw ⟨n, hn⟩
    exact (hd z hz').congr_of_eventuallyEq hev

/-- The imaginary part of the logarithm with downward cut, `log(−i(x − n))`, is `π/2` at real
`x < n`. -/
lemma im_log_neg_I_mul_of_lt {n : ℤ} {x : ℝ} (h : x < n) :
    (Complex.log (-I * ((x : ℂ) - n))).im = π / 2 := by
  rw [Complex.log_im, show -I * ((x : ℂ) - n) = ((n - x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.arg_real_mul _ (by linarith), Complex.arg_I]

/-- The imaginary part of `log(−i(x − n))` is `−π/2` at real `x > n`. -/
lemma im_log_neg_I_mul_of_gt {n : ℤ} {x : ℝ} (h : (n : ℝ) < x) :
    (Complex.log (-I * ((x : ℂ) - n))).im = -(π / 2) := by
  rw [Complex.log_im, show -I * ((x : ℂ) - n) = ((x - n : ℝ) : ℂ) * (-I) by push_cast; ring,
    Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]

/-- `−i(z − n)` lies in the slit plane for `z` in the closed upper half-plane, `z ≠ n`. -/
lemma neg_I_mul_sub_mem_slitPlane {n : ℤ} {z : ℂ} (hz : 0 ≤ z.im) (hn : z ≠ n) :
    -I * (z - n) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  simp only [mul_re, neg_re, I_re, zero_mul, sub_re, intCast_re, neg_im, I_im,
    sub_im, intCast_im, sub_zero, mul_im, zero_add, neg_mul, one_mul, zero_sub]
  rcases hz.lt_or_eq with hz | hz
  · left; simpa using hz
  · right
    intro h
    apply hn
    apply Complex.ext
    · simp only [intCast_re]; linarith
    · simp only [intCast_im]; linarith

/-- **Principal parts and a primitive.** Let `f` be holomorphic off the integers, with real
residues `cₙ` (`(z − n) f(z) → cₙ`) that vanish outside a finite set `M`, and real on the real
axis. For real `x₁ < M < x₂` there is a primitive `Φ` of `f` on the closed upper half-plane minus
the integers, continuous on the closed upper half-plane minus `M`, with
`Im (Φ(x₂) − Φ(x₁)) = −π Σ_{n ∈ M} cₙ`. -/
theorem exists_primitive_im_sub {f : ℂ → ℂ} {c : ℤ → ℂ} {M : Finset ℤ} {x₁ x₂ : ℝ}
    (hd : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → DifferentiableAt ℂ f z)
    (hres : ∀ n : ℤ, Tendsto (fun z => (z - n) * f z) (𝓝[≠] (n : ℂ)) (𝓝 (c n)))
    (hM : ∀ n, n ∉ M → c n = 0) (hc : ∀ n, (c n).im = 0)
    (hreal : ∀ x : ℝ, (∀ n : ℤ, (x : ℂ) ≠ n) → (f x).im = 0)
    (h₁ : ∀ n ∈ M, x₁ < n) (h₂ : ∀ n ∈ M, (n : ℝ) < x₂) :
    ∃ Φ : ℂ → ℂ, (∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) → HasDerivAt Φ (f z) z) ∧
      (∀ z : ℂ, 0 ≤ z.im → (∀ n ∈ M, z ≠ n) → ContinuousAt Φ z) ∧
      (Φ x₂ - Φ x₁).im = -π * ∑ n ∈ M, (c n).re := by
  classical
  set h : ℂ → ℂ := fun z => f z - ∑ m ∈ M, c m / (z - m) with hh
  have hdh : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → DifferentiableAt ℂ h z := fun z hz => by
    refine (hd z hz).sub (DifferentiableAt.fun_sum fun m _ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
      (sub_ne_zero.mpr (hz m))
  have hoh : ∀ n : ℤ, Tendsto (fun z => (z - n) * h z) (𝓝[≠] (n : ℂ)) (𝓝 0) := fun n => by
    have hterm : ∀ m ∈ M, Tendsto (fun z => (z - n) * (c m / (z - m))) (𝓝[≠] (n : ℂ))
        (𝓝 (if m = n then c m else 0)) := by
      intro m _
      by_cases hmn : m = n
      · subst hmn
        rw [ite_eq_left rfl]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        field_simp [sub_ne_zero.mpr hz]
      · rw [ite_eq_right hmn]
        have hnm : (n : ℂ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hmn)
        have : ContinuousAt (fun z => (z - n) * (c m / (z - m))) (n : ℂ) :=
          (continuousAt_id.sub continuousAt_const).mul
            (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hnm)
        have := this.tendsto
        rw [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
    have hsum := tendsto_finsetSum M hterm
    rw [Finset.sum_ite_eq'] at hsum
    have hcn : (if n ∈ M then c n else 0) = c n := by
      split_ifs with hn
      · rfl
      · exact (hM n hn).symm
    rw [hcn] at hsum
    have := (hres n).sub hsum
    rw [sub_self] at this
    refine this.congr fun z => ?_
    simp only [h, mul_sub, Finset.mul_sum]
  obtain ⟨g, hg, hgh⟩ := exists_differentiable_eq_of_tendsto hdh hoh
  obtain ⟨G, hG⟩ := hg.isExactOn_univ
  have hlog : ∀ z : ℂ, 0 ≤ z.im → ∀ m ∈ M, z ≠ m →
      HasDerivAt (fun z => c m * Complex.log (-I * (z - m))) (c m * (1 / (z - m))) z := by
    intro z hz m _ hzm
    have hm : z - m ≠ 0 := sub_ne_zero.mpr hzm
    have := ((((hasDerivAt_id z).sub_const (m : ℂ)).const_mul (-I)).clog
      (neg_I_mul_sub_mem_slitPlane hz hzm)).const_mul (c m)
    refine this.congr_deriv ?_
    simp only [mul_one, id]
    field_simp [I_ne_zero]
  refine ⟨fun z => G z + ∑ m ∈ M, c m * Complex.log (-I * (z - m)), ?_, ?_, ?_⟩
  · intro z hz hzn
    refine ((hG z (mem_univ _)).add
      (HasDerivAt.fun_sum fun m hm => hlog z hz m hm (hzn m))).congr_deriv ?_
    rw [hgh z hzn]
    simp only [h, mul_one_div, sub_add_cancel]
  · intro z hz hzM
    exact (hG z (mem_univ _)).continuousAt.add
      (HasDerivAt.fun_sum fun m hm => hlog z hz m hm (hzM m hm)).continuousAt
  · -- `Im g = 0` on the real axis, so `Im G` is constant there
    have hgr : ∀ x : ℝ, (g x).im = 0 := by
      have hcont : Continuous fun x : ℝ => (g x).im :=
        Complex.continuous_im.comp (hg.continuous.comp Complex.continuous_ofReal)
      have hdense : Dense {x : ℝ | ∀ n : ℤ, (x : ℂ) ≠ n} := by
        have hD := (countable_range (Int.cast : ℤ → ℝ)).dense_compl ℝ
        convert hD using 1
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
        refine forall_congr' fun n => ?_
        rw [Ne, eq_comm, ← Complex.ofReal_intCast, Complex.ofReal_inj]
      have := hcont.ext_on hdense continuous_const fun x hx => by
        simp only
        rw [hgh x hx, hh, sub_im, hreal x hx, im_sum, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [div_im, hc m]
        simp
      exact fun x => congrFun this x
    have hder : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (G t).im) (g x).im x := fun x => by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hG x (mem_univ _)).comp_ofReal
      simpa [Function.comp_def] using this
    have hGr : (G x₂).im = (G x₁).im :=
      is_const_of_deriv_eq_zero (fun x => (hder x).differentiableAt)
        (fun x => by rw [(hder x).deriv, hgr x]) x₂ x₁
    have key : ∀ m ∈ M, (c m * (Complex.log (-I * ((x₂ : ℂ) - m)) -
        Complex.log (-I * ((x₁ : ℂ) - m)))).im = -π * (c m).re := by
      intro m hm
      rw [mul_im, hc m, zero_mul, add_zero, sub_im, im_log_neg_I_mul_of_gt (h₂ m hm),
        im_log_neg_I_mul_of_lt (h₁ m hm)]
      ring
    have hΦ : (G x₂ + ∑ m ∈ M, c m * Complex.log (-I * ((x₂ : ℂ) - m))) -
        (G x₁ + ∑ m ∈ M, c m * Complex.log (-I * ((x₁ : ℂ) - m))) = (G x₂ - G x₁) +
        ∑ m ∈ M, c m * (Complex.log (-I * ((x₂ : ℂ) - m)) -
          Complex.log (-I * ((x₁ : ℂ) - m))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    simp only
    rw [hΦ, add_im, im_sum, Finset.sum_congr rfl key, ← Finset.mul_sum, sub_im, hGr, sub_self,
      zero_add]

/-! ### Racah's kernel -/

/-- The entire numerator of Racah's kernel,
`T(z) = ∏_{j ≤ a₀} (z − a₀ + 1 + j) · ∏_{i ≥ 1} 1/Γ(z − aᵢ + 1) · ∏ₖ 1/Γ(bₖ − z + 1)`.
The polynomial factor is `Γ(z + 2)/Γ(z − a₀ + 1)` (`racahT_eq_Gamma`), written as a product so
that `T` has no junk values at the poles of that quotient. -/
noncomputable def racahT (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ range (a 0 + 1), (z - a 0 + 1 + j)) *
    (∏ i : Fin 3, (Complex.Gamma (z - a i.succ + 1))⁻¹) * ∏ k, (Complex.Gamma (b k - z + 1))⁻¹

/-- **Racah's kernel** `π T(z) / sin(π z)`, meromorphic with at most simple poles at the
integers; its residue at `t` is Racah's `t`-th term. (At the integers themselves the division
by `sin (π t) = 0` gives the junk value `0`; only the limits there are used.) -/
noncomputable def racahKernel (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (z : ℂ) : ℂ :=
  π * racahT a b z / Complex.sin (π * z)

/-- `T` is entire. -/
lemma differentiable_racahT (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) : Differentiable ℂ (racahT a b) := by
  intro z
  have hG : ∀ w : ℂ → ℂ, Differentiable ℂ w →
      DifferentiableAt ℂ (fun z => (Complex.Gamma (w z))⁻¹) z :=
    fun w hw => (Complex.differentiable_one_div_Gamma (w z)).comp z (hw z)
  exact ((DifferentiableAt.fun_finsetProd fun j _ => by fun_prop).mul
    (DifferentiableAt.fun_finsetProd fun i _ => hG _ (by fun_prop))).mul
    (DifferentiableAt.fun_finsetProd fun k _ => hG _ (by fun_prop))

/-- `Γ(w + n) = (∏_{j < n} (w + j)) Γ(w)` when none of `w, …, w + n − 1` is zero. -/
lemma Gamma_add_nat_eq_prod_mul {w : ℂ} {n : ℕ} (hw : ∀ j < n, w + j ≠ 0) :
    Complex.Gamma (w + n) = (∏ j ∈ range n, (w + j)) * Complex.Gamma w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (hw n (Nat.lt_succ_self n)),
      ih fun j hj => hw j (by omega), prod_range_succ]
    ring

/-- The polynomial factor of `T` times `Γ(z − a₀ + 1)` is `Γ(z + 2)`. -/
lemma prod_mul_Gamma_eq {z : ℂ} {a₀ : ℕ} (hz : ∀ j ≤ a₀, z - a₀ + 1 + j ≠ 0) :
    (∏ j ∈ range (a₀ + 1), (z - a₀ + 1 + j)) * Complex.Gamma (z - a₀ + 1) =
      Complex.Gamma (z + 2) := by
  rw [← Gamma_add_nat_eq_prod_mul fun j hj => hz j (by omega)]
  congr 1
  push_cast
  ring

/-- **The Γ form of `T`** on the upper half-plane:
`T(z) = Γ(z + 2) ∏ᵢ 1/Γ(z − aᵢ + 1) ∏ₖ 1/Γ(bₖ − z + 1)`. -/
theorem racahT_eq_Gamma (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {z : ℂ} (hz : 0 < z.im) :
    racahT a b z = Complex.Gamma (z + 2) * (∏ i, (Complex.Gamma (z - a i + 1))⁻¹) *
      ∏ k, (Complex.Gamma (b k - z + 1))⁻¹ := by
  have hne : ∀ j : ℕ, z - a 0 + 1 + j ≠ 0 := fun j h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : Complex.Gamma (z - a 0 + 1) ≠ 0 := Complex.Gamma_ne_zero fun m h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [racahT, Fin.prod_univ_succ (n := 3), ← prod_mul_Gamma_eq fun j _ => hne j]
  field_simp

/-- `1/Γ(m + 1) = 1/m!` at every integer `m`, and `0` for `m < 0` (Physlib's `invFact`). -/
lemma inv_Gamma_intCast_add_one (m : ℤ) :
    (Complex.Gamma ((m : ℂ) + 1))⁻¹ = (invFact m : ℂ) := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [invFact_of_neg hm, Complex.ofReal_zero]
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -(m + 1) by omega)
    rw [show (m : ℂ) + 1 = -(k : ℂ) by
      rw [show (k : ℂ) = ((k : ℤ) : ℂ) by norm_cast, ← hk]; push_cast; ring,
      Complex.Gamma_neg_nat_eq_zero, inv_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [invFact_natCast, Int.cast_natCast, Complex.Gamma_nat_eq_factorial]
    push_cast
    rfl

/-- The polynomial factor of `T` at a natural number `t` is `(t + 1)!/(t − a₀)!`, and `0` for
`t < a₀`. -/
lemma prod_natCast_eq (a₀ t : ℕ) :
    ∏ j ∈ range (a₀ + 1), ((t : ℂ) - a₀ + 1 + j) =
      ((t + 1).factorial : ℂ) * (invFact ((t : ℤ) - a₀) : ℂ) := by
  rcases le_or_gt a₀ t with h | h
  · have hpos : ∀ j ≤ a₀, (t : ℂ) - a₀ + 1 + j ≠ 0 := fun j _ => by
      rw [show (t : ℂ) - a₀ + 1 + j = ((t - a₀ + 1 + j : ℕ) : ℂ) by push_cast [h]; ring]
      exact_mod_cast (by omega : t - a₀ + 1 + j ≠ 0)
    have hG1 : Complex.Gamma ((t : ℂ) - a₀ + 1) = ((t - a₀).factorial : ℂ) := by
      rw [show (t : ℂ) - a₀ + 1 = ((t - a₀ : ℕ) : ℂ) + 1 by push_cast [h]; ring]
      exact Complex.Gamma_nat_eq_factorial _
    have hG2 : Complex.Gamma ((t : ℂ) + 2) = ((t + 1).factorial : ℂ) := by
      rw [show (t : ℂ) + 2 = ((t + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
      exact Complex.Gamma_nat_eq_factorial _
    have key := prod_mul_Gamma_eq hpos
    rw [hG1, hG2] at key
    have hF : ((t - a₀).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [invFact_eq (show (t : ℤ) - a₀ = ((t - a₀ : ℕ) : ℤ) by omega), ← key]
    push_cast
    field_simp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [invFact_of_neg (by omega), Complex.ofReal_zero, mul_zero]
    refine prod_eq_zero (i := d) (mem_range.mpr (by omega)) ?_
    push_cast
    ring

/-- **`T` at a natural number `t`** is `(t + 1)! ∏ᵢ 1/(t − aᵢ)! ∏ₖ 1/(bₖ − t)!`, so that
`(−1)^t T(t)` is the `t`-th term of Racah's sum. -/
theorem racahT_natCast (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (t : ℕ) :
    racahT a b t = ((t + 1).factorial : ℂ) * (∏ i, (invFact ((t : ℤ) - a i) : ℂ)) *
      ∏ k, (invFact ((b k : ℤ) - t) : ℂ) := by
  have e1 : ∀ i : Fin 3, (Complex.Gamma ((t : ℂ) - a i.succ + 1))⁻¹ =
      (invFact ((t : ℤ) - a i.succ) : ℂ) := fun i => by
    rw [← inv_Gamma_intCast_add_one]
    push_cast
    rfl
  have e2 : ∀ k : Fin 3, (Complex.Gamma ((b k : ℂ) - t + 1))⁻¹ =
      (invFact ((b k : ℤ) - t) : ℂ) := fun k => by
    rw [← inv_Gamma_intCast_add_one]
    push_cast
    rfl
  rw [racahT, prod_natCast_eq, Fin.prod_univ_succ (n := 3)]
  simp only [e1, e2]
  ring

/-- `T` vanishes at the negative integers, through the factor `1/Γ(z − a₁ + 1)`. -/
lemma racahT_intCast_of_neg (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {n : ℤ} (hn : n < 0) :
    racahT a b n = 0 := by
  have h0 : (∏ i : Fin 3, (Complex.Gamma ((n : ℂ) - a i.succ + 1))⁻¹) = 0 := by
    refine prod_eq_zero (i := 0) (mem_univ _) ?_
    rw [show (n : ℂ) - (a (Fin.succ 0) : ℂ) + 1 = ((n - a (Fin.succ 0) : ℤ) : ℂ) + 1 by
      push_cast; ring, inv_Gamma_intCast_add_one, invFact_of_neg (by omega), Complex.ofReal_zero]
  rw [racahT, h0, mul_zero, zero_mul]

/-- `T` is real on the real axis. -/
lemma racahT_ofReal (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (x : ℝ) :
    racahT a b x = ((∏ j ∈ range (a 0 + 1), (x - a 0 + 1 + j)) *
      (∏ i : Fin 3, (Real.Gamma (x - a i.succ + 1))⁻¹) *
        ∏ k, (Real.Gamma (b k - x + 1))⁻¹ : ℝ) := by
  simp only [racahT, ofReal_mul, ofReal_prod, ofReal_inv, ← Complex.Gamma_ofReal, ofReal_add,
    ofReal_sub, ofReal_natCast, ofReal_one]

/-- Racah's kernel is real on the real axis. -/
lemma racahKernel_ofReal_im (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (x : ℝ) :
    (racahKernel a b x).im = 0 := by
  rw [racahKernel, racahT_ofReal, show (π : ℂ) * x = ((π * x : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_sin, ← ofReal_mul, ← ofReal_div, ofReal_im]

/-- `cos (π n) = (−1)ⁿ` at every integer `n`. -/
lemma cos_pi_mul_intCast (n : ℤ) : Complex.cos (π * n) = (-1) ^ n := by
  rw [show (π : ℂ) * n = ((n * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Real.cos_int_mul_pi]
  push_cast
  rfl

/-- **The residues of Racah's kernel**: `(z − n) f(z) → (−1)ⁿ T(n)` at every integer `n`. -/
theorem tendsto_mul_racahKernel (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (n : ℤ) :
    Tendsto (fun z => (z - n) * racahKernel a b z) (𝓝[≠] (n : ℂ))
      (𝓝 ((-1) ^ n * racahT a b n)) := by
  have hs : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * n) * (π * 1)) n :=
    ((hasDerivAt_id' (n : ℂ)).const_mul (π : ℂ)).csin
  have hcos := cos_pi_mul_intCast n
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : Complex.cos (π * n) * (π * 1) ≠ 0 := by
    rw [hcos, mul_one]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hπ
  have hT : Tendsto (fun z => (π : ℂ) * racahT a b z) (𝓝[≠] (n : ℂ)) (𝓝 (π * racahT a b n)) :=
    ((continuous_const.mul (differentiable_racahT a b).continuous).tendsto _).mono_left
      nhdsWithin_le_nhds
  have hlim := hT.mul ((hasDerivAt_iff_tendsto_slope.mp hs).inv₀ hne)
  have hval : (π : ℂ) * racahT a b n * (Complex.cos (π * n) * (π * 1))⁻¹ =
      (-1) ^ n * racahT a b n := by
    have h1 : ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n := by rw [← inv_zpow, inv_neg, inv_one]
    rw [hcos, mul_one, mul_inv, h1]
    field_simp
  rw [hval] at hlim
  refine hlim.congr fun z => ?_
  rw [slope_def_field, sin_pi_mul_intCast, sub_zero, inv_div, racahKernel]
  ring

/-! ### The contour identity -/

/-- **The contour identity for Racah's sum.** For real `x₁` left of some face sum and `x₂` right
of some quadrilateral sum, Racah's kernel has a primitive `Φ` on the closed upper half-plane
minus the integers, continuous at `x₁` and `x₂` (which may be integers), with
`racahSum J = −Im (Φ(x₂) − Φ(x₁)) / π`. Hence
`racahSum J = −(1/π) Im ∫_P f` along every path `P` from `x₁` to `x₂` in the upper half-plane. -/
theorem racahSum_eq_im_primitive (J : Fin 6 → ℕ) {x₁ x₂ : ℝ} (h₁ : ∃ i, x₁ < faceN J i)
    (h₂ : ∃ k, (quadN J k : ℝ) < x₂) :
    ∃ Φ : ℂ → ℂ, (∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) →
        HasDerivAt Φ (racahKernel (faceN J) (quadN J) z) z) ∧
      ContinuousAt Φ x₁ ∧ ContinuousAt Φ x₂ ∧ racahSum J = -(Φ x₂ - Φ x₁).im / π := by
  classical
  set a := faceN J with ha
  set b := quadN J with hb
  obtain ⟨i₀, hi₀⟩ := h₁
  obtain ⟨k₀, hk₀⟩ := h₂
  set M : Finset ℤ :=
    ((range (b 0 + 1)).filter fun t => (∀ i, a i ≤ t) ∧ ∀ k, t ≤ b k).map Nat.castEmbedding
    with hM
  have hzero : ∀ t : ℕ, ¬ ((∀ i, a i ≤ t) ∧ ∀ k, t ≤ b k) →
      (-1 : ℝ) ^ t * ((t + 1).factorial : ℝ) * (∏ i, invFact ((t : ℤ) - a i)) *
        ∏ k, invFact ((b k : ℤ) - t) = 0 := by
    intro t ht
    simp only [not_and_or, not_forall, not_le] at ht
    rcases ht with ⟨i, hi⟩ | ⟨k, hk⟩
    · rw [prod_eq_zero (mem_univ i) (invFact_of_neg (by omega))]
      ring
    · rw [prod_eq_zero (mem_univ k) (invFact_of_neg (by omega))]
      ring
  have hval : ∀ t : ℕ, (-1 : ℂ) ^ (t : ℤ) * racahT a b ((t : ℤ) : ℂ) =
      (((-1 : ℝ) ^ t * ((t + 1).factorial : ℝ) * (∏ i, invFact ((t : ℤ) - a i)) *
        ∏ k, invFact ((b k : ℤ) - t) : ℝ) : ℂ) := by
    intro t
    rw [Int.cast_natCast, racahT_natCast, zpow_natCast]
    push_cast
    ring
  have hMz : ∀ n, n ∉ M → (-1 : ℂ) ^ n * racahT a b n = 0 := by
    intro n hn
    rcases lt_or_ge n 0 with hneg | hnn
    · rw [racahT_intCast_of_neg a b hneg, mul_zero]
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
      have ht : ¬ ((∀ i, a i ≤ t) ∧ ∀ k, t ≤ b k) := by
        intro hp
        apply hn
        simp only [hM, Finset.mem_map, Finset.mem_filter, Finset.mem_range, Nat.castEmbedding_apply]
        exact ⟨t, ⟨by have := hp.2 0; omega, hp⟩, rfl⟩
      rw [hval t, hzero t ht, ofReal_zero]
  have hc : ∀ n : ℤ, ((-1 : ℂ) ^ n * racahT a b n).im = 0 := by
    intro n
    rw [← Complex.ofReal_intCast n, racahT_ofReal,
      show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_zpow, ← ofReal_mul, ofReal_im]
  have hMt : ∀ n ∈ M, ∃ t : ℕ, n = t ∧ (∀ i, a i ≤ t) ∧ ∀ k, t ≤ b k := by
    intro n hn
    simp only [hM, Finset.mem_map, Finset.mem_filter, Nat.castEmbedding_apply] at hn
    obtain ⟨t, ⟨-, hp⟩, rfl⟩ := hn
    exact ⟨t, rfl, hp⟩
  have h1 : ∀ n ∈ M, x₁ < n := by
    intro n hn
    obtain ⟨t, rfl, hp, -⟩ := hMt n hn
    have : (a i₀ : ℝ) ≤ t := by exact_mod_cast hp i₀
    push_cast
    linarith
  have h2 : ∀ n ∈ M, (n : ℝ) < x₂ := by
    intro n hn
    obtain ⟨t, rfl, -, hp⟩ := hMt n hn
    have : (t : ℝ) ≤ b k₀ := by exact_mod_cast hp k₀
    push_cast
    linarith
  have hdk : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → DifferentiableAt ℂ (racahKernel a b) z := fun z hz =>
    ((differentiable_racahT a b z).const_mul _).div (by fun_prop) (sin_pi_mul_ne_zero hz)
  obtain ⟨Φ, hΦ, hΦc, him⟩ := exists_primitive_im_sub (c := fun n => (-1) ^ n * racahT a b n)
    (M := M) hdk (tendsto_mul_racahKernel a b) hMz hc (fun x _ => racahKernel_ofReal_im a b x) h1 h2
  refine ⟨Φ, hΦ, hΦc _ (by simp) fun n hn e => (h1 n hn).ne (by exact_mod_cast e),
    hΦc _ (by simp) fun n hn e => (h2 n hn).ne' (by exact_mod_cast e), ?_⟩
  rw [him, neg_mul, neg_neg, mul_div_cancel_left₀ _ Real.pi_ne_zero, hM, sum_map]
  simp only [Nat.castEmbedding_apply, hval, ofReal_re]
  rw [sum_filter_of_ne fun t _ ht => by_contra fun hp => ht (hzero t hp), racahSum]

end Lightlike.Asymptotics
