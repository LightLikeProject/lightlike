import Mathlib

/-!
# The Riemann function profile of the Klein–Gordon operator on `1+1` Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For a real number `c` (later `c = -m²/4`) put
`besselPhi c z = ∑ₖ cᵏ zᵏ / (k!)²` (so `besselPhi (-m²/4) (τ² - ξ²) = J₀(m √(τ² - ξ²))`).
In null coordinates the retarded Green function of `-∂ₜ² + ∂ₓ² - m²` is
`-½ · 1_{J⁺} · besselPhi (-m²/4) (s r)`, and the key property is the ordinary differential
equation `z φ'' + φ' = c φ`, which says `∂ₛ ∂ᵣ φ(s r) = c φ(s r)`.

Main results: `besselPhi_zero`, `contDiff_besselPhi`, `besselPhi_ode`.

This is a supporting result; no catalogue entry.
-/

open Real Nat Set

namespace Lightlike.GreenOperators

/-- Coefficients `cᵏ / (k!)²`. -/
noncomputable def besselCoeff (c : ℝ) (k : ℕ) : ℝ := c ^ k / ((k.factorial : ℝ) ^ 2)

/-- `besselPhi c z = ∑ₖ cᵏ zᵏ / (k!)²`. -/
noncomputable def besselPhi (c z : ℝ) : ℝ := ∑' k : ℕ, besselCoeff c k * z ^ k

/-- First derivative series. -/
noncomputable def besselPhi1 (c z : ℝ) : ℝ :=
  ∑' k : ℕ, besselCoeff c k * ((k : ℝ) * z ^ (k - 1))

/-- Second derivative series. -/
noncomputable def besselPhi2 (c z : ℝ) : ℝ :=
  ∑' k : ℕ, besselCoeff c k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * z ^ (k - 1 - 1)))

/-- Summable majorant, valid on `|z| < ρ`, `ρ ≥ 1`. -/
noncomputable def besselBound (c ρ : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2 * (|c| * ρ) ^ k / ((k.factorial : ℝ) ^ 2)

lemma besselBound_nonneg {c ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) : 0 ≤ besselBound c ρ k := by
  unfold besselBound
  positivity

lemma summable_besselBound (c : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : Summable (besselBound c ρ) := by
  refine Summable.of_nonneg_of_le (besselBound_nonneg hρ)
    (fun k => ?_) (Real.summable_pow_div_factorial (Real.exp 2 * (|c| * ρ)))
  have h1 : ((k : ℝ) + 1) ^ 2 ≤ (Real.exp 2) ^ k := by
    have h := Real.add_one_le_exp (k : ℝ)
    have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    calc ((k : ℝ) + 1) ^ 2 ≤ (Real.exp k) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = (Real.exp 2) ^ k := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; ring_nf
  have hf : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr k.factorial_ne_zero
  unfold besselBound
  rw [mul_pow (Real.exp 2)]
  have hp : 0 ≤ (|c| * ρ) ^ k := by positivity
  have hfp : (0 : ℝ) < (k.factorial : ℝ) := by linarith
  calc ((k : ℝ) + 1) ^ 2 * (|c| * ρ) ^ k / ((k.factorial : ℝ) ^ 2)
      ≤ ((Real.exp 2) ^ k * (|c| * ρ) ^ k) / (k.factorial : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hfp]
        have : ((k : ℝ) + 1) ^ 2 * (|c| * ρ) ^ k * (k.factorial : ℝ)
            ≤ (Real.exp 2) ^ k * (|c| * ρ) ^ k * (k.factorial : ℝ) ^ 2 := by
          have h2 : (k.factorial : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by nlinarith
          calc ((k : ℝ) + 1) ^ 2 * (|c| * ρ) ^ k * (k.factorial : ℝ)
              ≤ (Real.exp 2) ^ k * (|c| * ρ) ^ k * (k.factorial : ℝ) := by gcongr
            _ ≤ (Real.exp 2) ^ k * (|c| * ρ) ^ k * (k.factorial : ℝ) ^ 2 := by gcongr
        exact this
    _ = _ := by ring

/-- Generic term bound. -/
lemma besselTerm_le {c ρ z : ℝ} (hρ : 1 ≤ ρ) (hz : |z| < ρ) {k n : ℕ} (hn : n ≤ k) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : M ≤ ((k : ℝ) + 1) ^ 2) :
    |besselCoeff c k * (M * z ^ n)| ≤ besselBound c ρ k := by
  unfold besselCoeff besselBound
  have hzn : |z| ^ n ≤ ρ ^ k := by
    calc |z| ^ n ≤ ρ ^ n := pow_le_pow_left₀ (abs_nonneg z) hz.le n
      _ ≤ ρ ^ k := pow_le_pow_right₀ hρ hn
  have hfp : (0 : ℝ) < ((k.factorial : ℝ) ^ 2) := by positivity
  rw [abs_mul, abs_mul, abs_div, abs_of_pos hfp, abs_pow, abs_pow, abs_of_nonneg hM0, mul_pow]
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hfp]
  have : M * |z| ^ n ≤ ((k : ℝ) + 1) ^ 2 * ρ ^ k := by
    apply mul_le_mul hM hzn (by positivity) (by positivity)
  calc |c| ^ k * (M * |z| ^ n) ≤ |c| ^ k * (((k : ℝ) + 1) ^ 2 * ρ ^ k) := by gcongr
    _ = _ := by ring

lemma hasDerivAt_besselPhi (c z : ℝ) : HasDerivAt (besselPhi c) (besselPhi1 c z) z := by
  set ρ : ℝ := |z| + 1 with hρ
  have hρ1 : 1 ≤ ρ := by have := abs_nonneg z; linarith
  have hy : z ∈ Ioo (-ρ) ρ := by
    rw [mem_Ioo]; constructor <;> cases abs_cases z <;> linarith
  have hab : ∀ y ∈ Ioo (-ρ) ρ, |y| < ρ := fun y hy => abs_lt.mpr hy
  refine hasDerivAt_tsum_of_isPreconnected (summable_besselBound c (by linarith : (0:ℝ) ≤ ρ))
    (g := fun k z => besselCoeff c k * z ^ k)
    (g' := fun k z => besselCoeff c k * ((k : ℝ) * z ^ (k - 1))) isOpen_Ioo isPreconnected_Ioo
    ?_ ?_ (y₀ := z) hy ?_ hy
  · intro k y _
    exact (hasDerivAt_pow k y).const_mul _
  · intro k y hy'
    rw [Real.norm_eq_abs]
    exact besselTerm_le hρ1 (hab y hy') (Nat.sub_le k 1) (M := (k : ℝ)) (by positivity)
      (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  · refine Summable.of_norm_bounded (summable_besselBound c (by linarith : (0:ℝ) ≤ ρ))
      (fun k => ?_)
    have := besselTerm_le (c := c) (z := z) (ρ := ρ) hρ1 (hab z hy) (n := k) (k := k) le_rfl
      (M := 1) zero_le_one (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    simpa using this

lemma summable_besselTerm (c z : ℝ) {n : ℕ → ℕ} (hn : ∀ k, n k ≤ k) {M : ℕ → ℝ}
    (hM0 : ∀ k, 0 ≤ M k) (hM : ∀ k, M k ≤ ((k : ℝ) + 1) ^ 2) :
    Summable fun k : ℕ => besselCoeff c k * (M k * z ^ n k) := by
  have hρ1 : 1 ≤ |z| + 1 := by have := abs_nonneg z; linarith
  refine Summable.of_norm_bounded (summable_besselBound c (by linarith : (0:ℝ) ≤ |z| + 1))
    (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact besselTerm_le hρ1 (by linarith [abs_nonneg z]) (hn k) (hM0 k) (hM k)

lemma hasDerivAt_besselPhi1 (c z : ℝ) : HasDerivAt (besselPhi1 c) (besselPhi2 c z) z := by
  set ρ : ℝ := |z| + 1 with hρ
  have hρ1 : 1 ≤ ρ := by have := abs_nonneg z; linarith
  have hy : z ∈ Ioo (-ρ) ρ := by
    rw [mem_Ioo]; constructor <;> cases abs_cases z <;> linarith
  have hab : ∀ y ∈ Ioo (-ρ) ρ, |y| < ρ := fun y hy => abs_lt.mpr hy
  have hMb : ∀ k : ℕ, (k : ℝ) * (((k - 1 : ℕ) : ℝ)) ≤ ((k : ℝ) + 1) ^ 2 := by
    intro k
    have h1 : (((k - 1 : ℕ) : ℝ)) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  refine hasDerivAt_tsum_of_isPreconnected (summable_besselBound c (by linarith : (0:ℝ) ≤ ρ))
    (g := fun k z => besselCoeff c k * ((k : ℝ) * z ^ (k - 1)))
    (g' := fun k z => besselCoeff c k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * z ^ (k - 1 - 1))))
    isOpen_Ioo isPreconnected_Ioo ?_ ?_ (y₀ := z) hy ?_ hy
  · intro k y _
    exact ((hasDerivAt_pow (k - 1) y).const_mul _).const_mul _
  · intro k y hy'
    rw [Real.norm_eq_abs]
    refine besselTerm_le hρ1 (hab y hy') (n := k - 1 - 1) (by omega)
      (M := (k : ℝ) * (((k - 1 : ℕ) : ℝ))) (by positivity) (hMb k) |>.trans_eq' ?_
    ring_nf
  · exact summable_besselTerm c z (n := fun k => k - 1) (M := fun k => (k : ℝ))
      (fun k => Nat.sub_le k 1) (fun k => Nat.cast_nonneg k)
      (fun k => by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

lemma continuous_besselPhi2 (c : ℝ) : Continuous (besselPhi2 c) := by
  rw [continuous_iff_continuousAt]
  intro z
  set ρ : ℝ := |z| + 1 with hρ
  have hρ1 : 1 ≤ ρ := by have := abs_nonneg z; linarith
  have hy : z ∈ Ioo (-ρ) ρ := by
    rw [mem_Ioo]; constructor <;> cases abs_cases z <;> linarith
  have hMb : ∀ k : ℕ, (k : ℝ) * (((k - 1 : ℕ) : ℝ)) ≤ ((k : ℝ) + 1) ^ 2 := by
    intro k
    have h1 : (((k - 1 : ℕ) : ℝ)) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hc : ContinuousOn (besselPhi2 c) (Ioo (-ρ) ρ) := by
    refine continuousOn_tsum (u := besselBound c ρ) (fun k => ?_)
      (summable_besselBound c (by linarith : (0:ℝ) ≤ ρ)) (fun k y hy' => ?_)
    · fun_prop
    · rw [Real.norm_eq_abs]
      refine besselTerm_le hρ1 (abs_lt.mpr hy') (n := k - 1 - 1) (by omega)
        (M := (k : ℝ) * (((k - 1 : ℕ) : ℝ))) (by positivity) (hMb k) |>.trans_eq' ?_
      ring_nf
  exact hc.continuousAt (isOpen_Ioo.mem_nhds hy)

/-- `besselPhi c` is `C²`. -/
theorem contDiff_besselPhi (c : ℝ) : ContDiff ℝ 2 (besselPhi c) := by
  have h1 : deriv (besselPhi c) = besselPhi1 c := funext fun z => (hasDerivAt_besselPhi c z).deriv
  have h2 : deriv (besselPhi1 c) = besselPhi2 c :=
    funext fun z => (hasDerivAt_besselPhi1 c z).deriv
  have hd : Differentiable ℝ (besselPhi c) := fun z => (hasDerivAt_besselPhi c z).differentiableAt
  have hd1 : Differentiable ℝ (besselPhi1 c) :=
    fun z => (hasDerivAt_besselPhi1 c z).differentiableAt
  have hC1 : ContDiff ℝ 1 (besselPhi1 c) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hd1, by rw [h2]; exact continuous_besselPhi2 c⟩
  have : ContDiff ℝ ((1 : ℕ) + 1) (besselPhi c) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hd, by simp, ?_⟩
    rw [h1]; exact_mod_cast hC1
  exact_mod_cast this

lemma besselPhi_zero (c : ℝ) : besselPhi c 0 = 1 := by
  unfold besselPhi
  rw [tsum_eq_single 0]
  · simp [besselCoeff]
  · intro k hk; simp [hk]

lemma besselPhi1_zero (c : ℝ) : besselPhi1 c 0 = c := by
  unfold besselPhi1
  rw [tsum_eq_single 1]
  · simp [besselCoeff]
  · intro k hk
    rcases k with _ | _ | k
    · simp
    · exact absurd rfl hk
    · simp

/-- The differential equation `z φ'' + φ' = c φ`. -/
theorem besselPhi_ode (c z : ℝ) :
    z * besselPhi2 c z + besselPhi1 c z = c * besselPhi c z := by
  have hs2 : Summable fun k : ℕ => besselCoeff c k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * z ^ (k - 1 - 1))) :=
    by simpa [mul_assoc] using
      summable_besselTerm c z (n := fun k => k - 1 - 1) (M := fun k => (k : ℝ) * (((k - 1 : ℕ) : ℝ)))
        (fun k => by omega) (fun k => by positivity)
        (fun k => by
          have h1 : (((k - 1 : ℕ) : ℝ)) ≤ k := by exact_mod_cast Nat.sub_le k 1
          have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith)
  have hs1 : Summable fun k : ℕ => besselCoeff c k * ((k : ℝ) * z ^ (k - 1)) :=
    summable_besselTerm c z (n := fun k => k - 1) (M := fun k => (k : ℝ))
      (fun k => Nat.sub_le k 1) (fun k => Nat.cast_nonneg k)
      (fun k => by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hs0 : Summable fun k : ℕ => besselCoeff c k * z ^ k := by
    simpa using summable_besselTerm c z (n := fun k => k) (M := fun _ => (1 : ℝ))
      (fun k => le_rfl) (fun k => zero_le_one) (fun k => by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  unfold besselPhi2 besselPhi1 besselPhi
  rw [← tsum_mul_left, ← Summable.tsum_add (hs2.mul_left z) hs1, ← tsum_mul_left]
  have hterm : ∀ k : ℕ, z * (besselCoeff c k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * z ^ (k - 1 - 1))))
      + besselCoeff c k * ((k : ℝ) * z ^ (k - 1))
      = (fun k : ℕ => besselCoeff c k * (((k : ℝ) * (k : ℝ)) * z ^ (k - 1))) k := by
    intro k
    rcases k with _ | _ | k
    · simp
    · simp
    · simp only [Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one]
      have : z * z ^ k = z ^ (k + 1) := by ring
      rw [← this]
      ring
  simp_rw [hterm]
  have hsum : Summable fun k : ℕ => besselCoeff c k * (((k : ℝ) * (k : ℝ)) * z ^ (k - 1)) := by
    have := hs2.mul_left z |>.add hs1
    refine this.congr (fun k => hterm k)
  rw [hsum.tsum_eq_zero_add]
  have hcoef : ∀ j : ℕ, besselCoeff c (j + 1) * (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
      = c * besselCoeff c j := by
    intro j
    unfold besselCoeff
    rw [Nat.factorial_succ]
    push_cast
    have : ((j.factorial : ℝ)) ≠ 0 := by positivity
    have : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    rw [pow_succ]
    ring
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
  refine tsum_congr fun j => ?_
  rw [Nat.add_sub_cancel]
  linear_combination (z ^ j) * hcoef j

end Lightlike.GreenOperators
