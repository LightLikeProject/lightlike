module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileRel

/-!
# The ladder equations for the radial profiles of the discrete series

Let `ψ_{jl}(ξ) = κ cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))` (`profileFun`, with `κ = ‖e_j‖²` for the matrix coefficient
`⟨e_j, D_n(a(ξ)) e_l⟩`, `profile_eq_mcoef`) and `b_{jl}(ξ) = ((n + 2l) cosh ξ - (n + 2j)) / (2 sinh ξ)`. For `ξ > 0`:
* `ψ_{j,k+1}' + b_{j,k+1} ψ_{j,k+1} = (k + 1) ψ_{jk}` (`profileFun_up`) and `ψ_{j0}' + b_{j0} ψ_{j0} = 0`
  (`profileFun_up_zero`);
* `ψ_{jl}' - b_{jl} ψ_{jl} = -(n + l) ψ_{j,l+1}` (`profileFun_down`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The radial profile** `ψ(ξ) = κ cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))` with a prescribed constant `κ`. -/
def profileFun (n l j : ℕ) (κ : ℂ) (ξ : ℝ) : ℂ :=
  κ * (((Real.cosh (ξ / 2) ^ n)⁻¹ : ℝ) : ℂ) * profPoly n l j (Real.tanh (ξ / 2))

/-- **The coefficient of the ladder equations**, `b_{jl}(ξ) = ((n + 2l) cosh ξ - (n + 2j)) / (2 sinh ξ)`. -/
def ladB (n j l : ℕ) (ξ : ℝ) : ℝ :=
  (((n + 2 * l : ℕ) : ℝ) * Real.cosh ξ - ((n + 2 * j : ℕ) : ℝ)) / (2 * Real.sinh ξ)

lemma abs_tanh_half_lt_one (ξ : ℝ) : |Real.tanh (ξ / 2)| < 1 :=
  abs_lt.2 ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

lemma hasDerivAt_tanh_half (ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => Real.tanh (ξ / 2)) ((1 - Real.tanh (ξ / 2) ^ 2) / 2) ξ := by
  have hc : Real.cosh (ξ / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hx : HasDerivAt (fun ξ : ℝ => ξ / 2) (1 / 2) ξ := (hasDerivAt_id ξ).div_const 2
  have h1 : HasDerivAt (fun ξ : ℝ => Real.sinh (ξ / 2)) (Real.cosh (ξ / 2) * (1 / 2)) ξ := hx.sinh
  have h2 : HasDerivAt (fun ξ : ℝ => Real.cosh (ξ / 2)) (Real.sinh (ξ / 2) * (1 / 2)) ξ := hx.cosh
  have h3 := h1.div h2 hc
  have h4 : (fun ξ : ℝ => Real.tanh (ξ / 2)) = fun ξ : ℝ => Real.sinh (ξ / 2) / Real.cosh (ξ / 2) := by
    funext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [h4]
  refine h3.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_sq (ξ / 2)
  first | (field_simp; nlinarith [this]) | field_simp

lemma hasDerivAt_cosh_half_pow_inv (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => (Real.cosh (ξ / 2) ^ n)⁻¹)
      (-((n : ℝ) / 2) * Real.tanh (ξ / 2) * (Real.cosh (ξ / 2) ^ n)⁻¹) ξ := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  have hx : HasDerivAt (fun ξ : ℝ => ξ / 2) (1 / 2) ξ := (hasDerivAt_id ξ).div_const 2
  have h2 : HasDerivAt (fun ξ : ℝ => Real.cosh (ξ / 2)) (Real.sinh (ξ / 2) * (1 / 2)) ξ := hx.cosh
  have h3 := h2.pow (M + 1)
  have hc : Real.cosh (ξ / 2) ^ (M + 1) ≠ 0 := (pow_pos (Real.cosh_pos _) _).ne'
  have h4 := h3.inv (by simpa using hc)
  refine h4.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc0 : Real.cosh (ξ / 2) ≠ 0 := (Real.cosh_pos _).ne'
  simp only [Nat.add_sub_cancel, Pi.pow_apply]
  push_cast
  field_simp
  ring

lemma tanh_half_facts {ξ : ℝ} (hξ : 0 < ξ) :
    0 < Real.tanh (ξ / 2) ∧ Real.tanh (ξ / 2) < 1 ∧
      Real.cosh ξ * (1 - Real.tanh (ξ / 2) ^ 2) = 1 + Real.tanh (ξ / 2) ^ 2 ∧
      Real.sinh ξ * (1 - Real.tanh (ξ / 2) ^ 2) = 2 * Real.tanh (ξ / 2) := by
  have hc : Real.cosh (ξ / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hξ2 : ξ = 2 * (ξ / 2) := by ring
  have hC2 := Real.cosh_sq (ξ / 2)
  have key : 1 - (Real.sinh (ξ / 2) / Real.cosh (ξ / 2)) ^ 2 = 1 / Real.cosh (ξ / 2) ^ 2 := by
    field_simp
    linarith
  refine ⟨?_, Real.tanh_lt_one _, ?_, ?_⟩
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 (by linarith)) (Real.cosh_pos _)
  · have h2 : Real.cosh ξ = Real.cosh (ξ / 2) ^ 2 + Real.sinh (ξ / 2) ^ 2 := by
      rw [← Real.cosh_two_mul]; congr 1
    rw [h2, Real.tanh_eq_sinh_div_cosh, key]
    field_simp
  · have h2 : Real.sinh ξ = 2 * Real.sinh (ξ / 2) * Real.cosh (ξ / 2) := by
      rw [← Real.sinh_two_mul]; congr 1
    rw [h2, Real.tanh_eq_sinh_div_cosh, key]
    field_simp

lemma hasDerivAt_profileFun (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) (ξ : ℝ) :
    HasDerivAt (profileFun n l j κ)
      (κ * (((Real.cosh (ξ / 2) ^ n)⁻¹ : ℝ) : ℂ) *
        (-(((n : ℝ) / 2 * Real.tanh (ξ / 2) : ℝ) : ℂ) * profPoly n l j (Real.tanh (ξ / 2)) +
          (((1 - Real.tanh (ξ / 2) ^ 2) / 2 : ℝ) : ℂ) * deriv (profPoly n l j) (Real.tanh (ξ / 2)))) ξ := by
  have hP := (hasDerivAt_profPoly n l j hn (abs_tanh_half_lt_one ξ)).scomp ξ (hasDerivAt_tanh_half ξ)
  have hr := (hasDerivAt_cosh_half_pow_inv n hn ξ).ofReal_comp
  have h := (hr.const_mul κ).mul hP
  unfold profileFun
  refine h.congr_deriv ?_
  rw [(hasDerivAt_profPoly n l j hn (abs_tanh_half_lt_one ξ)).deriv]
  simp only [Function.comp_apply, Complex.real_smul]
  generalize Real.tanh (ξ / 2) = T
  generalize Real.cosh (ξ / 2) ^ n = c
  push_cast
  ring

/-- Algebra of the raising equation. -/
lemma alg_up (κ r T P P' Q N L J G : ℂ) (hT : T ≠ 0)
    (hrel : T * (1 - T ^ 2) * P' + (L * (1 + T ^ 2) - (1 - T ^ 2) * J) * P = G * T * Q) :
    κ * r * (-(N / 2 * T) * P + ((1 - T ^ 2) / 2) * P') +
        (((N + 2 * L) * (1 + T ^ 2) - (N + 2 * J) * (1 - T ^ 2)) / (4 * T)) * (κ * r * P) =
      (G / 2) * (κ * r * Q) := by
  have e : κ * r * (-(N / 2 * T) * P + ((1 - T ^ 2) / 2) * P') +
        (((N + 2 * L) * (1 + T ^ 2) - (N + 2 * J) * (1 - T ^ 2)) / (4 * T)) * (κ * r * P) -
      (G / 2) * (κ * r * Q) =
      (κ * r / (2 * T)) * (T * (1 - T ^ 2) * P' + (L * (1 + T ^ 2) - (1 - T ^ 2) * J) * P - G * T * Q) := by
    field_simp
    ring
  linear_combination e + (κ * r / (2 * T)) * hrel

/-- Algebra of the lowering equation. -/
lemma alg_down (κ r T P P' Q N L J G : ℂ) (hT : T ≠ 0)
    (hrel : T * (1 - T ^ 2) * P' + ((1 - T ^ 2) * J - (L * (1 + T ^ 2) + 2 * N * T ^ 2)) * P = G * T * Q) :
    κ * r * (-(N / 2 * T) * P + ((1 - T ^ 2) / 2) * P') -
        (((N + 2 * L) * (1 + T ^ 2) - (N + 2 * J) * (1 - T ^ 2)) / (4 * T)) * (κ * r * P) =
      (G / 2) * (κ * r * Q) := by
  have e : κ * r * (-(N / 2 * T) * P + ((1 - T ^ 2) / 2) * P') -
        (((N + 2 * L) * (1 + T ^ 2) - (N + 2 * J) * (1 - T ^ 2)) / (4 * T)) * (κ * r * P) -
      (G / 2) * (κ * r * Q) =
      (κ * r / (2 * T)) * (T * (1 - T ^ 2) * P' + ((1 - T ^ 2) * J - (L * (1 + T ^ 2) + 2 * N * T ^ 2)) * P -
        G * T * Q) := by
    field_simp
    ring
  linear_combination e + (κ * r / (2 * T)) * hrel

/-- The coefficient `b` in terms of `T = tanh(ξ/2)`. -/
lemma ladB_eq (n j l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    (ladB n j l ξ : ℂ) =
      (((n : ℂ) + 2 * l) * (1 + ((Real.tanh (ξ / 2) : ℝ) : ℂ) ^ 2) -
        ((n : ℂ) + 2 * j) * (1 - ((Real.tanh (ξ / 2) : ℝ) : ℂ) ^ 2)) / (4 * ((Real.tanh (ξ / 2) : ℝ) : ℂ)) := by
  obtain ⟨hT0, hT1, hch, hsh⟩ := tanh_half_facts hξ
  unfold ladB
  have h1 : (1 - Real.tanh (ξ / 2) ^ 2) ≠ 0 := by nlinarith
  have hch' : Real.cosh ξ = (1 + Real.tanh (ξ / 2) ^ 2) / (1 - Real.tanh (ξ / 2) ^ 2) := by
    field_simp; linarith
  have hsh' : Real.sinh ξ = 2 * Real.tanh (ξ / 2) / (1 - Real.tanh (ξ / 2) ^ 2) := by
    field_simp; linarith
  rw [hch', hsh']
  generalize Real.tanh (ξ / 2) = T at *
  have hT0' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have h1' : (1 - (T : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1
  push_cast
  field_simp
  ring

/-- **The raising ladder equation** `ψ_{j,k+1}' + b ψ_{j,k+1} = (k+1) ψ_{jk}`. -/
theorem profileFun_up (n k j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    deriv (profileFun n (k + 1) j κ) ξ + (ladB n j (k + 1) ξ : ℂ) * profileFun n (k + 1) j κ ξ =
      ((k + 1 : ℕ) : ℂ) * profileFun n k j κ ξ := by
  obtain ⟨hT0, hT1, -, -⟩ := tanh_half_facts hξ
  have hrel := profPoly_lower n k j hn (abs_tanh_half_lt_one ξ)
  rw [(hasDerivAt_profileFun n (k + 1) j hn κ ξ).deriv, ladB_eq n j (k + 1) hξ]
  unfold profileFun
  generalize Real.tanh (ξ / 2) = T at *
  generalize (Real.cosh (ξ / 2) ^ n)⁻¹ = r
  have hT0' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have := alg_up κ (r : ℂ) (T : ℂ) (profPoly n (k + 1) j T) (deriv (profPoly n (k + 1) j) T) (profPoly n k j T)
    (n : ℂ) ((k + 1 : ℕ) : ℂ) (j : ℂ) (2 * ((k + 1 : ℕ) : ℂ)) hT0' (by linear_combination hrel)
  push_cast at this ⊢
  linear_combination this

/-- The raising ladder equation for `l = 0`: `ψ_{j0}' + b ψ_{j0} = 0`. -/
theorem profileFun_up_zero (n j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    deriv (profileFun n 0 j κ) ξ + (ladB n j 0 ξ : ℂ) * profileFun n 0 j κ ξ = 0 := by
  obtain ⟨hT0, hT1, -, -⟩ := tanh_half_facts hξ
  have hrel := profPoly_lower_zero n j hn (abs_tanh_half_lt_one ξ)
  rw [(hasDerivAt_profileFun n 0 j hn κ ξ).deriv, ladB_eq n j 0 hξ]
  unfold profileFun
  generalize Real.tanh (ξ / 2) = T at *
  generalize (Real.cosh (ξ / 2) ^ n)⁻¹ = r
  have hT0' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have := alg_up κ (r : ℂ) (T : ℂ) (profPoly n 0 j T) (deriv (profPoly n 0 j) T) 0
    (n : ℂ) ((0 : ℕ) : ℂ) (j : ℂ) 0 hT0' (by simp only [Nat.cast_zero] at hrel ⊢; linear_combination hrel)
  push_cast at this ⊢
  linear_combination this

/-- **The lowering ladder equation** `ψ_{jl}' - b ψ_{jl} = -(n + l) ψ_{j,l+1}`. -/
theorem profileFun_down (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    deriv (profileFun n l j κ) ξ - (ladB n j l ξ : ℂ) * profileFun n l j κ ξ =
      -((n + l : ℕ) : ℂ) * profileFun n (l + 1) j κ ξ := by
  obtain ⟨hT0, hT1, -, -⟩ := tanh_half_facts hξ
  have hrel := profPoly_raise n l j hn (abs_tanh_half_lt_one ξ)
  rw [(hasDerivAt_profileFun n l j hn κ ξ).deriv, ladB_eq n j l hξ]
  unfold profileFun
  generalize Real.tanh (ξ / 2) = T at *
  generalize (Real.cosh (ξ / 2) ^ n)⁻¹ = r
  have hT0' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have := alg_down κ (r : ℂ) (T : ℂ) (profPoly n l j T) (deriv (profPoly n l j) T) (profPoly n (l + 1) j T)
    (n : ℂ) (l : ℂ) (j : ℂ) (-2 * ((n + l : ℕ) : ℂ)) hT0' (by linear_combination hrel)
  push_cast at this ⊢
  linear_combination this

/-- The matrix coefficient at `a(ξ)` is the profile with `κ = ‖e_j‖²`. -/
theorem profile_eq_mcoef {n : ℕ} (hn : 2 ≤ n) (j l : ℕ) (ξ : ℝ) :
    profileFun n l j ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ) ξ = mcoef n (kClass hn j) (kClass hn l) (aR ξ) := by
  rw [mcoef_aR hn j l ξ]
  unfold profileFun
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
