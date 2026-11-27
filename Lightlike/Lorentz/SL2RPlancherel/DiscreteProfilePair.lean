module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileOrth

/-!
# The pairing of two radial profiles of discrete series

`profPair n l j κ n' l' j' κ' = ∫_0^∞ ψ^n_{jl} conj ψ^{n'}_{j'l'} sinh ξ dξ`. For equal `K × K`-weights
(`n + 2j = n' + 2j'`, `n + 2l = n' + 2l'`) and `n ≠ n'` it vanishes (`profPair_eq_zero_of_ne`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The pairing** `∫_0^∞ ψ conj χ sinh ξ dξ` of two radial profiles. -/
def profPair (n l j : ℕ) (κ : ℂ) (n' l' j' : ℕ) (κ' : ℂ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), profileFun n l j κ ξ * (starRingEnd ℂ) (profileFun n' l' j' κ' ξ) * (Real.sinh ξ : ℂ)

lemma ladB_congr {n j l n' j' l' : ℕ} (hl : n + 2 * l = n' + 2 * l') (hj : n + 2 * j = n' + 2 * j') (ξ : ℝ) :
    ladB n' j' l' ξ = ladB n j l ξ := by
  unfold ladB
  rw [← hl, ← hj]

lemma differentiableAt_profileFun (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) (ξ : ℝ) :
    DifferentiableAt ℝ (profileFun n l j κ) ξ :=
  (hasDerivAt_profileFun n l j hn κ ξ).differentiableAt

/-- **One step of the ladder**: `(n + l) ⟨ψ_{l+1}, χ_{l'+1}⟩ = (l' + 1) ⟨ψ_l, χ_{l'}⟩`. -/
theorem profPair_step (n l j : ℕ) (κ : ℂ) (n' l' j' : ℕ) (κ' : ℂ) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h4 : 4 ≤ n + n') (hb1 : n + 2 * (l + 1) = n' + 2 * (l' + 1)) (hb2 : n + 2 * j = n' + 2 * j') :
    ((n + l : ℕ) : ℂ) * profPair n (l + 1) j κ n' (l' + 1) j' κ' =
      ((l' + 1 : ℕ) : ℂ) * profPair n l j κ n' l' j' κ' := by
  have h := pair_core n l j hn κ (b := n') hn' h4 (χ := profileFun n' (l' + 1) j' κ')
    (χ₁ := profileFun n' l' j' κ') (((l' + 1 : ℕ) : ℝ))
    (Cχ := profConst n' (l' + 1) j' κ') (Cχ₁ := profConst n' l' j' κ')
    (continuous_profileFun n' _ _ hn' κ') (continuous_profileFun n' _ _ hn' κ')
    (fun ξ _ => differentiableAt_profileFun n' _ _ hn' κ' ξ)
    (fun ξ hξ => by
      have := profileFun_up n' l' j' hn' κ' hξ
      rw [ladB_congr hb1 hb2 ξ] at this
      simpa using this)
    (fun ξ hξ => norm_profileFun_le n' _ _ κ' hξ) (fun ξ hξ => norm_profileFun_le n' _ _ κ' hξ)
  simpa [profPair] using h

/-- **The last step**: `⟨ψ_{l+1}, χ_0⟩ = 0` when the weights match. -/
theorem profPair_step_zero (n l j : ℕ) (κ : ℂ) (n' j' : ℕ) (κ' : ℂ) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h4 : 4 ≤ n + n') (hb1 : n + 2 * (l + 1) = n' + 2 * 0) (hb2 : n + 2 * j = n' + 2 * j') :
    ((n + l : ℕ) : ℂ) * profPair n (l + 1) j κ n' 0 j' κ' = 0 := by
  have h := pair_core n l j hn κ (b := n') hn' h4 (χ := profileFun n' 0 j' κ')
    (χ₁ := profileFun n' 0 j' κ') (0 : ℝ)
    (Cχ := profConst n' 0 j' κ') (Cχ₁ := profConst n' 0 j' κ')
    (continuous_profileFun n' _ _ hn' κ') (continuous_profileFun n' _ _ hn' κ')
    (fun ξ _ => differentiableAt_profileFun n' _ _ hn' κ' ξ)
    (fun ξ hξ => by
      have := profileFun_up_zero n' j' hn' κ' hξ
      rw [ladB_congr hb1 hb2 ξ] at this
      simpa using this)
    (fun ξ hξ => norm_profileFun_le n' _ _ κ' hξ) (fun ξ hξ => norm_profileFun_le n' _ _ κ' hξ)
  simpa [profPair] using h

/-- **Vanishing by induction on `l'`**: if `l' < l` and the `K × K`-weights agree, the pairing is `0`. -/
theorem profPair_eq_zero_aux (n j j' : ℕ) (κ κ' : ℂ) (n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n') (h4 : 4 ≤ n + n')
    (hb2 : n + 2 * j = n' + 2 * j') :
    ∀ l' l : ℕ, l' < l → n + 2 * l = n' + 2 * l' → profPair n l j κ n' l' j' κ' = 0 := by
  intro l'
  induction l' with
  | zero =>
    intro l hl hb
    obtain ⟨l₀, rfl⟩ : ∃ l₀, l = l₀ + 1 := ⟨l - 1, by omega⟩
    have h := profPair_step_zero n l₀ j κ n' j' κ' hn hn' h4 hb hb2
    have hne : ((n + l₀ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + l₀ ≠ 0)
    exact (mul_eq_zero.1 h).resolve_left hne
  | succ l'₀ ih =>
    intro l hl hb
    obtain ⟨l₀, rfl⟩ : ∃ l₀, l = l₀ + 1 := ⟨l - 1, by omega⟩
    have h := profPair_step n l₀ j κ n' l'₀ j' κ' hn hn' h4 hb hb2
    have hz := ih l₀ (by omega) (by omega)
    rw [hz, mul_zero] at h
    have hne : ((n + l₀ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + l₀ ≠ 0)
    exact (mul_eq_zero.1 h).resolve_left hne

lemma profPair_swap (n l j : ℕ) (κ : ℂ) (n' l' j' : ℕ) (κ' : ℂ) (hn : 1 ≤ n) (hn' : 1 ≤ n') (h4 : 4 ≤ n + n') :
    profPair n' l' j' κ' n l j κ = (starRingEnd ℂ) (profPair n l j κ n' l' j' κ') := by
  unfold profPair
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **The profiles of distinct discrete series with the same `K × K`-weights are orthogonal.** -/
theorem profPair_eq_zero_of_ne (n l j : ℕ) (κ : ℂ) (n' l' j' : ℕ) (κ' : ℂ) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h4 : 4 ≤ n + n') (hne : n ≠ n') (hl : n + 2 * l = n' + 2 * l') (hj : n + 2 * j = n' + 2 * j') :
    profPair n l j κ n' l' j' κ' = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact profPair_eq_zero_aux n j j' κ κ' n' hn hn' h4 hj l' l (by omega) hl
  · have := profPair_eq_zero_aux n' j' j κ' κ n hn' hn (by omega) hj.symm l l' (by omega) hl.symm
    rw [profPair_swap n l j κ n' l' j' κ' hn hn' h4] at this
    simpa using this

end Lightlike.Lorentz.SL2RPlancherel
