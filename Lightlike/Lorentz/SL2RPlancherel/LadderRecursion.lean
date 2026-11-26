import Lightlike.Lorentz.SL2RPlancherel.LadderClosed
import Lightlike.Lorentz.SL2RPlancherel.LadderLocal

/-!
# The Casimir on the ladder images of a radial function

`radialCasimir 0 0 (G ∘ cosh) = (Q G) ∘ cosh`, and the Casimir of the type `(l, r)` acts on the ladder images by the radial
Laplacian of the generating function: `radialCasimir l r (hLR r G l) = hLR r (Q G) l` on `ξ > 0`. This is the engine of the
recursion on `l` (the weight `(l + ½)² + ρ²` of the Plancherel formula is `¼ + ρ² + l (l + 1)`).
-/

open Set Real Filter
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `radialCasimir l r F ξ` depends only on `F` near `ξ`. -/
lemma radialCasimir_congr (l r : ℝ) {F F' : ℝ → ℂ} {ξ : ℝ} (h : F =ᶠ[nhds ξ] F') :
    radialCasimir l r F ξ = radialCasimir l r F' ξ := by
  have h1 : deriv F =ᶠ[nhds ξ] deriv F' := h.deriv
  have h2 : deriv (deriv F) ξ = deriv (deriv F') ξ := h1.deriv_eq
  unfold radialCasimir
  rw [h2, h1.self_of_nhds, h.self_of_nhds]

/-- `radialCasimir 0 0 (G ∘ cosh) = (Q G) ∘ cosh`. -/
theorem radialCasimir_zero_zero {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir 0 0 (fun y => G (Real.cosh y)) ξ = radialQ G (Real.cosh ξ) := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hG1 : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.1 hG).2
  have d0 : ∀ v, HasDerivAt G (deriv G v) v := fun v => ((hG.differentiable (by simp)) v).hasDerivAt
  have d1 : ∀ v, HasDerivAt (deriv G) (deriv (deriv G) v) v :=
    fun v => ((hG1.differentiable (by simp)) v).hasDerivAt
  have e1 : ∀ y, deriv (fun y => G (Real.cosh y)) y = ((Real.sinh y : ℝ) : ℂ) * deriv G (Real.cosh y) := by
    intro y
    have := (d0 (Real.cosh y)).scomp y (Real.hasDerivAt_cosh y)
    rw [show (fun y => G (Real.cosh y)) = G ∘ Real.cosh from rfl, this.deriv]
    simp [Complex.real_smul]
  have hd : HasDerivAt (fun y => ((Real.sinh y : ℝ) : ℂ) * deriv G (Real.cosh y))
      (((Real.cosh ξ : ℝ) : ℂ) * deriv G (Real.cosh ξ) +
        ((Real.sinh ξ : ℝ) : ℂ) * (Real.sinh ξ • deriv (deriv G) (Real.cosh ξ))) ξ :=
    (Real.hasDerivAt_sinh ξ).ofReal_comp.mul ((d1 (Real.cosh ξ)).scomp ξ (Real.hasDerivAt_cosh ξ))
  have e2 : deriv (deriv (fun y => G (Real.cosh y))) ξ =
      ((Real.cosh ξ : ℝ) : ℂ) * deriv G (Real.cosh ξ) +
        ((Real.sinh ξ : ℝ) : ℂ) * (Real.sinh ξ • deriv (deriv G) (Real.cosh ξ)) := by
    have : deriv (fun y => G (Real.cosh y)) = fun y => ((Real.sinh y : ℝ) : ℂ) * deriv G (Real.cosh y) :=
      funext e1
    rw [this]; exact hd.deriv
  have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
  unfold radialCasimir radialQ
  rw [e2, e1]
  simp only [Complex.real_smul, zero_pow two_ne_zero, mul_zero, zero_mul, add_zero, Complex.ofReal_zero,
    zero_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  field_simp
  linear_combination (deriv (deriv G) (Real.cosh ξ)) * hrel

/-- `ladUp l r F ξ` depends only on `F` near `ξ`. -/
lemma ladUp_congr (l r : ℝ) {F F' : ℝ → ℂ} {ξ : ℝ} (h : F =ᶠ[nhds ξ] F') :
    ladUp l r F ξ = ladUp l r F' ξ := by
  unfold ladUp
  rw [h.deriv_eq, h.self_of_nhds]

/-- The profile `sinh^k G^{(k)}(cosh)` is smooth. -/
theorem contDiff_profile (k : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (profile k G) := by
  unfold profile
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => ((Real.sinh y ^ k : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sinh.pow k)
  have h2 : ContDiff ℝ ∞ (fun y : ℝ => iteratedDeriv k G (Real.cosh y)) :=
    (contDiff_iteratedDeriv_infty hG k).comp Real.contDiff_cosh
  exact h1.mul h2

/-- **The Casimir on the profiles**: `radialCasimir k 0 (profile k G) = profile k (Q G)` on `ξ > 0`. -/
theorem radialCasimir_profile (k : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) :
    ∀ ξ : ℝ, 0 < ξ → radialCasimir (k : ℝ) 0 (profile k G) ξ = profile k (radialQ G) ξ := by
  have hQ : ContDiff ℝ ∞ (radialQ G) := contDiff_radialQ hG
  induction k with
  | zero =>
    intro ξ hξ
    have e : ∀ H : ℝ → ℂ, profile 0 H = fun y => H (Real.cosh y) := by
      intro H; funext y; simp [profile]
    rw [e G, e (radialQ G)]
    simpa using radialCasimir_zero_zero hG hξ
  | succ k ih =>
    intro ξ hξ
    have hev : ∀ H : ℝ → ℂ, ContDiff ℝ ∞ H →
        profile (k + 1) H =ᶠ[nhds ξ] ladUp (k : ℝ) 0 (profile k H) :=
      fun H hH => Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => (ladUp_profile k hH hy).symm)
    rw [radialCasimir_congr _ _ (hev G hG)]
    have hc := radialCasimir_ladUp (k : ℝ) 0 ((contDiff_profile k hG).contDiffOn (s := Ioi 0)) hξ
    push_cast
    rw [hc]
    have hih : radialCasimir (k : ℝ) 0 (profile k G) =ᶠ[nhds ξ] profile k (radialQ G) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => ih y hy)
    rw [ladUp_congr _ _ hih, ladUp_profile k hQ hξ]

/-- The ladder images are smooth on `ξ > 0`. -/
theorem contDiffOn_hLR (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ContDiffOn ℝ ∞ (hLR r G l) (Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => ((Real.sinh y ^ (l + r) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sinh.pow _)
  have h2 : ContDiffOn ℝ ∞ (fun y : ℝ => uRec r G l (Real.cosh y)) (Ioi 0) :=
    (uRec_contDiffOn r hG l).comp Real.contDiff_cosh.contDiffOn (fun y hy => by
      show (-1 : ℝ) < Real.cosh y
      linarith [Real.one_le_cosh y])
  exact (h1.contDiffOn.mul h2).congr (fun ξ hξ => hLR_eq r hG l ξ hξ)

/-- **The Casimir on the ladder images**: `radialCasimir l r (hLR r G l) = hLR r (Q G) l` on `ξ > 0`. -/
theorem radialCasimir_hLR (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ∀ ξ : ℝ, 0 < ξ → radialCasimir (l : ℝ) (r : ℝ) (hLR r G l) ξ = hLR r (radialQ G) l ξ := by
  have hQ : ContDiff ℝ ∞ (radialQ G) := contDiff_radialQ hG
  induction l with
  | zero =>
    intro ξ hξ
    have hsw : radialCasimir ((0 : ℕ) : ℝ) (r : ℝ) = radialCasimir (r : ℝ) 0 := by
      funext F ξ'; simp [radialCasimir]
    rw [hsw]
    exact radialCasimir_profile r hG ξ hξ
  | succ l ih =>
    intro ξ hξ
    show radialCasimir ((l + 1 : ℕ) : ℝ) (r : ℝ) (ladUp (l : ℝ) (r : ℝ) (hLR r G l)) ξ =
      ladUp (l : ℝ) (r : ℝ) (hLR r (radialQ G) l) ξ
    push_cast
    rw [radialCasimir_ladUp (l : ℝ) (r : ℝ) (contDiffOn_hLR r hG l) hξ]
    exact ladUp_congr _ _ (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => ih y hy))

end Lightlike.Lorentz.SL2RPlancherel
