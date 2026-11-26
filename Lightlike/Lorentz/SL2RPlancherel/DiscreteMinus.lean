module

public import Lightlike.Lorentz.SL2RPlancherel.DiscretePlancherelTerm

/-!
# The antiholomorphic discrete series `D_n⁻` and its orthogonality to the holomorphic series

The matrix coefficients of the antiholomorphic series `D_n⁻` are the complex conjugates `conj ⟨v, D_n(g) w⟩` of those of
`D_n⁺`: the left and right `K`-weights are negated, so `D_n⁺` and `D_{n'}⁻` have no common `K`-weights and their
coefficients are orthogonal in `L²(SL(2,ℝ))` (`integral_mcoef_mul_mcoef`, `inner_uLp_uLpBar`,
`discreteSpace_orthogonal_bar`).
-/

@[expose] public section

open MeasureTheory Set Finset Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The coefficients of `D_n⁺` and of `conj D_{n'}⁺` are orthogonal**: `∫ ⟨e_j, D_n e_l⟩ ⟨e_{j'}, D_{n'} e_{l'}⟩ dg = 0`
(a product, not a conjugate: the `K`-weights add up to a positive number). -/
theorem integral_mcoef_mul_mcoef {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (j l j' l' : ℕ) :
    ∫ g, mcoef n (kClass hn j) (kClass hn l) g * mcoef n' (kClass hn' j') (kClass hn' l') g ∂haarR = 0 := by
  set P : SL2R → ℂ := fun g => mcoef n (kClass hn j) (kClass hn l) g *
    mcoef n' (kClass hn' j') (kClass hn' l') g with hP
  set N : ℕ := (n + 2 * j) + (n' + 2 * j') with hN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hrot : ∀ α g, P (rot α * g * rot 0) =
      Complex.exp (-((N : ℂ) * (α : ℂ) * Complex.I)) * P g := by
    intro α g
    simp only [hP]
    rw [mcoef_rot hn j l α 0 g, mcoef_rot hn' j' l' α 0 g]
    have e1 : Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        Complex.exp (-(((n' + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I)) =
        Complex.exp (-((N : ℂ) * (α : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; simp only [hN]; push_cast; ring
    have e2 : ∀ (m : ℕ), Complex.exp (-((m : ℂ) * ((0 : ℝ) : ℂ) * Complex.I)) = 1 := by
      intro m; simp
    rw [e2, e2, ← e1]
    ring
  have hinv : ∀ α, ∫ g, P (rot α * g * rot 0) ∂haarR = ∫ g, P g ∂haarR := by
    intro α
    rw [rot_zero]
    simp only [mul_one]
    exact integral_mul_left_eq_self P (rot α)
  have key : ∀ α : ℝ, Complex.exp (-((N : ℂ) * (α : ℂ) * Complex.I)) * ∫ g, P g ∂haarR = ∫ g, P g ∂haarR := by
    intro α
    have h2 := hinv α
    simp_rw [hrot α] at h2
    rw [integral_const_mul] at h2
    exact h2
  have h2 := key (π / (N : ℝ))
  have hphase : Complex.exp (-((N : ℂ) * ((π / (N : ℝ) : ℝ) : ℂ) * Complex.I)) = -1 := by
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have : -((N : ℂ) * ((π / (N : ℝ) : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  rw [hphase] at h2
  linear_combination (-1 / 2 : ℂ) * h2

/-- **The matrix coefficients of `D_n⁻`**: the complex conjugates of those of `D_n⁺`, as elements of `L²`. -/
def uLpBar {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : Lp ℂ 2 (haarR : Measure SL2R) :=
  ((memLp_uFun hn p).star).toLp (star (uFun hn p))

/-- **`D_n⁺` and `D_{n'}⁻` have orthogonal coefficients.** -/
theorem inner_uLp_uLpBar {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (p p' : ℕ × ℕ) :
    ⟪uLp hn p, uLpBar hn' p'⟫_ℂ = 0 := by
  have hae : ∀ᵐ g ∂haarR, ⟪(uLp hn p : SL2R → ℂ) g, (uLpBar hn' p' : SL2R → ℂ) g⟫_ℂ =
      (starRingEnd ℂ) (uFun hn p g * uFun hn' p' g) := by
    filter_upwards [(memLp_uFun hn p).coeFn_toLp, ((memLp_uFun hn' p').star).coeFn_toLp] with g h1 h2
    simp only [uLp, uLpBar]
    rw [h1, h2]
    simp [RCLike.inner_apply]
    ring
  rw [L2.inner_def, integral_congr_ae hae, integral_conj]
  have : ∫ g, uFun hn p g * uFun hn' p' g ∂haarR = 0 := by
    have e : ∀ g, uFun hn p g * uFun hn' p' g =
        ((uConst hn p : ℂ) * (uConst hn' p' : ℂ)) *
          (mcoef n (kClass hn p.1) (kClass hn p.2) g * mcoef n' (kClass hn' p'.1) (kClass hn' p'.2) g) := by
      intro g; simp only [uFun]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_mcoef_mul_mcoef hn hn', mul_zero]
  rw [this]; simp

/-- **The isotypic subspaces of `D_n⁺` and `D_{n'}⁻` are orthogonal.** -/
theorem discreteSpace_orthogonal_bar {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (q : ℕ × ℕ)
    (f : Lp ℂ 2 (haarR : Measure SL2R)) (hf : f ∈ discreteSpace hn) :
    ⟪uLpBar hn' q, f⟫_ℂ = 0 := by
  have hcl : (Submodule.span ℂ (Set.range (uLp hn))).topologicalClosure ≤
      (ℂ ∙ uLpBar hn' q)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [← inner_conj_symm, inner_uLp_uLpBar hn hn' p q]; simp
  have := hcl hf
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
  exact this

end Lightlike.Lorentz.SL2RPlancherel
