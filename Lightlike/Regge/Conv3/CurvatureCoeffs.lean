import Lightlike.Regge.Conv3.CurvatureEta
import Lightlike.Regge.Conv3.FetaTaylor
import Lightlike.Regge.Conv3.Exp2Inv

/-!
# The first two `η`-coefficients of the curvature density of `1 + η h`

For a jet `J = (h, ∂h, ∂∂h)` the curvature density `Feta (η, J)` of `CurvatureEta` has the expansion
`η F₁ + η² F₂ / 2 + O(η³)` of `FetaTaylor`. Here the same expansion is computed from the explicit formula with the
second-order calculus `Exp2`: the inverse metric `(1 + η h)⁻¹` is `1 - η h + η² h² + O(η³)` (`Gi_exp`), the Christoffel
symbols and their derivatives have explicit first and second coefficients (`chr_exp`, `dchr_exp`), and the scalar
curvature is `η R₁ + η² R₂ + O(η³)` (`curv_exp`), so that `F₁ = R₁ / 2` and `F₂ = R₂ + R₁ tr h / 2` (`F_eq`, by the
uniqueness `Exp2.unique`).

## Main results

* `det_exp`, `adj_exp`, `Gi_exp`: the determinant, adjugate and inverse of `1 + η h`.
* `chr_exp`, `dchr_exp`, `curv_exp`: the Christoffel symbols, their derivatives and the scalar curvature.
* `F_eq`: `F1 J = R1 / 2` and `F2 J = R2 + R1 tr h / 2`.

**Limits.** Dimension 3; the coefficients `R1`, `R2` are sums over indices, not yet simplified to the Fierz–Pauli form
(that is `CurvaturePoly`); no symmetry of `h`, `∂h`, `∂∂h` is used here.
-/

open Matrix Finset Real Asymptotics Filter Topology
open scoped ContDiff
namespace Lightlike.Regge.Conv3

section coeffs

variable (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)

/-- `tr H`. -/
def trH : ℝ := H 0 0 + H 1 1 + H 2 2

/-- The second elementary symmetric function of `H`: the sum of the `2 × 2` principal minors. -/
def e2H : ℝ := (H 0 0 * H 1 1 - H 0 1 * H 1 0) + (H 0 0 * H 2 2 - H 0 2 * H 2 0) + (H 1 1 * H 2 2 - H 1 2 * H 2 1)

/-- The matrix square of `H`. -/
def sqH (a b : Fin 3) : ℝ := ∑ c, H a c * H c b

theorem det_exp : Exp2 (fun η => (gJ (η, H, dh, dd)).det) 1 (trH H) (e2H H) := by
  have h := Exp2.poly 1 (trH H) (e2H H) ((Matrix.of H).det) 0
  refine h.congr_fun fun η => ?_
  simp [Matrix.det_fin_three, gJ, trH, e2H]
  ring

theorem adj_exp (a b : Fin 3) :
    Exp2 (fun η => (gJ (η, H, dh, dd)).adjugate a b) (if a = b then 1 else 0)
      (trH H * (if a = b then 1 else 0) - H a b)
      (e2H H * (if a = b then 1 else 0) - trH H * H a b + sqH H a b) := by
  have h := Exp2.poly (if a = b then 1 else 0) (trH H * (if a = b then 1 else 0) - H a b)
    (e2H H * (if a = b then 1 else 0) - trH H * H a b + sqH H a b) 0 0
  refine h.congr_fun fun η => ?_
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.adjugate_fin_three, gJ, trH, e2H, sqH, Fin.sum_univ_three] <;> ring

/-- The inverse of `1 + η h` has the expansion `1 - η h + η² h² + O(η³)` entrywise. -/
theorem Gi_exp (a b : Fin 3) :
    Exp2 (fun η => (gJ (η, H, dh, dd))⁻¹ a b) (if a = b then 1 else 0) (-H a b) (sqH H a b) := by
  have h1 := (det_exp H dh dd).inv
  have h2 := h1.mul (adj_exp H dh dd a b)
  refine (h2.congr_fun fun η => ?_).congr ?_ ?_ ?_
  · rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  · ring
  · ring
  · ring

/-- `∂_j h_lk + ∂_k h_lj - ∂_l h_jk`. -/
def Bdh (j k l : Fin 3) : ℝ := dh j l k + dh k l j - dh l j k

theorem Bdh_exp (j k l : Fin 3) : Exp2 (fun η => η * dh j l k + η * dh k l j - η * dh l j k) 0 (Bdh dh j k l) 0 := by
  have h := Exp2.poly 0 (Bdh dh j k l) 0 0 0
  refine h.congr_fun fun η => ?_
  simp only [Bdh]; ring

theorem chr_exp (i j k : Fin 3) :
    Exp2 (fun η => chrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) i j k) 0
      (1 / 2 * Bdh dh j k i) (-(1 / 2) * ∑ l, H i l * Bdh dh j k l) := by
  have h := Exp2.const_mul (1 / 2) (Exp2.sum univ fun l _ => (Gi_exp H dh dd i l).mul (Bdh_exp dh j k l))
  refine (h.congr_fun fun η => ?_).congr ?_ ?_ ?_
  · simp only [chrJ, mul_sum]
  · simp
  · simp [Finset.sum_ite_eq]
  · simp only [mul_zero, zero_add, mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- `∂_μ∂_ν h_lσ + ∂_μ∂_σ h_lν - ∂_μ∂_l h_νσ`. -/
def Bdd (μ ν σ l : Fin 3) : ℝ := dd μ ν l σ + dd μ σ l ν - dd μ l ν σ

theorem Bdd_exp (μ ν σ l : Fin 3) :
    Exp2 (fun η => η * dd μ ν l σ + η * dd μ σ l ν - η * dd μ l ν σ) 0 (Bdd dd μ ν σ l) 0 := by
  have h := Exp2.poly 0 (Bdd dd μ ν σ l) 0 0 0
  refine h.congr_fun fun η => ?_
  simp only [Bdd]; ring

theorem A_exp (μ ρ l : Fin 3) :
    ∃ Q : ℝ, Exp2 (fun η => -∑ i, ∑ r, (gJ (η, H, dh, dd))⁻¹ ρ i * (η * dh μ i r) * (gJ (η, H, dh, dd))⁻¹ r l) 0
      (-dh μ ρ l) Q := by
  have hη : ∀ i r : Fin 3, Exp2 (fun η => η * dh μ i r) 0 (dh μ i r) 0 := fun i r => by
    have := Exp2.poly 0 (dh μ i r) 0 0 0
    exact this.congr_fun fun η => by ring
  have h := (Exp2.sum univ fun i _ => Exp2.sum univ fun r _ =>
    ((Gi_exp H dh dd ρ i).mul (hη i r)).mul (Gi_exp H dh dd r l)).neg
  refine ⟨_, h.congr ?_ ?_ rfl⟩
  · simp
  · simp [Finset.sum_ite_eq]

/-- The derivative of the Christoffel symbols of `1 + η h` has the expansion `η D₁ + η² D₂ + O(η³)`. -/
theorem dchr_exp (μ ρ ν σ : Fin 3) :
    Exp2 (fun η => dChrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) (fun a b i j => η * dd a b i j) μ ρ ν σ)
      0 (1 / 2 * Bdd dd μ ν σ ρ)
      (1 / 2 * ∑ l, (-dh μ ρ l * Bdh dh ν σ l - H ρ l * Bdd dd μ ν σ l)) := by
  choose Q hQ using fun l => A_exp H dh dd μ ρ l
  have h := Exp2.const_mul (1 / 2) (Exp2.sum univ fun l _ =>
    ((hQ l).mul (Bdh_exp dh ν σ l)).add ((Gi_exp H dh dd ρ l).mul (Bdd_exp dd μ ν σ l)))
  refine (h.congr_fun fun η => ?_).congr ?_ ?_ ?_
  · simp only [dChrJ]
  · simp
  · simp [Finset.sum_ite_eq]
  · simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- The first-order Christoffel symbols `½ (∂_j h_ik + ∂_k h_ij - ∂_i h_jk)`. -/
noncomputable def Gam1 (i j k : Fin 3) : ℝ := 1 / 2 * Bdh dh j k i

/-- The first-order part of `dChrJ`. -/
noncomputable def D1 (μ ρ ν σ : Fin 3) : ℝ := 1 / 2 * Bdd dd μ ν σ ρ

/-- The second-order part of `dChrJ`. -/
noncomputable def D2 (μ ρ ν σ : Fin 3) : ℝ := 1 / 2 * ∑ l, (-dh μ ρ l * Bdh dh ν σ l - H ρ l * Bdd dd μ ν σ l)

/-- The first-order part of the Ricci contraction. -/
noncomputable def I1 (σ ν : Fin 3) : ℝ := ∑ ρ, (D1 dd ρ ρ ν σ - D1 dd ν ρ ρ σ)

/-- The second-order part of the Ricci contraction. -/
noncomputable def I2 (σ ν : Fin 3) : ℝ := ∑ ρ, (D2 H dh dd ρ ρ ν σ - D2 H dh dd ν ρ ρ σ +
  ∑ l, (Gam1 dh ρ ρ l * Gam1 dh l ν σ - Gam1 dh ρ ν l * Gam1 dh l ρ σ))

/-- The first coefficient of the scalar curvature of `1 + η h`. -/
noncomputable def R1 : ℝ := ∑ σ, I1 dd σ σ

/-- The second coefficient of the scalar curvature of `1 + η h`. -/
noncomputable def R2 : ℝ := ∑ σ, ∑ ν, ((if σ = ν then 1 else 0) * I2 H dh dd σ ν - H σ ν * I1 dd σ ν)

/-- The scalar curvature of `1 + η h` has the expansion `η R₁ + η² R₂ + O(η³)`. -/
theorem curv_exp :
    Exp2 (fun η => curvJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) (fun a b i j => η * dd a b i j))
      0 (R1 dd) (R2 H dh dd) := by
  have hI : ∀ σ ν : Fin 3, Exp2 (fun η => ∑ ρ, (dChrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j)
        (fun a b i j => η * dd a b i j) ρ ρ ν σ - dChrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j)
        (fun a b i j => η * dd a b i j) ν ρ ρ σ +
        ∑ l, (chrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) ρ ρ l *
          chrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) l ν σ -
          chrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) ρ ν l *
          chrJ (gJ (η, H, dh, dd))⁻¹ (fun a i j => η * dh a i j) l ρ σ))) 0 (I1 dd σ ν) (I2 H dh dd σ ν) := by
    intro σ ν
    have h := Exp2.sum univ fun ρ _ => ((dchr_exp H dh dd ρ ρ ν σ).sub (dchr_exp H dh dd ν ρ ρ σ)).add
      (Exp2.sum univ fun l _ => ((chr_exp H dh dd ρ ρ l).mul (chr_exp H dh dd l ν σ)).sub
        ((chr_exp H dh dd ρ ν l).mul (chr_exp H dh dd l ρ σ)))
    refine h.congr ?_ ?_ ?_
    · simp
    · simp only [I1, D1, mul_zero, zero_mul, add_zero, sum_const_zero, sub_zero]
    · simp only [I2, D2, Gam1, mul_zero, zero_mul, add_zero, zero_add]
  have h := Exp2.sum univ fun σ _ => Exp2.sum univ fun ν _ => (Gi_exp H dh dd σ ν).mul (hI σ ν)
  refine h.congr ?_ ?_ ?_
  · simp
  · simp [R1, Finset.sum_ite_eq]
  · simp only [R2]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring

end coeffs

/-- The curvature density `Feta` has the expansion `η R₁/2 + η² (R₂/2 + R₁ tr h/4) + O(η³)`. -/
theorem feta_exp (J : Jet3) :
    Exp2 (fun η => Feta (η, J)) 0 (R1 J.2.2 / 2) (R2 J.1 J.2.1 J.2.2 / 2 + R1 J.2.2 * trH J.1 / 4) := by
  obtain ⟨H, dh, dd⟩ := J
  have h := (curv_exp H dh dd).const_mul (1 / 2) |>.mul (Exp2.sqrt (det_exp H dh dd))
  refine (h.congr_fun fun η => ?_).congr ?_ ?_ ?_
  · simp only [Feta]; ring
  · ring
  · ring
  · ring

theorem exp_feta (J : Jet3) :
    Exp2 (fun η => Feta (η, J)) 0 (F1 J) (F2 J / 2) := by
  obtain ⟨M, r, hr, h⟩ := feta_expansion (K := {J}) isCompact_singleton
  have hb := h J rfl
  unfold Exp2
  refine IsBigO.of_bound M ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with η hη
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hη
  have := hb η hη.le
  simp only [Real.norm_eq_abs, abs_pow]
  convert this using 2
  ring_nf

/-- **`F1` and `F2` are the coefficients of the explicit expansion.** -/
theorem F_eq (J : Jet3) :
    F1 J = R1 J.2.2 / 2 ∧ F2 J = R2 J.1 J.2.1 J.2.2 + R1 J.2.2 * trH J.1 / 2 := by
  obtain ⟨h0, h1, h2⟩ := Exp2.unique (exp_feta J) (feta_exp J)
  exact ⟨h1, by linarith⟩

end Lightlike.Regge.Conv3
