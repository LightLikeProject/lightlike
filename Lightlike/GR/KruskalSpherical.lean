import Lightlike.GR.KruskalManifold

/-!
# The spherical chart of the Kruskal manifold

Gap row G1-020. The map `(T, X, θ, φ) ↦ (T, e^X sin θ cos φ, e^X sin θ sin φ, e^X cos θ)` (`kruskalSph`) is a chart
change from the domain `kruskalU` of the Kruskal chart into the global chart `kruskalC` of the Kruskal manifold
(`isChartChange_kruskalSph`), and the metric of the global chart pulls back to the Kruskal metric
(`pullback_kruskalC_sph`). So the Kruskal chart `(T, X, θ, φ)` is a chart of the Lorentzian manifold
`kruskalManifoldMetric`, covering everything except the rotation axis.
-/

open Matrix Real Set
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The spherical chart map `(T, X, θ, φ) ↦ (T, e^X n(θ, φ))`. -/
def kruskalSph (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![y 0, exp (y 1) * (sin (y 2) * cos (y 3)), exp (y 1) * (sin (y 2) * sin (y 3)),
    exp (y 1) * cos (y 2)]

lemma rhoSq_kruskalSph (y : Fin 4 → ℝ) : rhoSq (kruskalSph y) = exp (y 1) ^ 2 := by
  have hθ := sin_sq_add_cos_sq (y 2)
  have hφ := sin_sq_add_cos_sq (y 3)
  show (exp (y 1) * (sin (y 2) * cos (y 3))) ^ 2 + (exp (y 1) * (sin (y 2) * sin (y 3))) ^ 2 +
    (exp (y 1) * cos (y 2)) ^ 2 = exp (y 1) ^ 2
  linear_combination (exp (y 1) ^ 2 * sin (y 2) ^ 2) * hφ + exp (y 1) ^ 2 * hθ

lemma sC_kruskalSph (y : Fin 4 → ℝ) : sC (kruskalSph y) = y 1 ^ 2 - y 0 ^ 2 := by
  unfold sC
  rw [rhoSq_kruskalSph, Real.log_pow, Real.log_exp]
  show (1 / 2 * ((2 : ℕ) * y 1)) ^ 2 - y 0 ^ 2 = y 1 ^ 2 - y 0 ^ 2
  push_cast
  ring

lemma krC_kruskalSph (y : Fin 4 → ℝ) : krC M (kruskalSph y) = kr M y := by
  unfold krC kr
  rw [sC_kruskalSph]

lemma kruskalSph_mem {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) : kruskalSph y ∈ kruskalC := by
  refine ⟨?_, ?_⟩
  · rw [rhoSq_kruskalSph]; positivity
  · rw [sC_kruskalSph]; exact hy.1

/-- The Jacobian of the spherical chart map. -/
lemma jac_kruskalSph (y : Fin 4 → ℝ) :
    jac kruskalSph y =
      !![1, 0, 0, 0;
         0, exp (y 1) * (sin (y 2) * cos (y 3)), exp (y 1) * (cos (y 2) * cos (y 3)),
            -(exp (y 1) * (sin (y 2) * sin (y 3)));
         0, exp (y 1) * (sin (y 2) * sin (y 3)), exp (y 1) * (cos (y 2) * sin (y 3)),
            exp (y 1) * (sin (y 2) * cos (y 3));
         0, exp (y 1) * cos (y 2), -(exp (y 1) * sin (y 2)), 0] := by
  have hp : ∀ k : Fin 4, HasFDerivAt (fun z : Fin 4 → ℝ => z k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k) y := fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).hasFDerivAt
  have hE := (hp 1).exp
  have hs2 := (hp 2).sin
  have hc2 := (hp 2).cos
  have hs3 := (hp 3).sin
  have hc3 := (hp 3).cos
  have h1 : HasFDerivAt (fun z : Fin 4 → ℝ => exp (z 1) * (sin (z 2) * cos (z 3))) _ y :=
    hE.mul (hs2.mul hc3)
  have h2 : HasFDerivAt (fun z : Fin 4 → ℝ => exp (z 1) * (sin (z 2) * sin (z 3))) _ y :=
    hE.mul (hs2.mul hs3)
  have h3 : HasFDerivAt (fun z : Fin 4 → ℝ => exp (z 1) * cos (z 2)) _ y := hE.mul hc2
  ext μ a
  fin_cases μ
  · change pd a (fun z : Fin 4 → ℝ => z 0) y = _
    rw [pd, (hp 0).fderiv]
    fin_cases a <;> simp [Pi.single_apply]
  · change pd a (fun z : Fin 4 → ℝ => exp (z 1) * (sin (z 2) * cos (z 3))) y = _
    rw [pd, h1.fderiv]
    fin_cases a <;> simp [Pi.single_apply] <;> ring
  · change pd a (fun z : Fin 4 → ℝ => exp (z 1) * (sin (z 2) * sin (z 3))) y = _
    rw [pd, h2.fderiv]
    fin_cases a <;> simp [Pi.single_apply] <;> ring
  · change pd a (fun z : Fin 4 → ℝ => exp (z 1) * cos (z 2)) y = _
    rw [pd, h3.fderiv]
    fin_cases a <;> simp [Pi.single_apply] <;> ring

/-- `Σᵢ xᵢ J^i_a` over the spatial indices. -/
def radN (x1 x2 x3 : ℝ) (J : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4) : ℝ :=
  x1 * J 1 a + x2 * J 2 a + x3 * J 3 a

/-- `Σᵢ J^i_a J^i_b` over the spatial indices. -/
def radD (J : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) : ℝ :=
  J 1 a * J 1 b + J 2 a * J 2 b + J 3 a * J 3 b

/-- The pull-back of a metric of the form `-h dT² + α (x·dx)² + β |dx|²` by a matrix `J`. -/
lemma radial_form (h α β x1 x2 x3 : ℝ) (J : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) :
    (Jᵀ * (!![-h, 0, 0, 0;
       0, α * (x1 * x1) + β, α * (x1 * x2), α * (x1 * x3);
       0, α * (x2 * x1), α * (x2 * x2) + β, α * (x2 * x3);
       0, α * (x3 * x1), α * (x3 * x2), α * (x3 * x3) + β] : Matrix (Fin 4) (Fin 4) ℝ) * J) a b =
      -h * (J 0 a * J 0 b) + α * (radN x1 x2 x3 J a * radN x1 x2 x3 J b) + β * radD J a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, radN, radD]
  ring

/-- **The metric of the global chart pulls back to the Kruskal metric** under the spherical chart map. -/
theorem pullback_kruskalC_sph (y : Fin 4 → ℝ) :
    pullback (kruskalCMetric M) kruskalSph y = kruskalMetric M y := by
  have hθ := sin_sq_add_cos_sq (y 2)
  have hφ := sin_sq_add_cos_sq (y 3)
  have hE : exp (y 1) ≠ 0 := (exp_pos _).ne'
  have hN : ∀ a, radN (kruskalSph y 1) (kruskalSph y 2) (kruskalSph y 3) (jac kruskalSph y) a =
      (![0, exp (y 1) ^ 2, 0, 0] : Fin 4 → ℝ) a := by
    intro a
    rw [jac_kruskalSph]
    fin_cases a <;> simp [radN, kruskalSph] <;>
      first
        | ring1
        | linear_combination (exp (y 1) ^ 2 * sin (y 2) ^ 2) * hφ + exp (y 1) ^ 2 * hθ
        | linear_combination (exp (y 1) ^ 2 * sin (y 2) * cos (y 2)) * hφ
  have hD : ∀ a b, radD (jac kruskalSph y) a b =
      (!![0, 0, 0, 0; 0, exp (y 1) ^ 2, 0, 0; 0, 0, exp (y 1) ^ 2, 0;
          0, 0, 0, exp (y 1) ^ 2 * sin (y 2) ^ 2] : Matrix (Fin 4) (Fin 4) ℝ) a b := by
    intro a b
    rw [jac_kruskalSph]
    fin_cases a <;> fin_cases b <;> simp [radD] <;>
      first
        | ring1
        | linear_combination (exp (y 1) ^ 2 * sin (y 2) ^ 2) * hφ + exp (y 1) ^ 2 * hθ
        | linear_combination (exp (y 1) ^ 2 * cos (y 2) ^ 2) * hφ + exp (y 1) ^ 2 * hθ
        | linear_combination (exp (y 1) ^ 2 * sin (y 2) * cos (y 2)) * hφ
        | linear_combination (exp (y 1) ^ 2 * sin (y 2) ^ 2) * hφ
  have hG : kruskalCMetric M (kruskalSph y) =
      !![-kh M (krC M (kruskalSph y)), 0, 0, 0;
         0, (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 1 * kruskalSph y 1) + krC M (kruskalSph y) ^ 2 / rhoSq (kruskalSph y),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 1 * kruskalSph y 2),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 1 * kruskalSph y 3);
         0, (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 2 * kruskalSph y 1),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 2 * kruskalSph y 2) + krC M (kruskalSph y) ^ 2 / rhoSq (kruskalSph y),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 2 * kruskalSph y 3);
         0, (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 3 * kruskalSph y 1),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 3 * kruskalSph y 2),
            (kh M (krC M (kruskalSph y)) - krC M (kruskalSph y) ^ 2) / rhoSq (kruskalSph y) ^ 2 *
              (kruskalSph y 3 * kruskalSph y 3) + krC M (kruskalSph y) ^ 2 / rhoSq (kruskalSph y)] := rfl
  rw [pullback_eq_mul]
  ext a b
  rw [hG, radial_form, hN, hN, hD, krC_kruskalSph, rhoSq_kruskalSph]
  have hJ0 : ∀ c : Fin 4, jac kruskalSph y 0 c = (![1, 0, 0, 0] : Fin 4 → ℝ) c := by
    intro c; rw [jac_kruskalSph]; fin_cases c <;> rfl
  rw [hJ0, hJ0]
  fin_cases a <;> fin_cases b <;> simp [kruskalMetric] <;> field_simp <;> ring

lemma contDiff_kruskalSph (μ : Fin 4) : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => kruskalSph y μ := by
  fin_cases μ
  · show ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0
    fun_prop
  · show ContDiff ℝ ∞ fun y : Fin 4 → ℝ => exp (y 1) * (sin (y 2) * cos (y 3))
    fun_prop
  · show ContDiff ℝ ∞ fun y : Fin 4 → ℝ => exp (y 1) * (sin (y 2) * sin (y 3))
    fun_prop
  · show ContDiff ℝ ∞ fun y : Fin 4 → ℝ => exp (y 1) * cos (y 2)
    fun_prop

/-- **The spherical chart map is a chart change** from the Kruskal chart domain into the global chart. -/
theorem isChartChange_kruskalSph (hM : 0 < M) : IsChartChange kruskalSph kruskalU kruskalC where
  isOpen := isOpen_kruskalU
  mapsTo := fun _ hy => kruskalSph_mem hy
  smooth := fun μ => (contDiff_kruskalSph μ).contDiffOn
  isUnit_det := fun y hy => by
    -- `Jᵀ g J` is the Kruskal metric, whose determinant is a unit
    have h1 := (isCoordMetric_kruskal M hM).isUnit_det y hy
    rw [← pullback_kruskalC_sph M y, pullback_eq_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose] at h1
    exact isUnit_of_mul_isUnit_right h1

end Lightlike
