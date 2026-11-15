import Mathlib
import Lightlike.Regge.Linear.Model

/-!
# The local error of the linearized deficit

If the entries of `h` agree with their quadratic Taylor polynomials at `P` up to `K s³` on the
cube `‖x - P‖ ≤ s`, the linearized deficit angle at `P` differs from `s²` times the linearized
curvature by at most `336 K s³`.
-/

open Real MeasureTheory Lightlike.Geodesic

namespace Lightlike.Regge.Linear

noncomputable section

/-- Every neighbour offset has coordinates of absolute value at most `1`. -/
lemma abs_off_le (j : Fin 6) (i : Fin 2) : |off j i| ≤ 1 := by
  fin_cases j <;> fin_cases i <;> simp [off]

/-- The coefficients of the angle variation are bounded. -/
lemma coef_bound (j : Fin 6) :
    |(sqA j - sqB j + sqC j) / sqA j| ≤ 6 ∧ |(sqB j - sqA j + sqC j) / sqB j| ≤ 6 := by
  fin_cases j <;> norm_num [sqA, sqB, sqC, off]

/-- The difference of the quadratic forms of two fields along a vector `e` with coordinates of
absolute value at most `2`. -/
lemma normSq_sub_le {h M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {x e : Fin 2 → ℝ} {E : ℝ}
    (hE : ∀ i j, |h x i j - M x i j| ≤ E) (he : ∀ i, |e i| ≤ 2) :
    |normSq h x e - normSq M x e| ≤ 16 * E := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 0 0)
  have key : normSq h x e - normSq M x e =
      ∑ i, ∑ j, (h x i j - M x i j) * (e i * e j) := by
    simp only [normSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [key]
  have hb : ∀ i j, |(h x i j - M x i j) * (e i * e j)| ≤ 4 * E := by
    intro i j
    rw [abs_mul, abs_mul]
    have h1 := hE i j
    have h2 := he i
    have h3 := he j
    calc |h x i j - M x i j| * (|e i| * |e j|) ≤ E * (2 * 2) := by
          gcongr
      _ = 4 * E := by ring
  calc _ ≤ ∑ i, |∑ j, (h x i j - M x i j) * (e i * e j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(h x i j - M x i j) * (e i * e j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 4 * E :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = 16 * E := by simp [Fin.sum_univ_two]; ring

/-- The edge variations of two fields differ by at most `16 E` if the entries differ by at most
`E` on the cube `‖x - P‖ ≤ s`, for edges between points of the star. -/
lemma edgeVar_sub_le {h M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ i j, Continuous fun x => h x i j) (hM : ∀ i j, Continuous fun x => M x i j)
    {P : Fin 2 → ℝ} {s E : ℝ} (hs : 0 < s)
    (hE : ∀ x, ‖x - P‖ ≤ s → ∀ i j, |h x i j - M x i j| ≤ E) {p q : Fin 2 → ℝ}
    (hp : ∀ i, |p i| ≤ 1) (hq : ∀ i, |q i| ≤ 1) :
    |edgeVar h s P p q - edgeVar M s P p q| ≤ 16 * E := by
  have hcont : ∀ (N : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ i j, Continuous fun x => N x i j) →
      Continuous fun t : ℝ => normSq N (P + s • (p + t • (q - p))) (q - p) := by
    intro N hN
    simp only [normSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  unfold edgeVar
  rw [← intervalIntegral.integral_sub ((hcont h hc).intervalIntegrable _ _)
    ((hcont M hM).intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => normSq h (P + s • (p + t • (q - p))) (q - p) -
      normSq M (P + s • (p + t • (q - p))) (q - p)) (C := 16 * E) (by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [Real.norm_eq_abs]
      refine normSq_sub_le (fun i j => hE _ ?_ i j) (fun i => ?_)
      · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
        calc s * ‖p + t • (q - p)‖ ≤ s * 1 := by
              gcongr
              rw [pi_norm_le_iff_of_nonneg zero_le_one]
              intro i
              simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs]
              have := hp i; have := hq i
              rw [abs_le] at *
              constructor <;> nlinarith
          _ = s := mul_one s
      · simp only [Pi.sub_apply]
        have := hp i; have := hq i
        calc |q i - p i| ≤ |q i| + |p i| := abs_sub _ _
          _ ≤ 2 := by linarith)
  simpa [Real.norm_eq_abs] using this

/-- The entries of the quadratic model are continuous. -/
lemma continuous_modelField (J00 J01 J11 : Jet) (P : Fin 2 → ℝ) (i j : Fin 2) :
    Continuous fun x => modelField J00 J01 J11 P x i j := by
  fin_cases i <;> fin_cases j <;> simp [modelField, Jet.eval] <;> fun_prop

/-- **The local error of the linearized deficit.** If every entry of `h` is within `K s³` of its
quadratic Taylor polynomial (the jets `J00, J01, J11`) on the cube `‖x - P‖ ≤ s`, then
`|linDef h s P - s² · curv| ≤ 336 K s³`. -/
theorem linDef_taylor {h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ i j, Continuous fun x => h x i j) {P : Fin 2 → ℝ} {s K : ℝ} (hs : 0 < s)
    (J00 J01 J11 : Jet)
    (hT : ∀ x, ‖x - P‖ ≤ s → ∀ i j, |h x i j - modelField J00 J01 J11 P x i j| ≤ K * s ^ 3) :
    |linDef h s P - s ^ 2 * curv J00 J01 J11| ≤ 336 * K * s ^ 3 := by
  set M := modelField J00 J01 J11 P with hMdef
  have hK : 0 ≤ K * s ^ 3 := (abs_nonneg _).trans (hT P (by simp [hs.le]) 0 0)
  have hM : ∀ i j, Continuous fun x => M x i j := continuous_modelField J00 J01 J11 P
  have h0 : ∀ i, |(0 : Fin 2 → ℝ) i| ≤ 1 := fun i => by simp
  have hA : ∀ j, |varA h s P j - varA M s P j| ≤ 16 * (K * s ^ 3) := fun j =>
    edgeVar_sub_le hc hM hs hT h0 (abs_off_le j)
  have hB : ∀ j, |varB h s P j - varB M s P j| ≤ 16 * (K * s ^ 3) := fun j =>
    edgeVar_sub_le hc hM hs hT h0 (abs_off_le (j + 1))
  have hC : ∀ j, |varC h s P j - varC M s P j| ≤ 16 * (K * s ^ 3) := fun j =>
    edgeVar_sub_le hc hM hs hT (abs_off_le (j + 1)) (abs_off_le j)
  rw [← linDef_model J00 J01 J11 P s, ← hMdef]
  have hdiff : linDef h s P - linDef M s P = -∑ j : Fin 6,
      (2 * (varC h s P j - varC M s P j)
        - (sqA j - sqB j + sqC j) / sqA j * (varA h s P j - varA M s P j)
        - (sqB j - sqA j + sqC j) / sqB j * (varB h s P j - varB M s P j)) / 4 := by
    unfold linDef
    rw [neg_sub_neg, ← neg_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : sqA j ≠ 0 := (sq_facts j).1.ne'
    have h2 : sqB j ≠ 0 := (sq_facts j).2.1.ne'
    field_simp
    ring
  rw [hdiff, abs_neg]
  have hterm : ∀ j : Fin 6, |(2 * (varC h s P j - varC M s P j)
        - (sqA j - sqB j + sqC j) / sqA j * (varA h s P j - varA M s P j)
        - (sqB j - sqA j + sqC j) / sqB j * (varB h s P j - varB M s P j)) / 4| ≤
      14 * (16 * (K * s ^ 3)) / 4 := by
    intro j
    obtain ⟨c1, c2⟩ := coef_bound j
    have e1 := hA j
    have e2 := hB j
    have e3 := hC j
    set E := 16 * (K * s ^ 3)
    have hE : 0 ≤ E := by positivity
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
    calc _ ≤ |2 * (varC h s P j - varC M s P j)| +
          |(sqA j - sqB j + sqC j) / sqA j * (varA h s P j - varA M s P j)| +
          |(sqB j - sqA j + sqC j) / sqB j * (varB h s P j - varB M s P j)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ 2 * E + 6 * E + 6 * E := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          gcongr
      _ = 14 * E := by ring
  calc _ ≤ ∑ j : Fin 6, |(2 * (varC h s P j - varC M s P j)
        - (sqA j - sqB j + sqC j) / sqA j * (varA h s P j - varA M s P j)
        - (sqB j - sqA j + sqC j) / sqB j * (varB h s P j - varB M s P j)) / 4| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 6, 14 * (16 * (K * s ^ 3)) / 4 := Finset.sum_le_sum fun j _ => hterm j
    _ = 336 * K * s ^ 3 := by simp; ring

end

end Lightlike.Regge.Linear
