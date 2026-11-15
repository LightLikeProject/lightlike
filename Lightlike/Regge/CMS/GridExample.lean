import Mathlib
import Lightlike.Regge.CMS.Triangulation
import Lightlike.Regge.CMS.NonVacuity

/-!
# A grid patch with a non-empty interior (RC6b)

A `4 × 4` grid of vertices `h (a, b)` is cut into `3 × 3` squares, each split by the diagonal from
its lower-left to its upper-right corner into two right triangles (18 triangles). The four central
vertices form `V`, each with a full star of six triangles; the two triangles of the central square
have all three corners in `V`, so the interior union of
`cms_convergence_triangulation` is non-empty.

This file proves the combinatorial and geometric hypotheses: the triangles overlap only in null
sets (three families of null lines) and each lies in a unit-scaled square.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- Position of the grid vertex `(a, b)`. -/
def gP (h : ℝ) (v : ℕ × ℕ) : Fin 2 → ℝ := ![h * v.1, h * v.2]

/-- Index of a triangle: the square `(i, j)` and which half (`true`: lower right). -/
abbrev GT (m : ℕ) := Fin m × Fin m × Bool

/-- Corners of the triangles. -/
def gC {m : ℕ} : GT m → Fin 3 → ℕ × ℕ
  | (i, j, true) => ![((i : ℕ), (j : ℕ)), ((i : ℕ) + 1, (j : ℕ)), ((i : ℕ) + 1, (j : ℕ) + 1)]
  | (i, j, false) => ![((i : ℕ), (j : ℕ)), ((i : ℕ) + 1, (j : ℕ) + 1), ((i : ℕ), (j : ℕ) + 1)]

/-- Bounds satisfied by a point of the triangle `(i, j, b)`. -/
theorem grid_mem {m : ℕ} {h : ℝ} (hh : 0 ≤ h) (i j : Fin m) (b : Bool) {x : Fin 2 → ℝ}
    (hx : x ∈ cell (gP h) gC (i, j, b)) :
    h * i ≤ x 0 ∧ x 0 ≤ h * (i + 1) ∧ h * j ≤ x 1 ∧ x 1 ≤ h * (j + 1) ∧
      (b = true → h * ((i : ℝ) - j) ≤ x 0 - x 1) ∧ (b = false → x 0 - x 1 ≤ h * ((i : ℝ) - j)) := by
  obtain ⟨y, ⟨hy0, hy1, hy2⟩, rfl⟩ := hx
  have p0 := mul_nonneg hh hy0
  have p1 := mul_nonneg hh hy1
  cases b <;> simp [triMap, gP, gC] <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_nonneg hh (sub_nonneg.2 hy2)]

/-- Two numbers in the intervals `[i h, (i+1) h]` and `[i' h, (i'+1) h]` with `i ≠ i'` lie on a
grid line. -/
theorem line_of_ne {h x : ℝ} (hh : 0 < h) {i i' : ℕ} (hne : i ≠ i')
    (h1 : h * i ≤ x ∧ x ≤ h * (i + 1)) (h2 : h * i' ≤ x ∧ x ≤ h * (i' + 1)) :
    ∃ k : ℕ, x = h * k := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hlt
    exact ⟨i + 1, by push_cast; nlinarith [h1.2, h2.1]⟩
  · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    exact ⟨i' + 1, by push_cast; nlinarith [h1.1, h2.2]⟩

theorem null_coord (k : Fin 2) (c : ℝ) : volume {x : Fin 2 → ℝ | x k = c} = 0 :=
  Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) k c

theorem null_diag (c : ℝ) : volume {x : Fin 2 → ℝ | x 0 - x 1 = c} = 0 := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]
  have hdet : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin']; simp [M, Matrix.det_fin_two]
  have hpre : {x : Fin 2 → ℝ | x 0 - x 1 = c} = (Matrix.toLin' M) ⁻¹' {y | y 0 = c} := by
    ext x; simp [M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring_nf
  rw [hpre, Measure.addHaar_preimage_linearMap volume hdet, null_coord 0 c, mul_zero]

/-- Distinct triangles of the patch overlap in a null set. -/
theorem grid_disjoint {m : ℕ} {h : ℝ} (hh : 0 < h) (t t' : GT m) (hne : t ≠ t') :
    AEDisjoint volume (cell (gP h) gC t) (cell (gP h) gC t') := by
  obtain ⟨i, j, b⟩ := t
  obtain ⟨i', j', b'⟩ := t'
  have hsub : cell (gP h) gC (i, j, b) ∩ cell (gP h) gC (i', j', b') ⊆
      (⋃ k : ℕ, {x | x 0 = h * k}) ∪ (⋃ k : ℕ, {x | x 1 = h * k}) ∪
        {x | x 0 - x 1 = h * ((i : ℝ) - j)} := by
    rintro x ⟨hx, hx'⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := grid_mem hh.le i j b hx
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := grid_mem hh.le i' j' b' hx'
    by_cases hi : (i : ℕ) = i'
    · by_cases hj : (j : ℕ) = j'
      · have hb : b ≠ b' := by
          intro hb; subst hb; exact hne (by simp [Fin.ext hi, Fin.ext hj])
        have hij : (i : ℝ) = i' := by exact_mod_cast hi
        have hjj : (j : ℝ) = j' := by exact_mod_cast hj
        right
        cases b <;> cases b' <;> simp at hb a5 a6 b5 b6 ⊢ <;> rw [hij, hjj] at * <;> linarith
      · left; right
        obtain ⟨k, hk⟩ := line_of_ne hh hj ⟨a3, a4⟩ ⟨b3, b4⟩
        exact mem_iUnion.2 ⟨k, hk⟩
    · left; left
      obtain ⟨k, hk⟩ := line_of_ne hh hi ⟨a1, a2⟩ ⟨b1, b2⟩
      exact mem_iUnion.2 ⟨k, hk⟩
  have h0 : volume (⋃ k : ℕ, {x : Fin 2 → ℝ | x 0 = h * k}) = 0 :=
    measure_iUnion_null fun k => null_coord 0 _
  have h1 : volume (⋃ k : ℕ, {x : Fin 2 → ℝ | x 1 = h * k}) = 0 :=
    measure_iUnion_null fun k => null_coord 1 _
  exact measure_mono_null hsub (measure_union_null (measure_union_null h0 h1) (null_diag _))

/-- The interior vertices `(a, b)`, `1 ≤ a, b ≤ m - 1`, of the `m × m` grid. -/
def gV (m : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 (m - 1) ×ˢ Finset.Icc 1 (m - 1)

theorem mem_gV {m : ℕ} {v : ℕ × ℕ} : v ∈ gV m ↔ 1 ≤ v.1 ∧ v.1 ≤ m - 1 ∧ 1 ≤ v.2 ∧ v.2 ≤ m - 1 := by
  simp [gV, Finset.mem_product, Finset.mem_Icc]; tauto

theorem zmod6_cases (j : ZMod 6) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  revert j; decide

/-- Neighbours of `v`, in cyclic order. -/
def gnb (v : ℕ × ℕ) : ZMod 6 → ℕ × ℕ :=
  ![(v.1 + 1, v.2), (v.1 + 1, v.2 + 1), (v.1, v.2 + 1), (v.1 - 1, v.2), (v.1 - 1, v.2 - 1),
    (v.1, v.2 - 1)]

/-- The six triangles around `v`, in the order of the neighbours. -/
def gtt (m : ℕ) [NeZero m] (v : ℕ × ℕ) : ZMod 6 → GT m :=
  ![(Fin.ofNat m v.1, Fin.ofNat m v.2, true), (Fin.ofNat m v.1, Fin.ofNat m v.2, false),
    (Fin.ofNat m (v.1 - 1), Fin.ofNat m v.2, true),
    (Fin.ofNat m (v.1 - 1), Fin.ofNat m (v.2 - 1), false),
    (Fin.ofNat m (v.1 - 1), Fin.ofNat m (v.2 - 1), true),
    (Fin.ofNat m v.1, Fin.ofNat m (v.2 - 1), false)]

theorem grid_inj (m : ℕ) : ∀ t : GT m, Function.Injective (gC t) := by
  rintro ⟨i, j, b⟩ a a' h
  cases b <;> fin_cases a <;> fin_cases a' <;> simp [gC, Prod.ext_iff] at h ⊢ <;> omega

theorem ofNat_val {m : ℕ} [NeZero m] {a : ℕ} (h : a < m) : (Fin.ofNat m a : ℕ) = a := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt h]

theorem grid_star (m : ℕ) [NeZero m] : ∀ v ∈ gV m, Function.Injective (gtt m v) ∧
    ∀ t : GT m, (∃ k, gC t k = v) ↔ ∃ j, gtt m v j = t := by
  intro v hv
  obtain ⟨h1, h2, h3, h4⟩ := mem_gV.1 hv
  have a1 : (Fin.ofNat m v.1 : ℕ) = v.1 := ofNat_val (by omega)
  have a2 : (Fin.ofNat m (v.1 - 1) : ℕ) = v.1 - 1 := ofNat_val (by omega)
  have b1 : (Fin.ofNat m v.2 : ℕ) = v.2 := ofNat_val (by omega)
  have b2 : (Fin.ofNat m (v.2 - 1) : ℕ) = v.2 - 1 := ofNat_val (by omega)
  have c1 : v.1 % m = v.1 := Nat.mod_eq_of_lt (by omega)
  have c2 : (v.1 - 1) % m = v.1 - 1 := Nat.mod_eq_of_lt (by omega)
  have d1 : v.2 % m = v.2 := Nat.mod_eq_of_lt (by omega)
  have d2 : (v.2 - 1) % m = v.2 - 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro j j' h
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod6_cases j' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2] at h ⊢ <;> omega
  · rintro ⟨i, j, b⟩
    constructor
    · rintro ⟨k, hk⟩
      cases b <;> fin_cases k <;> simp [gC, Prod.ext_iff] at hk
      · refine ⟨1, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
      · refine ⟨3, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
      · refine ⟨5, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
      · refine ⟨0, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
      · refine ⟨2, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
      · refine ⟨4, ?_⟩; simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2]; omega
    · rintro ⟨j', hj⟩
      rcases zmod6_cases j' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gtt, Prod.ext_iff, Fin.ext_iff, a1, a2, b1, b2, c1, c2, d1, d2] at hj <;> obtain ⟨hi, hj, rfl⟩ := hj
      · exact ⟨0, by simp [gC, Prod.ext_iff]; omega⟩
      · exact ⟨0, by simp [gC, Prod.ext_iff]; omega⟩
      · exact ⟨1, by simp [gC, Prod.ext_iff]; omega⟩
      · exact ⟨1, by simp [gC, Prod.ext_iff]; omega⟩
      · exact ⟨2, by simp [gC, Prod.ext_iff]; omega⟩
      · exact ⟨2, by simp [gC, Prod.ext_iff]; omega⟩

theorem grid_corn (m : ℕ) [NeZero m] : ∀ v ∈ gV m, ∀ j : ZMod 6,
    ∃ σ : Equiv.Perm (Fin 3), gC (gtt m v j) ∘ σ = ![v, gnb v j, gnb v (j + 1)] := by
  intro v hv j
  obtain ⟨h1, h2, h3, h4⟩ := mem_gV.1 hv
  have a1 : (Fin.ofNat m v.1 : ℕ) = v.1 := ofNat_val (by omega)
  have a2 : (Fin.ofNat m (v.1 - 1) : ℕ) = v.1 - 1 := ofNat_val (by omega)
  have b1 : (Fin.ofNat m v.2 : ℕ) = v.2 := ofNat_val (by omega)
  have b2 : (Fin.ofNat m (v.2 - 1) : ℕ) = v.2 - 1 := ofNat_val (by omega)
  have c1 : v.1 % m = v.1 := Nat.mod_eq_of_lt (by omega)
  have c2 : (v.1 - 1) % m = v.1 - 1 := Nat.mod_eq_of_lt (by omega)
  have d1 : v.2 % m = v.2 := Nat.mod_eq_of_lt (by omega)
  have d2 : (v.2 - 1) % m = v.2 - 1 := Nat.mod_eq_of_lt (by omega)
  have e0 : (0 : ZMod 6) + 1 = 1 := by decide
  have e1 : (1 : ZMod 6) + 1 = 2 := by decide
  have e2 : (2 : ZMod 6) + 1 = 3 := by decide
  have e3 : (3 : ZMod 6) + 1 = 4 := by decide
  have e4 : (4 : ZMod 6) + 1 = 5 := by decide
  have e5 : (5 : ZMod 6) + 1 = 0 := by decide
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨1, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e0, a1, a2, b1, b2, c1, c2, d1, d2, Prod.ext_iff]
  · refine ⟨1, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e1, a1, a2, b1, b2, c1, c2, d1, d2, Prod.ext_iff]
  · refine ⟨finRotate 3, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e2, a1, a2, b1, b2, Prod.ext_iff] <;> omega
  · refine ⟨finRotate 3, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e3, a1, a2, b1, b2, Prod.ext_iff] <;> omega
  · refine ⟨finRotate 3 * finRotate 3, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e4, a1, a2, b1, b2, Prod.ext_iff] <;> omega
  · refine ⟨finRotate 3 * finRotate 3, ?_⟩
    funext k; fin_cases k <;> simp [gC, gtt, gnb, e5, a1, a2, b1, b2, Prod.ext_iff] <;> omega

/-- The neighbour offsets, scaled by `h`. -/
def gW (h : ℝ) : ZMod 6 → Fin 2 → ℝ :=
  ![![h, 0], ![h, h], ![0, h], ![-h, 0], ![-h, -h], ![0, -h]]

theorem gP_nb (h : ℝ) {v : ℕ × ℕ} (h1 : 1 ≤ v.1) (h2 : 1 ≤ v.2) (j : ZMod 6) :
    gP h (gnb v j) - gP h v = gW h j := by
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> ext m <;> fin_cases m <;>
    simp [gP, gnb, gW, Nat.cast_sub h1, Nat.cast_sub h2] <;> ring

theorem gW_norm {h : ℝ} (hh : 0 ≤ h) (j : ZMod 6) : ‖gW h j‖ ≤ h := by
  rw [pi_norm_le_iff_of_nonneg hh]
  intro i
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp [gW, abs_of_nonneg hh, hh]

theorem gW_det2 (h : ℝ) (j : ZMod 6) : det2 (gW h j) (gW h (j + 1)) = h ^ 2 := by
  have e0 : (0 : ZMod 6) + 1 = 1 := by decide
  have e1 : (1 : ZMod 6) + 1 = 2 := by decide
  have e2 : (2 : ZMod 6) + 1 = 3 := by decide
  have e3 : (3 : ZMod 6) + 1 = 4 := by decide
  have e4 : (4 : ZMod 6) + 1 = 5 := by decide
  have e5 : (5 : ZMod 6) + 1 = 0 := by decide
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [det2, gW, e0, e1, e2, e3, e4, e5] <;> ring

theorem norm_toC (x : Fin 2 → ℝ) : ‖toC x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp [toC]; ring_nf

theorem angle_quarter {x y : Fin 2 → ℝ} (hn : ‖toC x‖ * ‖toC y‖ ≠ 0)
    (hi : inner ℝ (toC x) (toC y) = ‖toC x‖ * ‖toC y‖ * (√2 / 2)) :
    InnerProductGeometry.angle (toC x) (toC y) = π / 4 := by
  unfold InnerProductGeometry.angle
  rw [hi, mul_div_cancel_left₀ _ hn, ← Real.cos_pi_div_four, Real.arccos_cos] <;> linarith [Real.pi_pos]

theorem gW_angle {h : ℝ} (hh : 0 < h) (j : ZMod 6) :
    InnerProductGeometry.angle (toC (gW h j)) (toC (gW h (j + 1))) =
      ![π / 4, π / 4, π / 2, π / 4, π / 4, π / 2] j := by
  have e0 : (0 : ZMod 6) + 1 = 1 := by decide
  have e1 : (1 : ZMod 6) + 1 = 2 := by decide
  have e2 : (2 : ZMod 6) + 1 = 3 := by decide
  have e3 : (3 : ZMod 6) + 1 = 4 := by decide
  have e4 : (4 : ZMod 6) + 1 = 5 := by decide
  have e5 : (5 : ZMod 6) + 1 = 0 := by decide
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hsq : ∀ a : ℝ, √(a ^ 2 + a ^ 2) = |a| * √2 := fun a => by
    rw [← two_mul, Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, mul_comm]
  have hpi2 : ∀ x y : Fin 2 → ℝ, ‖toC x‖ * ‖toC y‖ ≠ 0 →
      inner ℝ (toC x) (toC y) = 0 → InnerProductGeometry.angle (toC x) (toC y) = π / 2 :=
    fun x y _ hi => (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).1 hi
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e0]; apply angle_quarter <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, abs_of_pos hh, hsq, Real.sqrt_sq hh.le, hh.ne'] <;>
      nlinarith [hs, mul_pos hh hh]
  · rw [e1]; apply angle_quarter <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, abs_of_pos hh, hsq, Real.sqrt_sq hh.le, hh.ne'] <;>
      nlinarith [hs, mul_pos hh hh]
  · rw [e2]; apply hpi2 <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, Real.sqrt_sq hh.le, hh.ne']
  · rw [e3]; apply angle_quarter <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, abs_of_pos hh, hsq, Real.sqrt_sq hh.le, hh.ne'] <;>
      nlinarith [hs, mul_pos hh hh]
  · rw [e4]; apply angle_quarter <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, abs_of_pos hh, hsq, Real.sqrt_sq hh.le, hh.ne'] <;>
      nlinarith [hs, mul_pos hh hh]
  · rw [e5]; apply hpi2 <;> (try simp only [norm_toC]) <;>
      simp [gW, Complex.inner, toC, Real.sqrt_sq hh.le, hh.ne']

theorem gW_angle_sum {h : ℝ} (hh : 0 < h) :
    ∑ j : ZMod 6, InnerProductGeometry.angle (toC (gW h j)) (toC (gW h (j + 1))) = 2 * π := by
  rw [Finset.sum_congr rfl fun j _ => gW_angle hh j]
  show ∑ j : Fin 6, ![π / 4, π / 4, π / 2, π / 4, π / 4, π / 2] j = 2 * π
  simp [Fin.sum_univ_succ]; ring

/-- The triangles of the `m × m` grid lie in the box `[0, h m]²`. -/
theorem grid_in_box {m : ℕ} {h : ℝ} (hh : 0 < h) (t : GT m) :
    cell (gP h) gC t ⊆ Icc (0 : Fin 2 → ℝ) (fun _ => h * m) := by
  obtain ⟨i, j, b⟩ := t
  intro x hx
  obtain ⟨a1, a2, a3, a4, -, -⟩ := grid_mem hh.le i j b hx
  have hi : (i : ℝ) + 1 ≤ m := by have := i.isLt; exact_mod_cast this
  have hj : (j : ℝ) + 1 ≤ m := by have := j.isLt; exact_mod_cast this
  have i0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have j0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k <;> simp <;> nlinarith [mul_nonneg hh.le i0,
    mul_nonneg hh.le j0, mul_le_mul_of_nonneg_left hi hh.le, mul_le_mul_of_nonneg_left hj hh.le]

theorem grid_edge {m : ℕ} {h : ℝ} (hh : 0 < h) (t : GT m) (k : Fin 3) :
    dist (gP h (gC t k)) (gP h (gC t 0)) ≤ h := by
  obtain ⟨i, j, b⟩ := t
  rw [dist_pi_le_iff hh.le]
  intro n
  rw [Real.dist_eq]
  cases b <;> fin_cases k <;> fin_cases n <;> simp [gP, gC, abs_of_nonneg hh.le, hh.le] <;>
    first | (rw [abs_of_nonneg (by linarith)]; linarith) | linarith

/-- At most `8 m` triangles of the `m × m` grid have a corner outside the interior vertices: they
lie in the squares of the outer ring. -/
theorem grid_boundary_card_le (m : ℕ) [NeZero m] :
    (Finset.univ.filter fun t : GT m => cornersIn gC (gV m) t ≠ 3).card ≤ 8 * m := by
  have hsub : (Finset.univ.filter fun t : GT m => cornersIn gC (gV m) t ≠ 3) ⊆
      ((Finset.univ : Finset (Fin m × Bool)).image fun p => ((0 : Fin m), p.1, p.2)) ∪
      ((Finset.univ : Finset (Fin m × Bool)).image fun p => (Fin.ofNat m (m - 1), p.1, p.2)) ∪
      ((Finset.univ : Finset (Fin m × Bool)).image fun p => (p.1, (0 : Fin m), p.2)) ∪
      ((Finset.univ : Finset (Fin m × Bool)).image fun p => (p.1, Fin.ofNat m (m - 1), p.2)) := by
    intro t ht
    obtain ⟨i, j, b⟩ := t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hk : ∃ k, gC (i, j, b) k ∉ gV m := by
      by_contra hno
      apply ht
      have : (Finset.univ.filter fun k : Fin 3 => gC (i, j, b) k ∈ gV m) = Finset.univ := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        by_contra hk; exact hno ⟨k, hk⟩
      unfold cornersIn; rw [this]; simp
    obtain ⟨k, hk⟩ := hk
    have hi := i.isLt
    have hj := j.isLt
    have hcase : (i : ℕ) = 0 ∨ (i : ℕ) = m - 1 ∨ (j : ℕ) = 0 ∨ (j : ℕ) = m - 1 := by
      cases b <;> fin_cases k <;> simp [gC, mem_gV] at hk <;> omega
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    rcases hcase with h0 | h0 | h0 | h0
    · left; left; left; exact ⟨(j, b), by simp [Prod.ext_iff, Fin.ext_iff, h0]⟩
    · left; left; right
      exact ⟨(j, b), by simp [Prod.ext_iff, Fin.ext_iff, h0, Nat.mod_eq_of_lt (by omega : m - 1 < m)]⟩
    · left; right; exact ⟨(i, b), by simp [Prod.ext_iff, Fin.ext_iff, h0]⟩
    · right
      exact ⟨(i, b), by simp [Prod.ext_iff, Fin.ext_iff, h0, Nat.mod_eq_of_lt (by omega : m - 1 < m)]⟩
  refine (Finset.card_le_card hsub).trans ?_
  have hc : (Finset.univ : Finset (Fin m × Bool)).card = 2 * m := by simp [mul_comm]
  refine (Finset.card_union_le _ _).trans ?_
  have c1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin m × Bool)))
    (f := fun p : Fin m × Bool => ((0 : Fin m), p.1, p.2))
  have c2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin m × Bool)))
    (f := fun p : Fin m × Bool => (Fin.ofNat m (m - 1), p.1, p.2))
  have c3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin m × Bool)))
    (f := fun p : Fin m × Bool => (p.1, (0 : Fin m), p.2))
  have c4 := Finset.card_image_le (s := (Finset.univ : Finset (Fin m × Bool)))
    (f := fun p : Fin m × Bool => (p.1, Fin.ofNat m (m - 1), p.2))
  have u1 := Finset.card_union_le
    ((Finset.univ : Finset (Fin m × Bool)).image fun p : Fin m × Bool => ((0 : Fin m), p.1, p.2))
    ((Finset.univ : Finset (Fin m × Bool)).image fun p : Fin m × Bool =>
      (Fin.ofNat m (m - 1), p.1, p.2))
  have u2 := Finset.card_union_le
    (((Finset.univ : Finset (Fin m × Bool)).image fun p : Fin m × Bool => ((0 : Fin m), p.1, p.2)) ∪
      ((Finset.univ : Finset (Fin m × Bool)).image fun p : Fin m × Bool =>
        (Fin.ofNat m (m - 1), p.1, p.2)))
    ((Finset.univ : Finset (Fin m × Bool)).image fun p : Fin m × Bool => (p.1, (0 : Fin m), p.2))
  omega

/-- **The convergence bound for the `m × m` grid, for every size and with constants independent of
the size.** In the square `[0, R]²`, for a Riemannian metric `g`, mesh `h` with `h m ≤ R`, the
interior vertices `1 ≤ a, b ≤ m - 1` have full stars of six triangles; the constants `C`, `h₀` do
not depend on `m`. -/
theorem grid_bound_general {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    (hg : IsRiemMetric g univ) {R : ℝ} (hR : 0 < R) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → h ≤ h₀ → h * m ≤ R →
      |∑ v ∈ gV m, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP h v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist g univ (gP h v) (gP h (gnb v j)) ^ 2)
            (dist g univ (gP h v) (gP h (gnb v (j + 1))) ^ 2)
            (dist g univ (gP h (gnb v j)) (gP h (gnb v (j + 1))) ^ 2)) -
        ∫ x in ⋃ t ∈ Finset.univ.filter (fun t : GT m => cornersIn gC (gV m) t = 3),
            cell (gP h) gC t,
          (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (scalarCurvature g x / 2 *
            √(g x).det)| ≤ C * h := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := hg.cms_convergence_triangulation
    (K := Icc (0 : Fin 2 → ℝ) (fun _ => R)) isCompact_Icc (subset_univ _) (ρ := 1) (N := 6)
    (M := R ^ 2) (m := 8 * R) (by positivity) one_pos
    (f := fun _ => 1) (Lf := 0) (LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp)
  refine ⟨C, h₀, hh₀, fun m _ h hh hh0 hR' => ?_⟩
  have hbox : ∀ t : GT m, cell (gP h) gC t ⊆ Icc (0 : Fin 2 → ℝ) (fun _ => R) := fun t =>
    (grid_in_box hh t).trans (Icc_subset_Icc le_rfl fun _ => hR')
  have hV : ∀ v ∈ gV m, 1 ≤ v.1 ∧ 1 ≤ v.2 := fun v hv => by
    obtain ⟨a, -, b, -⟩ := mem_gV.1 hv; exact ⟨a, b⟩
  refine hmain (ℕ × ℕ) (GT m) (gV m) (fun _ => 6) (gP h) gC gnb (gtt m) h hh hh0 ?_ (grid_inj m)
    (fun t t' hne => grid_disjoint hh t t' hne) hbox (grid_edge hh) (grid_star m)
    (grid_corn m) ?_ ?_ ?_ ?_ ?_ ?_
  · have hcard : (gV m).card = (m - 1) * (m - 1) := by simp [gV]
    rw [hcard]
    have h1 : h * ((m - 1 : ℕ) : ℝ) ≤ R := le_trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le m 1) hh.le) hR'
    have h2 : 0 ≤ h * ((m - 1 : ℕ) : ℝ) := by positivity
    push_cast at h1 h2 ⊢
    nlinarith
  · intro v hv
    obtain ⟨a, b, c, d⟩ := mem_gV.1 hv
    have hv1 : (v.1 : ℝ) ≤ m := by exact_mod_cast (by omega : v.1 ≤ m)
    have hv2 : (v.2 : ℝ) ≤ m := by exact_mod_cast (by omega : v.2 ≤ m)
    refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k <;> simp [gP] <;>
      first | positivity | nlinarith [mul_le_mul_of_nonneg_left hv1 hh.le,
        mul_le_mul_of_nonneg_left hv2 hh.le]
  · intro v _; norm_num
  · intro v hv j
    rw [gP_nb h (hV v hv).1 (hV v hv).2]; exact gW_norm hh.le j
  · intro v hv j
    rw [gP_nb h (hV v hv).1 (hV v hv).2, gP_nb h (hV v hv).1 (hV v hv).2, gW_det2]; simp
  · intro v hv
    simp only [gP_nb h (hV v hv).1 (hV v hv).2]
    exact gW_angle_sum hh
  · have hc := grid_boundary_card_le m
    have : ((Finset.univ.filter fun t : GT m => cornersIn gC (gV m) t ≠ 3).card : ℝ) ≤ 8 * m := by
      exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_right this hh.le]

/-- **Non-vacuity, non-degenerate.** The `4 × 4` grid patch with the four central vertices, for any
Riemannian metric `g` on the plane: six triangles per vertex, 2 interior and 16 boundary triangles,
and the bound of the convergence theorem. -/
theorem grid_triangulation_bound_of {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    (hg : IsRiemMetric g univ) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → h ≤ 1 →
      |∑ v ∈ gV 3, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP h v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist g univ (gP h v) (gP h (gnb v j)) ^ 2)
            (dist g univ (gP h v) (gP h (gnb v (j + 1))) ^ 2)
            (dist g univ (gP h (gnb v j)) (gP h (gnb v (j + 1))) ^ 2)) -
        ∫ x in ⋃ t ∈ Finset.univ.filter (fun t : GT 3 => cornersIn gC (gV 3) t = 3),
            cell (gP h) gC t,
          (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (scalarCurvature g x / 2 *
            √(g x).det)| ≤ C * h := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := grid_bound_general hg (R := 3) (by norm_num)
  exact ⟨C, h₀, hh₀, fun h hh hh0 hh1 => hmain 3 h hh hh0 (by push_cast; linarith)⟩

/-- **Non-vacuity, non-degenerate.** The `4 × 4` grid patch with the four central vertices, for the
flat metric: six triangles per vertex, 2 interior and 16 boundary triangles. -/
theorem grid_triangulation_bound :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → h ≤ 1 →
      |∑ v ∈ gV 3, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP h v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist (shearBy fun _ => (0 : ℝ)) univ (gP h v) (gP h (gnb v j)) ^ 2)
            (dist (shearBy fun _ => (0 : ℝ)) univ (gP h v) (gP h (gnb v (j + 1))) ^ 2)
            (dist (shearBy fun _ => (0 : ℝ)) univ (gP h (gnb v j)) (gP h (gnb v (j + 1))) ^ 2)) -
        ∫ x in ⋃ t ∈ Finset.univ.filter (fun t : GT 3 => cornersIn gC (gV 3) t = 3),
            cell (gP h) gC t,
          (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (scalarCurvature (shearBy fun _ => (0 : ℝ)) x / 2 *
            √((shearBy fun _ => (0 : ℝ)) x).det)| ≤ C * h :=
  grid_triangulation_bound_of (isRiemMetric_shearBy contDiff_const)

theorem grid_boundary_card :
    (Finset.univ.filter fun t : GT 3 => cornersIn gC (gV 3) t ≠ 3).card = 16 := by decide

theorem grid_interior_card :
    (Finset.univ.filter fun t : GT 3 => cornersIn gC (gV 3) t = 3).card = 2 := by decide

/-- **Non-degeneracy.** The interior triangles (all three corners in `gV`) are the two halves of
the central square, and their union has positive area, so the integral region of
`grid_triangulation_bound` is not empty. -/
theorem grid_interior_positive {h : ℝ} (hh : 0 < h) :
    0 < volume (⋃ t ∈ Finset.univ.filter (fun t : GT 3 => cornersIn gC (gV 3) t = 3), cell (gP h) gC t) := by
  have hmem : ((1 : Fin 3), (1 : Fin 3), true) ∈
      Finset.univ.filter (fun t : GT 3 => cornersIn gC (gV 3) t = 3) := by decide
  refine lt_of_lt_of_le ?_ (measure_mono (subset_biUnion_of_mem (u := fun t => cell (gP h) gC t) hmem))
  rw [cell, volume_tri]
  have e : det2 (gP h ((gC ((1 : Fin 3), (1 : Fin 3), true)) 1) - gP h ((gC ((1 : Fin 3), (1 : Fin 3), true)) 0))
      (gP h ((gC ((1 : Fin 3), (1 : Fin 3), true)) 2) - gP h ((gC ((1 : Fin 3), (1 : Fin 3), true)) 0)) = h ^ 2 := by
    simp [gC, gP, det2]; ring
  rw [e, abs_of_pos (by positivity)]
  positivity

/-- **Wrong-model check.** The same four neighbours listed clockwise (`j ↦ -j`) have negative
`det2` for every consecutive pair, so the fatness hypothesis `ρ h² ≤ det2` of the theorem fails for
every `ρ > 0`: a star that is not positively oriented is rejected, while the counter-clockwise
star satisfies it with `ρ = 1` (`starW_det2`). -/
theorem reversed_star_not_fat {h ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ) :
    (∀ j : ZMod 4, det2 (starW h (-j)) (starW h (-(j + 1))) = -h ^ 2) ∧
      ∀ j : ZMod 4, ¬ ρ * h ^ 2 ≤ det2 (starW h (-j)) (starW h (-(j + 1))) := by
  have hd : ∀ j : ZMod 4, det2 (starW h (-j)) (starW h (-(j + 1))) = -h ^ 2 := by
    intro j
    have e0 : -(0 : ZMod 4) = 0 := by decide
    have e1 : -(0 + 1 : ZMod 4) = 3 := by decide
    have e2 : -(1 : ZMod 4) = 3 := by decide
    have e3 : -(1 + 1 : ZMod 4) = 2 := by decide
    have e4 : -(2 : ZMod 4) = 2 := by decide
    have e5 : -(2 + 1 : ZMod 4) = 1 := by decide
    have e6 : -(3 : ZMod 4) = 1 := by decide
    have e7 : -(3 + 1 : ZMod 4) = 0 := by decide
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp [det2, starW, e0, e1, e2, e3, e4, e5, e6, e7] <;> ring
  refine ⟨hd, fun j hj => ?_⟩
  rw [hd] at hj
  nlinarith [mul_pos hρ (pow_pos hh 2), pow_pos hh 2]

end Lightlike.CMS
