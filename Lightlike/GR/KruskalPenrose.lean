import Lightlike.GR.KruskalRegions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Penrose diagram of the Kruskal–Szekeres extension

Gap row G1-020. Source read: S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7,
eqs. (7.103)-(7.105) and the text after them (printed pages 197-198): with the null Kruskal coordinates `u'`, `v'`,
in which `ds² = -(16 G³M³/r) e^{-r/2GM} (du' dv' + dv' du') + r² dΩ²`, put `u'' = arctan (u'/√(2GM))`,
`v'' = arctan (v'/√(2GM))`; "the `(u'', v'')` part of the metric ... is now conformally related to Minkowski space.
In the new coordinates the singularities at `r = 0` are straight lines".

Here the null coordinates are `V = T + X`, `U = T - X`, and `p = arctan V`, `q = arctan U` (`penroseMap`):

* the Kruskal domain `X² - T² > -1` is mapped bijectively onto the bounded region `|p| < π/2`, `|q| < π/2`,
  `|p + q| < π/2` (`bijOn_penroseMap`), with inverse `T = (tan p + tan q)/2`, `X = (tan p - tan q)/2`
  (`penroseInv`);
* the singularity `r → 0`, i.e. `T² - X² → 1`, is the pair of straight lines `p + q = ±π/2`
  (`tan_mul_tan_eq_one_of_abs_add`), and the horizon `T = ±X` is `p = 0` or `q = 0` (`penroseMap_horizon_iff`);
* the Kruskal metric in the coordinates `(p, q, θ, φ)` is
  `-(h(r) / (2 cos² p cos² q)) (dp dq + dq dp) + r² dΩ²` (`pullback_kruskal_penroseInv`): its `(p, q)` part is
  the flat metric `-(dp dq + dq dp)/2` times the positive factor `h(r) / (cos² p cos² q)`.

**Differences from the source.** (kind: convention) No factor `√(2GM)` inside the arctangent: our `T`, `X` are
dimensionless. (kind: representation) The source states the ranges `-π/2 < u'', v'' < π/2`, `-π < u'' + v'' < π`
(the last one follows from the first two); the region proved here is the exact image, bounded by the lines
`p + q = ±π/2` in our sign convention `U = T - X`. Conformal infinity (`I±`, `i⁰`, `i±`) as points added to the
manifold is not formalized.
-/

open Matrix Real Set

noncomputable section

namespace Lightlike

/-! ### A trigonometric lemma -/

/-- For `p`, `q` in `(-π/2, π/2)`: `tan p tan q < 1` iff `|p + q| < π/2`. -/
lemma tan_mul_tan_lt_one_iff {p q : ℝ} (hp : p ∈ Ioo (-(π / 2)) (π / 2))
    (hq : q ∈ Ioo (-(π / 2)) (π / 2)) : tan p * tan q < 1 ↔ |p + q| < π / 2 := by
  have hcp := cos_pos_of_mem_Ioo hp
  have hcq := cos_pos_of_mem_Ioo hq
  have h1 : tan p * tan q < 1 ↔ 0 < cos (p + q) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, cos_add, div_mul_div_comm, div_lt_one (mul_pos hcp hcq)]
    constructor <;> intro h <;> linarith
  rw [h1]
  constructor
  · intro h
    by_contra hlt
    rcases le_abs.1 (not_lt.1 hlt) with h2 | h2
    · have := cos_nonpos_of_pi_div_two_le_of_le h2 (by linarith [hp.2, hq.2, pi_pos])
      linarith
    · have := cos_nonpos_of_pi_div_two_le_of_le h2 (by linarith [hp.1, hq.1, pi_pos])
      rw [cos_neg] at this
      linarith
  · intro h
    exact cos_pos_of_mem_Ioo ⟨(abs_lt.1 h).1, (abs_lt.1 h).2⟩

/-- **The singularity lines are straight**: on `p + q = ±π/2` one has `tan p tan q = 1`, which is `T² - X² = 1`,
the limit `r → 0`. -/
lemma tan_mul_tan_eq_one_of_abs_add {p q : ℝ} (hp : p ∈ Ioo (-(π / 2)) (π / 2))
    (hq : q ∈ Ioo (-(π / 2)) (π / 2)) (h : |p + q| = π / 2) : tan p * tan q = 1 := by
  have hcp := cos_pos_of_mem_Ioo hp
  have hcq := cos_pos_of_mem_Ioo hq
  have hc : cos (p + q) = 0 := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ π / 2) |>.1 h with h1 | h1
    · rw [h1, cos_pi_div_two]
    · rw [h1, cos_neg, cos_pi_div_two]
  rw [cos_add] at hc
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_mul_div_comm, div_eq_one_iff_eq (mul_pos hcp hcq).ne']
  linarith

/-! ### The compactification -/

/-- The Penrose coordinates `(p, q, θ, φ) = (arctan (T + X), arctan (T - X), θ, φ)`. -/
def penroseMap (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![arctan (y 0 + y 1), arctan (y 0 - y 1), y 2, y 3]

/-- The inverse: `T = (tan p + tan q)/2`, `X = (tan p - tan q)/2`. -/
def penroseInv (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(tan (z 0) + tan (z 1)) / 2, (tan (z 0) - tan (z 1)) / 2, z 2, z 3]

/-- The Penrose diagram: `|p| < π/2`, `|q| < π/2`, `|p + q| < π/2` (and `0 < θ < π`). -/
def penroseU : Set (Fin 4 → ℝ) :=
  {z | z 0 ∈ Ioo (-(π / 2)) (π / 2) ∧ z 1 ∈ Ioo (-(π / 2)) (π / 2) ∧ |z 0 + z 1| < π / 2 ∧
    0 < z 2 ∧ z 2 < π}

lemma penroseInv_penroseMap (y : Fin 4 → ℝ) : penroseInv (penroseMap y) = y := by
  ext i
  fin_cases i
  · show (tan (arctan (y 0 + y 1)) + tan (arctan (y 0 - y 1))) / 2 = y 0
    rw [tan_arctan, tan_arctan]; ring
  · show (tan (arctan (y 0 + y 1)) - tan (arctan (y 0 - y 1))) / 2 = y 1
    rw [tan_arctan, tan_arctan]; ring
  · rfl
  · rfl

lemma penroseMap_penroseInv {z : Fin 4 → ℝ} (hz : z ∈ penroseU) : penroseMap (penroseInv z) = z := by
  ext i
  fin_cases i
  · show arctan ((tan (z 0) + tan (z 1)) / 2 + (tan (z 0) - tan (z 1)) / 2) = z 0
    rw [show (tan (z 0) + tan (z 1)) / 2 + (tan (z 0) - tan (z 1)) / 2 = tan (z 0) by ring,
      arctan_tan hz.1.1 hz.1.2]
  · show arctan ((tan (z 0) + tan (z 1)) / 2 - (tan (z 0) - tan (z 1)) / 2) = z 1
    rw [show (tan (z 0) + tan (z 1)) / 2 - (tan (z 0) - tan (z 1)) / 2 = tan (z 1) by ring,
      arctan_tan hz.2.1.1 hz.2.1.2]
  · rfl
  · rfl

lemma penroseMap_mem {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) : penroseMap y ∈ penroseU := by
  refine ⟨arctan_mem_Ioo _, arctan_mem_Ioo _, ?_, hy.2.1, hy.2.2⟩
  show |arctan (y 0 + y 1) + arctan (y 0 - y 1)| < π / 2
  rw [← tan_mul_tan_lt_one_iff (arctan_mem_Ioo _) (arctan_mem_Ioo _), tan_arctan, tan_arctan]
  nlinarith [hy.1]

lemma penroseInv_mem {z : Fin 4 → ℝ} (hz : z ∈ penroseU) : penroseInv z ∈ kruskalU := by
  refine ⟨?_, hz.2.2.2.1, hz.2.2.2.2⟩
  show -1 < ((tan (z 0) - tan (z 1)) / 2) ^ 2 - ((tan (z 0) + tan (z 1)) / 2) ^ 2
  have h := (tan_mul_tan_lt_one_iff hz.1 hz.2.1).2 hz.2.2.1
  nlinarith [h]

/-- **The Kruskal domain is mapped bijectively onto the bounded Penrose diagram.** -/
theorem bijOn_penroseMap : BijOn penroseMap kruskalU penroseU :=
  ⟨fun _ hy => penroseMap_mem hy,
    fun y _ y' _ h => by rw [← penroseInv_penroseMap y, h, penroseInv_penroseMap],
    fun z hz => ⟨penroseInv z, penroseInv_mem hz, penroseMap_penroseInv hz⟩⟩

/-- **The horizon `T = ±X` is `p = 0` or `q = 0`** in the Penrose diagram. -/
theorem penroseMap_horizon_iff (y : Fin 4 → ℝ) :
    y 1 ^ 2 = y 0 ^ 2 ↔ penroseMap y 0 = 0 ∨ penroseMap y 1 = 0 := by
  show y 1 ^ 2 = y 0 ^ 2 ↔ arctan (y 0 + y 1) = 0 ∨ arctan (y 0 - y 1) = 0
  rw [arctan_eq_zero_iff, arctan_eq_zero_iff]
  constructor
  · intro h
    have h1 : (y 0 + y 1) * (y 0 - y 1) = 0 := by ring_nf; linarith
    exact mul_eq_zero.1 h1
  · rintro (h | h)
    · have : y 1 = -y 0 := by linarith
      rw [this]; ring
    · have : y 1 = y 0 := by linarith
      rw [this]

/-! ### The metric in the Penrose coordinates -/

lemma jac_penroseInv {z : Fin 4 → ℝ} (hz : z ∈ penroseU) :
    jac penroseInv z =
      !![1 / cos (z 0) ^ 2 / 2, 1 / cos (z 1) ^ 2 / 2, 0, 0;
         1 / cos (z 0) ^ 2 / 2, -(1 / cos (z 1) ^ 2) / 2, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] := by
  have h0 := hasDerivAt_tan_of_mem_Ioo hz.1
  have h1 := hasDerivAt_tan_of_mem_Ioo hz.2.1
  have P0 : ∀ k : Fin 4, pd k (fun w => tan (w 0)) z = if k = 0 then 1 / cos (z 0) ^ 2 else 0 := fun k =>
    pd_coord (n := 4) 0 k h0
  have P1 : ∀ k : Fin 4, pd k (fun w => tan (w 1)) z = if k = 1 then 1 / cos (z 1) ^ 2 else 0 := fun k =>
    pd_coord (n := 4) 1 k h1
  have P2 : ∀ k : Fin 4, pd k (fun w => w 2) z = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (z 2))
  have P3 : ∀ k : Fin 4, pd k (fun w => w 3) z = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (z 3))
  have d0 : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => tan (w 0)) z :=
    DifferentiableAt.comp (g := tan) (f := fun w : Fin 4 → ℝ => w 0) z h0.differentiableAt
      (by fun_prop : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => w 0) z)
  have d1 : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => tan (w 1)) z :=
    DifferentiableAt.comp (g := tan) (f := fun w : Fin 4 → ℝ => w 1) z h1.differentiableAt
      (by fun_prop : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => w 1) z)
  have hT : ∀ k, pd k (fun w => (tan (w 0) + tan (w 1)) / 2) z =
      (pd k (fun w => tan (w 0)) z + pd k (fun w => tan (w 1)) z) / 2 := by
    intro k
    have dS : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => tan (w 0) + tan (w 1)) z := d0.add d1
    have := pd_const_mul (2⁻¹ : ℝ) dS k
    rw [show (fun w : Fin 4 → ℝ => (tan (w 0) + tan (w 1)) / 2) =
      fun w => 2⁻¹ * (tan (w 0) + tan (w 1)) from by ext w; ring, this, pd_add d0 d1]
    ring
  have hX : ∀ k, pd k (fun w => (tan (w 0) - tan (w 1)) / 2) z =
      (pd k (fun w => tan (w 0)) z - pd k (fun w => tan (w 1)) z) / 2 := by
    intro k
    have dD : DifferentiableAt ℝ (fun w : Fin 4 → ℝ => tan (w 0) - tan (w 1)) z := d0.sub d1
    have := pd_const_mul (2⁻¹ : ℝ) dD k
    rw [show (fun w : Fin 4 → ℝ => (tan (w 0) - tan (w 1)) / 2) =
      fun w => 2⁻¹ * (tan (w 0) - tan (w 1)) from by ext w; ring, this, pd_sub d0 d1]
    ring
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp only [jac, penroseInv] <;>
    simp [hT, hX, P0, P1, P2, P3]

variable (M : ℝ)

/-- **The Kruskal metric in the Penrose coordinates** `(p, q, θ, φ)`:
`-(h(r) / (2 cos² p cos² q)) (dp dq + dq dp) + r² dΩ²`. Its `(p, q)` part is the flat metric
`-(dp dq + dq dp)/2` in null coordinates times the positive factor `h(r) / (cos² p cos² q)`. -/
theorem pullback_kruskal_penroseInv {z : Fin 4 → ℝ} (hz : z ∈ penroseU) :
    pullback (kruskalMetric M) penroseInv z =
      !![0, -(kh M (kr M (penroseInv z)) / (2 * cos (z 0) ^ 2 * cos (z 1) ^ 2)), 0, 0;
         -(kh M (kr M (penroseInv z)) / (2 * cos (z 0) ^ 2 * cos (z 1) ^ 2)), 0, 0, 0;
         0, 0, kr M (penroseInv z) ^ 2, 0;
         0, 0, 0, kr M (penroseInv z) ^ 2 * sin (z 2) ^ 2] := by
  have hcp := (cos_pos_of_mem_Ioo hz.1).ne'
  have hcq := (cos_pos_of_mem_Ioo hz.2.1).ne'
  rw [pullback_eq_mul, jac_penroseInv hz]
  have hθ : penroseInv z 2 = z 2 := rfl
  simp only [kruskalMetric, hθ]
  generalize kh M (kr M (penroseInv z)) = h
  generalize kr M (penroseInv z) = r
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> (field_simp; ring)

/-- The conformal factor `h(r) / (cos² p cos² q)` of the `(p, q)` part is positive. -/
theorem penrose_conformalFactor_pos (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ penroseU) :
    0 < kh M (kr M (penroseInv z)) / (cos (z 0) ^ 2 * cos (z 1) ^ 2) := by
  have hcp := cos_pos_of_mem_Ioo hz.1
  have hcq := cos_pos_of_mem_Ioo hz.2.1
  have := kh_pos M hM (kr_pos M hM (penroseInv_mem hz))
  positivity

end Lightlike
