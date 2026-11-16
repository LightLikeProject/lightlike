import Lightlike.Regge.Linear3.LinearizedLattice
import Lightlike.Regge.Linear3.SaintVenantClass

/-!
# The second-order expansion of the unit-scale degrees of freedom and of the class sums

For a field `hf` of symmetric matrices with `C³` entries, the six unit-scale degrees of freedom `atilV` of an
incidence `(σ, h)` at a point `v` of a compact set and scale `ε` are, up to `|M| ε³`, the polynomial
`incVec (qf H) + ε incVec (d1q ∂h) + ε² lenR (∂²h)` (`atilV_expansion`, from the averaged Taylor expansion
`quad_taylor`), with `H = h(v)`, `∂h`, `∂²h` the derivatives at `v`. The class sums of the angle derivative `dth` of the
zeroth- and first-order terms vanish (`class_A0`, `class_A1`), so
`Σ_{(σ,h) in class k} dth h (atilV) = ε² Σ_{class k} dth h (lenR ∂²h) + O(ε³)`, uniformly in `v` (`class_expansion`).

## Main results

* `atil_expansion`, `atilV_expansion`: the expansion of the degrees of freedom of an incidence.
* `dth_add`, `dth_smul`, `dth_bound`: `dth` is linear and bounded; `clsSum_add`, `clsSum_smul`, `clsSum_abs_le`.
* `class_expansion`: the class sum of `dth (atilV)` is `ε²` times that of `dth (lenR ∂²h)` up to `ε³`.

**Limits.** `C³` entries, symmetric `hf`; uniform on compact sets of base points.
-/

open Real Finset Filter Topology Matrix
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

theorem kpos_abs_le (σ h : Fin 6) (a : Fin 4) (i : Fin 3) : |kpos σ h a i| ≤ 1 := by
  rw [abs_le]
  fin_cases σ <;> fin_cases h <;> fin_cases a <;> fin_cases i <;>
    simp [kpos, kv, perms, hP, hQ] <;> norm_num

theorem kposv_norm_le (σ h : Fin 6) (a : Fin 4) : ‖kposv σ h a‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs]; exact kpos_abs_le σ h a i

theorem kv_diff_abs_le (a b : Fin 4) (j : Fin 3) : |kv b j - kv a j| ≤ 1 := by
  rw [abs_le]
  fin_cases a <;> fin_cases b <;> fin_cases j <;> simp [kv] <;> norm_num

theorem kposv_diff_norm_le (σ h : Fin 6) (a b : Fin 4) : ‖kposv σ h b - kposv σ h a‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have : kposv σ h b i - kposv σ h a i = kv b (perms σ i) - kv a (perms σ i) := by
    simp only [kposv, kpos]; ring
  rw [this]
  exact kv_diff_abs_le a b _


/-- The value of a matrix field at a point as a function of two indices. -/
def Hm (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => hf v i j

/-- The first partial derivatives `dh k i j = ∂_k h_ij (v)`. -/
noncomputable def dh1 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    Fin 3 → Fin 3 → Fin 3 → ℝ := fun k i j => pd1 (fun y => hf y i j) v k

/-- The second partial derivatives `dd k l i j = ∂_k ∂_l h_ij (v)`. -/
noncomputable def dd2 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun k l i j => pd2 (fun y => hf y i j) v k l

theorem poly_match (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (ε : ℝ) (s0 D : Fin 3 → ℝ) :
    ∑ i, ∑ j, D i * D j * (H i j + ε * ∑ k, (s0 k + D k / 2) * dh k i j +
        ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) * dd k l i j) =
      qf H D + ε * d1q dh (fun i => s0 i + D i / 2) D +
        ε ^ 2 * rf dd (fun i => s0 i + D i / 2) D := by
  simp only [qf, d1q, rf, ddq, Fin.sum_univ_three]
  ring


/-- **The second-order expansion of the unit-scale degrees of freedom of an incidence.** -/
theorem atil_expansion {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ (σ h : Fin 6) (a b : Fin 4),
      |atil hf ε v σ h a b - (qf (Hm hf v) (kposv σ h b - kposv σ h a) +
        ε * d1q (dh1 hf v) (fun i => (kpos σ h a i + kpos σ h b i) / 2) (kposv σ h b - kposv σ h a) +
        ε ^ 2 * rf (dd2 hf v) (fun i => (kpos σ h a i + kpos σ h b i) / 2)
          (kposv σ h b - kposv σ h a))| ≤ M * ε ^ 3 := by
  obtain ⟨M, r, hr, hb⟩ := quad_taylor hsm hK
  refine ⟨M, r, hr, fun v hv ε hε hεr σ h a b => ?_⟩
  have h1 := hb v hv ε hε hεr (kposv σ h a) (kposv σ h b - kposv σ h a) (kposv_norm_le σ h a)
    (kposv_diff_norm_le σ h a b)
  have h2 := poly_match (Hm hf v) (dh1 hf v) (dd2 hf v) ε (kposv σ h a) (kposv σ h b - kposv σ h a)
  have e : (fun i => kposv σ h a i + (kposv σ h b - kposv σ h a) i / 2) =
      fun i => (kpos σ h a i + kpos σ h b i) / 2 := by
    funext i; simp [kposv]; ring
  rw [e] at h2
  simp only [Hm, dh1, dd2] at h2 ⊢
  unfold atil
  rw [← h2]
  exact h1


theorem dth_add (h : Fin 6) (x y : Fin 6 → ℝ) : dth h (x + y) = dth h x + dth h y := by
  fin_cases h <;> simp [dth] <;> ring

theorem dth_smul (h : Fin 6) (c : ℝ) (x : Fin 6 → ℝ) : dth h (c • x) = c * dth h x := by
  fin_cases h <;> simp [dth] <;> ring

theorem dth_bound (h : Fin 6) (x : Fin 6 → ℝ) : |dth h x| ≤ 4 * ‖x‖ := by
  have hx : ∀ i, -‖x‖ ≤ x i ∧ x i ≤ ‖x‖ := fun i => abs_le.1 (by simpa using norm_le_pi_norm x i)
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3; have h4 := hx 4; have h5 := hx 5
  rw [abs_le]
  fin_cases h <;> simp [dth] <;>
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]


/-- The vector expansion of the six unit-scale degrees of freedom of an incidence. -/
theorem atilV_expansion {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ σ h : Fin 6,
      ‖atilV hf ε v σ h - (incVec (fun _ Δ => qf (Hm hf v) Δ) σ h + ε • incVec (fun s Δ => d1q (dh1 hf v) s Δ) σ h +
        ε ^ 2 • lenR (dd2 hf v) σ h)‖ ≤ |M| * ε ^ 3 := by
  obtain ⟨M, r, hr, hb⟩ := atil_expansion hsm hK
  refine ⟨M, r, hr, fun v hv ε hε hεr σ h => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hM : M * ε ^ 3 ≤ |M| * ε ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
  fin_cases i <;>
  · refine le_trans ?_ hM
    simp only [atilV, incVec, lenR, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    exact hb v hv ε hε hεr σ h _ _


theorem clsSum_add (w : Fin 3 → ℝ) (f g : Fin 6 → Fin 6 → ℝ) :
    clsSum w (fun σ h => f σ h + g σ h) = clsSum w f + clsSum w g := by
  unfold clsSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> simp

theorem clsSum_smul (w : Fin 3 → ℝ) (c : ℝ) (f : Fin 6 → Fin 6 → ℝ) :
    clsSum w (fun σ h => c * f σ h) = c * clsSum w f := by
  unfold clsSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> simp

open Classical in
theorem clsSum_abs_le (w : Fin 3 → ℝ) (f : Fin 6 → Fin 6 → ℝ) (B : ℝ) (hB : ∀ σ h, |f σ h| ≤ B) (hB0 : 0 ≤ B) :
    |clsSum w f| ≤ 36 * B := by
  unfold clsSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ : Fin 6, |∑ h : Fin 6, if InClass w σ h then f σ h else 0|
      ≤ ∑ σ : Fin 6, 6 * B := by
        refine Finset.sum_le_sum fun σ _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ h : Fin 6, |if InClass w σ h then f σ h else 0| ≤ ∑ h : Fin 6, B :=
              Finset.sum_le_sum fun h _ => by split_ifs <;> simp [hB σ h, hB0]
          _ = 6 * B := by simp
    _ = 36 * B := by simp; ring


/-- **The class sum of the angle derivative in the interpolated variation is `ε²` times the second-order
class sum, up to `ε³`.** -/
theorem class_expansion {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ k : Fin 7,
      |clsSum (dirs k) (fun σ h => dth h (atilV hf ε v σ h)) -
        ε ^ 2 * clsSum (dirs k) (fun σ h => dth h (lenR (dd2 hf v) σ h))| ≤ M * ε ^ 3 := by
  obtain ⟨M0, r, hr, hb⟩ := atilV_expansion hsm hK
  refine ⟨144 * |M0|, r, hr, fun v hv ε hε hεr k => ?_⟩
  have hHs : ∀ i j, Hm hf v i j = Hm hf v j i := fun i j => hsymm v i j
  have hds : ∀ k i j, dh1 hf v k i j = dh1 hf v k j i := fun k i j => by
    unfold dh1 pd1
    congr 2
    funext y
    exact hsymm y i j
  have c0 := class_A0 (Hm hf v) hHs k
  have c1 := class_A1 (dh1 hf v) (hds) k
  set A0 : Fin 6 → Fin 6 → Fin 6 → ℝ := fun σ h => incVec (fun _ Δ => qf (Hm hf v) Δ) σ h
  set A1 : Fin 6 → Fin 6 → Fin 6 → ℝ := fun σ h => incVec (fun s Δ => d1q (dh1 hf v) s Δ) σ h
  set A2 : Fin 6 → Fin 6 → Fin 6 → ℝ := fun σ h => lenR (dd2 hf v) σ h
  have hdec : ∀ σ h, dth h (atilV hf ε v σ h) = dth h (A0 σ h) + ε * dth h (A1 σ h) + ε ^ 2 * dth h (A2 σ h) +
      dth h (atilV hf ε v σ h - (A0 σ h + ε • A1 σ h + ε ^ 2 • A2 σ h)) := fun σ h => by
    rw [← dth_smul, ← dth_smul, ← dth_add, ← dth_add, ← dth_add]
    congr 1; abel
  have hfun : (fun σ h => dth h (atilV hf ε v σ h)) = fun σ h => ((dth h (A0 σ h) + ε * dth h (A1 σ h)) +
      ε ^ 2 * dth h (A2 σ h)) + dth h (atilV hf ε v σ h - (A0 σ h + ε • A1 σ h + ε ^ 2 • A2 σ h)) := by
    funext σ h; rw [hdec]
  rw [hfun, clsSum_add, clsSum_add, clsSum_add, clsSum_smul, clsSum_smul]
  have hR : |clsSum (dirs k) (fun σ h => dth h (atilV hf ε v σ h - (A0 σ h + ε • A1 σ h + ε ^ 2 • A2 σ h)))| ≤
      36 * (4 * (|M0| * ε ^ 3)) := by
    refine clsSum_abs_le _ _ _ (fun σ h => ?_) (by positivity)
    exact (dth_bound h _).trans (mul_le_mul_of_nonneg_left (hb v hv ε hε hεr σ h) (by norm_num))
  have e0 : clsSum (dirs k) (fun σ h => dth h (A0 σ h)) = 0 := c0
  have e1 : clsSum (dirs k) (fun σ h => dth h (A1 σ h)) = 0 := c1
  rw [e0, e1]
  calc |0 + ε * 0 + ε ^ 2 * clsSum (dirs k) (fun σ h => dth h (A2 σ h)) +
        clsSum (dirs k) (fun σ h => dth h (atilV hf ε v σ h - (A0 σ h + ε • A1 σ h + ε ^ 2 • A2 σ h))) -
        ε ^ 2 * clsSum (dirs k) (fun σ h => dth h (lenR (dd2 hf v) σ h))|
      = |clsSum (dirs k) (fun σ h => dth h (atilV hf ε v σ h - (A0 σ h + ε • A1 σ h + ε ^ 2 • A2 σ h)))| := by
        congr 1; simp only [A2]; ring
    _ ≤ 36 * (4 * (|M0| * ε ^ 3)) := hR
    _ = 144 * |M0| * ε ^ 3 := by ring

end Lightlike.Regge.Linear3
