import Lightlike.Spacetime.EnergyConditions
import Lightlike.Spacetime.Causal.ConeConvex
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# A null vector orthogonal to a null vector is parallel to it (G1-012, step D4)

In a Lorentzian form, if `k` is a non-zero null vector and `z` is null and orthogonal to `k`, then `z` is a
multiple of `k`.
-/

open Set Submodule

namespace Lightlike.Penrose

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- **A null vector orthogonal to a null vector `k` is a multiple of `k`.** -/
theorem eq_smul_of_null_orth {m : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsLorentzianForm (m + 1) B) {k z : V}
    (hk : B k k = 0) (hkne : k ≠ 0) (hz : B z k = 0) (hzz : B z z = 0) : ∃ c : ℝ, z = c • k := by
  -- `z` is orthogonal to every vector orthogonal to `k`
  have hperp : ∀ y, B y k = 0 → B z y = 0 := by
    intro y hy
    have hnn : ∀ t : ℝ, 0 ≤ 2 * t * B z y + t ^ 2 * B y y := by
      intro t
      have h1 := null_orth_nonneg hB (k := k) (z := z + t • y) hk hkne (by simp [hz, hy])
      have : B (z + t • y) (z + t • y) = 2 * t * B z y + t ^ 2 * B y y := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          hzz, hB.symm y z]
        ring
      rwa [this] at h1
    by_contra hne
    have hpos : B z y ≠ 0 := hne
    -- choose `t = - B z y / (|B y y| + 1)`: the expression is negative
    set a := B z y with ha
    set b := B y y with hb
    have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b := hnn
    have h1 := key (-a / (|b| + 1))
    have hbpos : 0 < |b| + 1 := by positivity
    have : 2 * (-a / (|b| + 1)) * a + (-a / (|b| + 1)) ^ 2 * b < 0 := by
      have ha2 : 0 < a ^ 2 := by positivity
      have hb' : b ≤ |b| := le_abs_self b
      have hfrac : 0 < a ^ 2 / (|b| + 1) := by positivity
      calc 2 * (-a / (|b| + 1)) * a + (-a / (|b| + 1)) ^ 2 * b
          = -(2 * a ^ 2 / (|b| + 1)) + a ^ 2 * b / (|b| + 1) ^ 2 := by field_simp
        _ < 0 := by
          have : a ^ 2 * b / (|b| + 1) ^ 2 ≤ a ^ 2 * |b| / (|b| + 1) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hb' (sq_nonneg a)
          have h2 : a ^ 2 * |b| / (|b| + 1) ^ 2 < 2 * a ^ 2 / (|b| + 1) := by
            rw [div_lt_div_iff₀ (by positivity) hbpos]
            nlinarith [abs_nonneg b, sq_nonneg a, mul_pos ha2 hbpos]
          linarith
    linarith
  -- hence `z ∈ (k^⊥)^⊥ = span k`
  have hnd := hB.bilinForm_nondegenerate
  have hrefl : (B.toBilinForm).IsRefl := (hB.isSymm).isRefl
  have hmem : z ∈ (B.toBilinForm).orthogonal ((B.toBilinForm).orthogonal (span ℝ {k})) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
    have h1 : (B.toBilinForm) k y = 0 := hy k (mem_span_singleton_self k)
    have h2 : B y k = 0 := by
      have : B k y = 0 := by simpa using h1
      rw [hB.symm]; exact this
    have := hperp y h2
    show B y z = 0
    rw [hB.symm]; exact this
  rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl] at hmem
  exact mem_span_singleton.1 hmem |>.imp fun c hc => hc.symm

/-- **A null vector orthogonal to a timelike vector is zero.** -/
theorem eq_zero_of_null_orth_timelike {m : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsLorentzianForm (m + 1) B)
    {X w : V} (hX : B X X < 0) (hwX : B w X = 0) (hww : B w w = 0) : w = 0 := by
  obtain ⟨e, he⟩ := hB
  have hX' := lorentz_apply e he X X
  have hw' := lorentz_apply e he w X
  have hww' := lorentz_apply e he w w
  set x0 := e.repr X 0
  set w0 := e.repr w 0
  set sx := ∑ i : Fin m, e.repr X i.succ * e.repr X i.succ
  set sw := ∑ i : Fin m, e.repr w i.succ * e.repr w i.succ
  set p := ∑ i : Fin m, e.repr w i.succ * e.repr X i.succ
  have hcs : p ^ 2 ≤ sw * sx := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin m => e.repr w i.succ)
      (fun i => e.repr X i.succ)
    simpa [sq, p, sw, sx] using this
  rw [hwX] at hw'
  rw [hww] at hww'
  rw [hX'] at hX
  have hsw : sw = w0 * w0 := by linarith
  have hp : p = w0 * x0 := by linarith
  have hsx : sx < x0 * x0 := by linarith
  have hw0 : w0 = 0 := by
    by_contra hne
    have hpos : 0 < w0 * w0 := mul_self_pos.2 hne
    have : (w0 * x0) ^ 2 ≤ w0 * w0 * sx := by rw [← hp, ← hsw]; exact hcs
    nlinarith
  have hsw0 : sw = 0 := by rw [hsw, hw0]; ring
  have hall : ∀ i : Fin m, e.repr w i.succ = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (e.repr w j.succ))).1 hsw0 i
      (Finset.mem_univ i)
    exact mul_self_eq_zero.1 this
  have : e.repr w = 0 := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hw0
    · simpa using hall i
  exact e.repr.injective (by simpa using this)

/-- **A future null vector pairs negatively with every future timelike vector of the same cone.** -/
theorem neg_of_future_null {m : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsLorentzianForm (m + 1) B) {X X' w : V}
    (hX : B X X < 0) (hX' : B X' X' < 0) (hX'X : B X' X < 0) (hww : B w w = 0) (hwX : B w X < 0)
    (hw0 : w ≠ 0) : B w X' < 0 := by
  have hs : ∀ u v : V, B u v = B v u := fun u v => hB.symm u v
  have hle : B w X' ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set c := B X X' with hc
    have hcneg : c < 0 := by rw [hc, hs]; exact hX'X
    set ε : ℝ := B w X' / (2 * (|c| + 1)) with hε
    have hεpos : 0 < ε := by positivity
    have h1 : B (w + ε • X) (w + ε • X) < 0 := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hww, hs X w]
      nlinarith [mul_pos hεpos (neg_pos.2 hwX), mul_pos hεpos hεpos]
    have h2 : B (w + ε • X) X < 0 := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith [mul_pos hεpos (neg_pos.2 hX)]
    have h3 := hB.neg_of_futureTimelike hX h1 hX' h2 hX'X  -- B (w + ε X) X' < 0
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h3
    rw [← hc] at h3
    have habs : |c| = -c := abs_of_neg hcneg
    have : B w X' < ε * (-c) := by linarith
    have hq : ε * (-c) < B w X' := by
      rw [hε]
      have : 0 < |c| + 1 := by positivity
      rw [← habs]
      calc B w X' / (2 * (|c| + 1)) * |c| = B w X' * (|c| / (2 * (|c| + 1))) := by ring
        _ < B w X' * 1 := by
          apply mul_lt_mul_of_pos_left _ hpos
          rw [div_lt_one (by positivity)]
          linarith [abs_nonneg c]
        _ = B w X' := by ring
    linarith
  refine lt_of_le_of_ne hle fun h0 => hw0 ?_
  exact eq_zero_of_null_orth_timelike hB hX' h0 hww

end Lightlike.Penrose
