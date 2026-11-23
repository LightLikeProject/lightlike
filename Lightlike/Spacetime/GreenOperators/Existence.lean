import Mathlib
import Lightlike.Spacetime.GreenOperators.Primitive
import Lightlike.Spacetime.GreenOperators.Uniqueness

/-!
# Existence of the retarded solution of the massless wave equation on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `f : ℝ × ℝ → ℝ` of class `C²` with compact support, the function
`retardedSol f (t, x) = -¼ ∫_{a' ≤ t - x, b' ≤ t + x} f (nullPt a' b') da' db'`
(which equals `-½ ∫_{J⁻(t,x)} f dt dx`) is a `C²` solution of `kgOp 0 u = f` (`kgOp_retardedSol`)
that vanishes for `t < T` whenever `f` does (`retardedSol_eq_zero`).

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- Second derivative of a composition with a continuous linear map on the right. -/
lemma fderiv_fderiv_comp_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] ℝ × ℝ) {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ 2 U) (p v w : G) :
    fderiv ℝ (fderiv ℝ (U ∘ L)) p v w = fderiv ℝ (fderiv ℝ U) (L p) (L v) (L w) := by
  have h := L.iteratedFDeriv_comp_right hU p (i := 2) (by norm_num)
  have h2 := congrArg (fun T => T ![v, w]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply] at h2
  simpa using h2

/-- The linear map `(t, x) ↦ (t - x, t + x)` to null coordinates. -/
noncomputable def toNull : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma toNull_apply (p : ℝ × ℝ) : toNull p = (p.1 - p.2, p.1 + p.2) := rfl

/-- `nullPt` as a function on `ℝ × ℝ`, as a homeomorphism (inverse `toNull`). -/
noncomputable def nullHomeo : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun q := nullPt q.1 q.2
  invFun p := toNull p
  left_inv q := by
    ext <;> simp [toNull_apply, nullPt] <;> ring
  right_inv p := by
    ext <;> simp [toNull_apply, nullPt]
  continuous_toFun := by simp only [nullPt]; fun_prop
  continuous_invFun := toNull.continuous

/-- The source in null coordinates. -/
noncomputable def nullSource (f : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := f (nullPt q.1 q.2)

lemma nullSource_hasCompactSupport {f : ℝ × ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (nullSource f) :=
  hf.comp_homeomorph nullHomeo

lemma nullSource_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (nullSource f) := by
  have : ContDiff ℝ 2 (fun q : ℝ × ℝ => nullPt q.1 q.2) := by
    simp only [nullPt]
    exact (((contDiff_fst.add contDiff_snd).div_const 2).prodMk
      ((contDiff_snd.sub contDiff_fst).div_const 2))
  exact hf.comp this

/-- The retarded solution of the massless wave equation `kgOp 0 u = f` on `1+1` Minkowski space. -/
noncomputable def retardedSol (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  quadPrim ((-(1 / 4 : ℝ)) • nullSource f) (toNull p)

lemma retardedSol_eq (f : ℝ × ℝ → ℝ) :
    retardedSol f = quadPrim ((-(1 / 4 : ℝ)) • nullSource f) ∘ toNull := rfl

lemma retardedSol_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (retardedSol f) := by
  have hg : ContDiff ℝ 2 ((-(1 / 4 : ℝ)) • nullSource f) :=
    (nullSource_contDiff hf).const_smul (-(1 / 4 : ℝ))
  have hcg : HasCompactSupport ((-(1 / 4 : ℝ)) • nullSource f) :=
    (nullSource_hasCompactSupport hc).smul_left
  have hU : ContDiff ℝ 2 (quadPrim ((-(1 / 4 : ℝ)) • nullSource f)) := by
    have := quadPrim_contDiff (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  rw [retardedSol_eq]
  exact hU.comp toNull.contDiff

/-- The retarded solution solves the massless wave equation `-u_tt + u_xx = f`. -/
theorem kgOp_retardedSol {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (p : ℝ × ℝ) : kgOp 0 (retardedSol f) p = f p := by
  set g := (-(1 / 4 : ℝ)) • nullSource f with hgdef
  have hg : ContDiff ℝ 2 g := (nullSource_contDiff hf).const_smul (-(1 / 4 : ℝ))
  have hcg : HasCompactSupport g := (nullSource_hasCompactSupport hc).smul_left
  obtain ⟨R, hR⟩ := exists_box hcg
  have hU : ContDiff ℝ 2 (quadPrim g) := by
    have := quadPrim_contDiff (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  set q := toNull p with hq
  have hB : fderiv ℝ (fderiv ℝ (quadPrim g)) q ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) = g q :=
    fderiv_fderiv_quadPrim hcg hg hR q
  have hsym := (hU.contDiffAt (x := q)).isSymmSndFDerivAt (n := 2)
    (by simp) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
  have e1 : toNull ((1 : ℝ), (0 : ℝ)) = (1, 0) + (0, 1) := by ext <;> simp [toNull_apply]
  have e2 : toNull ((0 : ℝ), (1 : ℝ)) = -(1, 0) + (0, 1) := by ext <;> simp [toNull_apply]
  unfold kgOp
  rw [retardedSol_eq, fderiv_fderiv_comp_clm toNull hU, fderiv_fderiv_comp_clm toNull hU, e1, e2]
  simp only [Function.comp, map_add, map_neg, add_apply, neg_apply]
  have hgq : g q = -(1 / 4 : ℝ) * f p := by
    simp only [hgdef, Pi.smul_apply, smul_eq_mul, nullSource, hq, toNull_apply, nullPt]
    congr 2
    ext <;> simp
  rw [hgq] at hB
  rw [← hq, zero_pow (by norm_num), zero_mul, sub_zero]
  linarith

lemma retardedSol_eq_zero {f : ℝ × ℝ → ℝ} {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0)
    (p : ℝ × ℝ) (hp : p.1 < T) : retardedSol f p = 0 := by
  apply quadPrim_eq_zero
  intro q hq
  simp only [Pi.smul_apply, smul_eq_mul, nullSource]
  rw [h0, mul_zero]
  have h1 : q.1 ≤ p.1 - p.2 := hq.1
  have h2 : q.2 ≤ p.1 + p.2 := hq.2
  simp only [nullPt]
  linarith

/-- **Existence and uniqueness of the retarded solution** of the massless wave equation
`-u_tt + u_xx = f` on `1+1` Minkowski space, for `f` of class `C²` with compact support that
vanishes for `t < T`: there is exactly one `C²` solution that vanishes for `t < T`. -/
theorem massless_retarded_existsUnique {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0) :
    ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp 0 u p = f p) ∧ ∀ p : ℝ × ℝ, p.1 < T → u p = 0 :=
  ⟨retardedSol f, ⟨retardedSol_contDiff hf hc, kgOp_retardedSol hf hc, retardedSol_eq_zero h0⟩,
    fun v ⟨hv, hkv, hv0⟩ =>
      retarded_unique 0 T hv (retardedSol_contDiff hf hc) (fun p => by rw [hkv p, kgOp_retardedSol hf hc])
        hv0 (retardedSol_eq_zero h0)⟩

end Lightlike.GreenOperators
