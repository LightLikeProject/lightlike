import Mathlib
import Lightlike.Spacetime.GreenOperators.PrimitiveGen
import Lightlike.Spacetime.GreenOperators.RiemannSol
import Lightlike.Spacetime.GreenOperators.Existence
import Lightlike.Spacetime.GreenOperators.Uniqueness

/-!
# Existence of the retarded solution of the Klein–Gordon equation on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `f` of class `C²` with compact support and `m : ℝ`, put `c = -m²/4`, `h = -¼ f ∘ nullPt`
(the source in null coordinates `a = t - x`, `b = t + x`, in which `-∂ₜ² + ∂ₓ² = -4 ∂ₐ ∂_b`) and
`u = riemannSol c h = K ⋆ h`, with `K` the Riemann kernel.  Then `u = quadPrim (h + c u)`, so
`u_{ab} = h + c u` (`fderiv_fderiv_riemannSol`), i.e. `massiveSol m f = u ∘ toNull` solves
`kgOp m u = f` (`kgOp_massiveSol`).  If `f` vanishes for `t < T`, so does the solution.
Together with `retarded_unique` this gives existence and uniqueness of the retarded solution for
every mass (`retarded_existsUnique`).
-/

open Set MeasureTheory
open scoped Convolution

namespace Lightlike.GreenOperators

/-- The retarded solution of `kgOp m u = f` on `1+1` Minkowski space. -/
noncomputable def massiveSol (m : ℝ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  riemannSol (-m ^ 2 / 4) ((-(1 / 4 : ℝ)) • nullSource f) ∘ toNull

/-- `u_{ab} = h + c u` for `u = K ⋆ h`. -/
lemma fderiv_fderiv_riemannSol (c : ℝ) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hcg : HasCompactSupport h) (q : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (riemannSol c h)) q ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
      = h q + c * riemannSol c h q := by
  have hc : Continuous h := hh.continuous
  obtain ⟨R, hz⟩ := exists_vanishing hcg
  have hu : ContDiff ℝ 2 (riemannSol c h) := by
    have := riemannSol_contDiff c (n := 2) hcg (by exact_mod_cast hh)
    exact_mod_cast this
  have hwc : Continuous (h + c • riemannSol c h) :=
    hc.add (hu.continuous.const_smul c)
  have hwz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → (h + c • riemannSol c h) q = 0 := by
    intro q hq
    simp [hz q hq, riemannSol_eq_zero c hz q hq]
  have heq := riemannSol_eq_quadPrim c hc hcg
  have hu' : ContDiff ℝ 2 (quadPrim (h + c • riemannSol c h)) := by rw [← heq]; exact hu
  have key := fderiv_fderiv_quadPrim' hwc hwz hu' q
  rw [← heq] at key
  simpa using key

/-- `K ⋆ h` vanishes at `p` if `h` vanishes on `{q | q.1 + q.2 < S}` and `p.1 + p.2 < S`. -/
lemma riemannSol_eq_zero_of_time (c : ℝ) {h : ℝ × ℝ → ℝ} {S : ℝ}
    (hz : ∀ q : ℝ × ℝ, q.1 + q.2 < S → h q = 0) (p : ℝ × ℝ) (hp : p.1 + p.2 < S) :
    riemannSol c h p = 0 := by
  unfold riemannSol
  rw [convolution_def]
  have : (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (riemannKernel c t) (h (p - t)))
      = fun _ => 0 := by
    funext t
    by_cases ht : (0 : ℝ × ℝ) ≤ t
    · have ht1 : (0 : ℝ) ≤ t.1 := ht.1
      have ht2 : (0 : ℝ) ≤ t.2 := ht.2
      rw [hz (p - t) (by simp only [Prod.fst_sub, Prod.snd_sub]; linarith)]
      simp
    · simp [riemannKernel, ht]
  rw [this, integral_zero]

lemma massiveSol_contDiff (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (massiveSol m f) := by
  have hg : ContDiff ℝ 2 ((-(1 / 4 : ℝ)) • nullSource f) :=
    (nullSource_contDiff hf).const_smul (-(1 / 4 : ℝ))
  have hcg : HasCompactSupport ((-(1 / 4 : ℝ)) • nullSource f) :=
    (nullSource_hasCompactSupport hc).smul_left
  have hU : ContDiff ℝ 2 (riemannSol (-m ^ 2 / 4) ((-(1 / 4 : ℝ)) • nullSource f)) := by
    have := riemannSol_contDiff (-m ^ 2 / 4) (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  exact hU.comp toNull.contDiff

/-- The retarded solution solves the Klein–Gordon equation `-u_tt + u_xx - m² u = f`. -/
theorem kgOp_massiveSol (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (p : ℝ × ℝ) : kgOp m (massiveSol m f) p = f p := by
  set g := (-(1 / 4 : ℝ)) • nullSource f with hgdef
  have hg : ContDiff ℝ 2 g := (nullSource_contDiff hf).const_smul (-(1 / 4 : ℝ))
  have hcg : HasCompactSupport g := (nullSource_hasCompactSupport hc).smul_left
  set U := riemannSol (-m ^ 2 / 4) g with hUdef
  have hU : ContDiff ℝ 2 U := by
    have := riemannSol_contDiff (-m ^ 2 / 4) (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  set q := toNull p with hq
  have hB : fderiv ℝ (fderiv ℝ U) q ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
      = g q + (-m ^ 2 / 4) * U q :=
    fderiv_fderiv_riemannSol (-m ^ 2 / 4) hg hcg q
  have hsym := (hU.contDiffAt (x := q)).isSymmSndFDerivAt (n := 2)
    (by simp) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
  have e1 : toNull ((1 : ℝ), (0 : ℝ)) = (1, 0) + (0, 1) := by ext <;> simp [toNull_apply]
  have e2 : toNull ((0 : ℝ), (1 : ℝ)) = -(1, 0) + (0, 1) := by ext <;> simp [toNull_apply]
  have hUq : U q = massiveSol m f p := rfl
  unfold kgOp
  rw [show massiveSol m f = U ∘ toNull from rfl, fderiv_fderiv_comp_clm toNull hU,
    fderiv_fderiv_comp_clm toNull hU, e1, e2]
  simp only [Function.comp, map_add, map_neg, add_apply, neg_apply]
  have hgq : g q = -(1 / 4 : ℝ) * f p := by
    simp only [hgdef, Pi.smul_apply, smul_eq_mul, nullSource, hq, toNull_apply, nullPt]
    congr 2
    ext <;> simp
  rw [hgq] at hB
  linarith

lemma massiveSol_eq_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0)
    (p : ℝ × ℝ) (hp : p.1 < T) : massiveSol m f p = 0 := by
  refine riemannSol_eq_zero_of_time (S := 2 * T) _ (fun q hq => ?_) (toNull p) ?_
  · simp only [Pi.smul_apply, smul_eq_mul, nullSource]
    rw [h0, mul_zero]
    simp only [nullPt]
    linarith
  · simp only [toNull_apply]
    linarith

/-- **Existence and uniqueness of the retarded solution** of the Klein–Gordon equation
`-u_tt + u_xx - m² u = f` on `1+1` Minkowski space (any `m`), for `f` of class `C²` with compact
support that vanishes for `t < T`: there is exactly one `C²` solution that vanishes for `t < T`. -/
theorem retarded_existsUnique (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0) :
    ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp m u p = f p) ∧ ∀ p : ℝ × ℝ, p.1 < T → u p = 0 :=
  ⟨massiveSol m f, ⟨massiveSol_contDiff m hf hc, kgOp_massiveSol m hf hc, massiveSol_eq_zero h0⟩,
    fun v ⟨hv, hkv, hv0⟩ =>
      retarded_unique m T hv (massiveSol_contDiff m hf hc)
        (fun p => by rw [hkv p, kgOp_massiveSol m hf hc]) hv0 (massiveSol_eq_zero h0)⟩

end Lightlike.GreenOperators
