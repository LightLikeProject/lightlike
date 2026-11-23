import Mathlib
import Lightlike.Spacetime.GreenOperators.Existence
import Lightlike.Spacetime.GreenOperators.TimeReversal

/-!
# Existence of the advanced solution of the massless wave equation on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
The advanced solution is obtained from the retarded one by time reversal:
`advancedSol f = retardedSol (f ∘ timeRev) ∘ timeRev` (`kgOp_advancedSol`,
`advancedSol_eq_zero`), and `massless_advanced_existsUnique` gives existence and uniqueness.

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- Time reversal `(t, x) ↦ (-t, x)` as a homeomorphism. -/
noncomputable def timeRevHomeo : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ)

@[simp] lemma timeRevHomeo_apply (p : ℝ × ℝ) : timeRevHomeo p = timeRevL p := rfl

/-- The advanced solution of the massless wave equation `kgOp 0 u = f`. -/
noncomputable def advancedSol (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  retardedSol (fun q => f (timeRevL q)) (timeRevL p)

lemma timeRev_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun q => f (timeRevL q)) := hf.comp timeRevL.contDiff

lemma timeRev_hasCompactSupport {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun q => f (timeRevL q)) :=
  hc.comp_homeomorph timeRevHomeo

lemma advancedSol_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (advancedSol f) :=
  (retardedSol_contDiff (timeRev_contDiff hf) (timeRev_hasCompactSupport hc)).comp
    timeRevL.contDiff

/-- The advanced solution solves the massless wave equation `-u_tt + u_xx = f`. -/
theorem kgOp_advancedSol {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (p : ℝ × ℝ) : kgOp 0 (advancedSol f) p = f p := by
  have h := kgOp_timeRev 0
    (retardedSol_contDiff (timeRev_contDiff hf) (timeRev_hasCompactSupport hc)) p
  have h2 := kgOp_retardedSol (timeRev_contDiff hf) (timeRev_hasCompactSupport hc) (timeRevL p)
  have e : advancedSol f = fun q => retardedSol (fun q => f (timeRevL q)) (timeRevL q) := rfl
  rw [e, h, h2]
  simp

lemma advancedSol_eq_zero {f : ℝ × ℝ → ℝ} {T : ℝ} (h0 : ∀ p : ℝ × ℝ, T < p.1 → f p = 0)
    (p : ℝ × ℝ) (hp : T < p.1) : advancedSol f p = 0 := by
  unfold advancedSol
  apply retardedSol_eq_zero (T := -T)
  · intro q hq
    apply h0
    simp
    linarith
  · simp
    linarith

/-- **Existence and uniqueness of the advanced solution** of the massless wave equation
`-u_tt + u_xx = f` on `1+1` Minkowski space, for `f` of class `C²` with compact support that
vanishes for `t > T`: there is exactly one `C²` solution that vanishes for `t > T`. -/
theorem massless_advanced_existsUnique {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {T : ℝ} (h0 : ∀ p : ℝ × ℝ, T < p.1 → f p = 0) :
    ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp 0 u p = f p) ∧ ∀ p : ℝ × ℝ, T < p.1 → u p = 0 :=
  ⟨advancedSol f, ⟨advancedSol_contDiff hf hc, kgOp_advancedSol hf hc, advancedSol_eq_zero h0⟩,
    fun v ⟨hv, hkv, hv0⟩ =>
      advanced_unique 0 T hv (advancedSol_contDiff hf hc)
        (fun p => by rw [hkv p, kgOp_advancedSol hf hc]) hv0 (advancedSol_eq_zero h0)⟩

end Lightlike.GreenOperators
