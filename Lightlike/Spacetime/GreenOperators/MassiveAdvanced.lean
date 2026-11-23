import Mathlib
import Lightlike.Spacetime.GreenOperators.MassiveExistence
import Lightlike.Spacetime.GreenOperators.Advanced

/-!
# The retarded and advanced Green solutions of the Klein–Gordon equation on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
The advanced solution `massiveAdvancedSol m f = massiveSol m (f ∘ timeRev) ∘ timeRev` is obtained by
time reversal.  `advanced_existsUnique` is the advanced counterpart of `retarded_existsUnique`, and
`green_existsUnique` states both: for every mass and every `f ∈ C_c²` there is exactly one `C²`
solution of `kgOp m u = f` vanishing for `t < T` (when `f` does), and exactly one vanishing for
`t > T` (when `f` does).
-/

namespace Lightlike.GreenOperators

/-- The advanced solution of `kgOp m u = f`. -/
noncomputable def massiveAdvancedSol (m : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  massiveSol m (fun q => f (timeRevL q)) (timeRevL p)

lemma massiveAdvancedSol_contDiff (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (massiveAdvancedSol m f) :=
  (massiveSol_contDiff m (timeRev_contDiff hf) (timeRev_hasCompactSupport hc)).comp
    timeRevL.contDiff

theorem kgOp_massiveAdvancedSol (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (p : ℝ × ℝ) : kgOp m (massiveAdvancedSol m f) p = f p := by
  have h := kgOp_timeRev m
    (massiveSol_contDiff m (timeRev_contDiff hf) (timeRev_hasCompactSupport hc)) p
  have h2 := kgOp_massiveSol m (timeRev_contDiff hf) (timeRev_hasCompactSupport hc) (timeRevL p)
  have e : massiveAdvancedSol m f
      = fun q => massiveSol m (fun q => f (timeRevL q)) (timeRevL q) := rfl
  rw [e, h, h2]
  simp

lemma massiveAdvancedSol_eq_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {T : ℝ}
    (h0 : ∀ p : ℝ × ℝ, T < p.1 → f p = 0) (p : ℝ × ℝ) (hp : T < p.1) :
    massiveAdvancedSol m f p = 0 := by
  unfold massiveAdvancedSol
  apply massiveSol_eq_zero (T := -T)
  · intro q hq
    apply h0
    simp
    linarith
  · simp
    linarith

/-- **Existence and uniqueness of the advanced solution** of the Klein–Gordon equation
`-u_tt + u_xx - m² u = f` on `1+1` Minkowski space (any `m`), for `f` of class `C²` with compact
support that vanishes for `t > T`: there is exactly one `C²` solution that vanishes for `t > T`. -/
theorem advanced_existsUnique (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {T : ℝ} (h0 : ∀ p : ℝ × ℝ, T < p.1 → f p = 0) :
    ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp m u p = f p) ∧ ∀ p : ℝ × ℝ, T < p.1 → u p = 0 :=
  ⟨massiveAdvancedSol m f, ⟨massiveAdvancedSol_contDiff m hf hc, kgOp_massiveAdvancedSol m hf hc,
      massiveAdvancedSol_eq_zero h0⟩,
    fun v ⟨hv, hkv, hv0⟩ =>
      advanced_unique m T hv (massiveAdvancedSol_contDiff m hf hc)
        (fun p => by rw [hkv p, kgOp_massiveAdvancedSol m hf hc]) hv0
        (massiveAdvancedSol_eq_zero h0)⟩

/-- **Existence and uniqueness of the advanced and retarded Green solutions** of the
Klein–Gordon equation `-u_tt + u_xx - m² u = f` on `1+1` Minkowski space, for every mass `m` and
every `f ∈ C_c²`: if `f` vanishes for `t < T` there is exactly one `C²` solution vanishing for
`t < T`; if `f` vanishes for `t > T` there is exactly one `C²` solution vanishing for `t > T`. -/
theorem green_existsUnique (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    (∀ T : ℝ, (∀ p : ℝ × ℝ, p.1 < T → f p = 0) →
      ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp m u p = f p) ∧
        ∀ p : ℝ × ℝ, p.1 < T → u p = 0) ∧
    (∀ T : ℝ, (∀ p : ℝ × ℝ, T < p.1 → f p = 0) →
      ∃! u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p, kgOp m u p = f p) ∧
        ∀ p : ℝ × ℝ, T < p.1 → u p = 0) :=
  ⟨fun _ h0 => retarded_existsUnique m hf hc h0, fun _ h0 => advanced_existsUnique m hf hc h0⟩

end Lightlike.GreenOperators
