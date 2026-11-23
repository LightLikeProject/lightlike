import Mathlib
import Lightlike.Spacetime.GreenOperators.NullCoordinates

/-!
# Uniqueness of retarded and advanced solutions on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
Two `C²` solutions `F₁, F₂ : ℝ × ℝ → ℝ` of the inhomogeneous Klein–Gordon equation
`P F = f` (`kgOp`) that both vanish in the past `t < T` coincide: this is the uniqueness half of
the retarded Green operator.  The advanced version (vanishing for `t > T`) follows by the time
reversal `(t, x) ↦ (-t, x)`.

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- `kgOp` is additive for `C²` functions. -/
lemma kgOp_sub (m : ℝ) {F G : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (p : ℝ × ℝ) :
    kgOp m (F - G) p = kgOp m F p - kgOp m G p := by
  have dF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have dG : Differentiable ℝ G := hG.differentiable (by norm_num)
  have ddF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have ddG : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (F - G) = fun q => fderiv ℝ F q - fderiv ℝ G q := by
    funext q
    exact fderiv_sub (dF q) (dG q)
  have h2 : fderiv ℝ (fderiv ℝ (F - G)) p = fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ G) p := by
    rw [h1]
    exact fderiv_sub (ddF p) (ddG p)
  unfold kgOp
  rw [h2]
  simp only [Pi.sub_apply, sub_apply]
  ring

/-- **Uniqueness of the retarded solution** on 1+1 Minkowski space: two `C²` functions with the same
Klein–Gordon source that both vanish for `t < T` are equal. -/
theorem retarded_unique (m T : ℝ) {F G : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hFG : ∀ p, kgOp m F p = kgOp m G p) (hF0 : ∀ p : ℝ × ℝ, p.1 < T → F p = 0)
    (hG0 : ∀ p : ℝ × ℝ, p.1 < T → G p = 0) : F = G := by
  have hsub : ContDiff ℝ 2 (F - G) := hF.sub hG
  have := kg_eq_zero_of_vanishes_before (F - G) m T hsub
    (fun p => by rw [kgOp_sub m hF hG, hFG p, sub_self])
    (fun p hp => by simp [hF0 p hp, hG0 p hp])
  funext p
  have := this p
  simpa [sub_eq_zero] using this

end Lightlike.GreenOperators
