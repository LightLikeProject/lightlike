import Mathlib
import Lightlike.Spacetime.GreenOperators.Uniqueness

/-!
# Time reversal for the Klein–Gordon operator on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
`kgOp m (F ∘ timeRev) = kgOp m F ∘ timeRev` for `timeRev (t, x) = (-t, x)`, and from it the
uniqueness of the advanced solution (`advanced_unique`).

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- The time reversal `(t, x) ↦ (-t, x)` as a continuous linear map. -/
noncomputable def timeRevL : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma timeRevL_apply (p : ℝ × ℝ) : timeRevL p = (-p.1, p.2) := rfl

lemma fderiv_comp_timeRev {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (q : ℝ × ℝ) :
    fderiv ℝ (fun p => F (timeRevL p)) q = (fderiv ℝ F (timeRevL q)).comp timeRevL := by
  have := fderiv_comp (𝕜 := ℝ) q (hF (timeRevL q)) timeRevL.differentiableAt
  simpa [Function.comp_def] using this

/-- `kgOp` commutes with time reversal. -/
lemma kgOp_timeRev (m : ℝ) {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (p : ℝ × ℝ) :
    kgOp m (fun q => F (timeRevL q)) p = kgOp m F (timeRevL p) := by
  have dF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have ddF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (fun q => F (timeRevL q))
      = fun q => (fderiv ℝ F (timeRevL q)).comp timeRevL := by
    funext q
    exact fderiv_comp_timeRev dF q
  let L : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ).flip timeRevL
  have h2 : (fun q => (fderiv ℝ F (timeRevL q)).comp timeRevL)
      = fun q => L ((fderiv ℝ F) (timeRevL q)) := by
    funext q
    rfl
  have h3 : fderiv ℝ (fun q => L ((fderiv ℝ F) (timeRevL q))) p
      = L.comp ((fderiv ℝ (fderiv ℝ F) (timeRevL p)).comp timeRevL) := by
    have hd : HasFDerivAt (fun q => (fderiv ℝ F) (timeRevL q))
        ((fderiv ℝ (fderiv ℝ F) (timeRevL p)).comp timeRevL) p :=
      (ddF (timeRevL p)).hasFDerivAt.comp p timeRevL.hasFDerivAt
    exact (L.hasFDerivAt.comp p hd).fderiv
  unfold kgOp
  rw [h1, h2, h3]
  have e : (((-1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = -((1 : ℝ), (0 : ℝ)) := by ext <;> simp
  simp [L]
  rw [e]
  simp only [map_neg, neg_apply, neg_neg]

/-- **Uniqueness of the advanced solution** on 1+1 Minkowski space: two `C²` functions with the same
Klein–Gordon source that both vanish for `t > T` are equal. -/
theorem advanced_unique (m T : ℝ) {F G : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hFG : ∀ p, kgOp m F p = kgOp m G p) (hF0 : ∀ p : ℝ × ℝ, T < p.1 → F p = 0)
    (hG0 : ∀ p : ℝ × ℝ, T < p.1 → G p = 0) : F = G := by
  have hFr : ContDiff ℝ 2 (fun q => F (timeRevL q)) := hF.comp timeRevL.contDiff
  have hGr : ContDiff ℝ 2 (fun q => G (timeRevL q)) := hG.comp timeRevL.contDiff
  have key := retarded_unique m (-T) hFr hGr
    (fun p => by rw [kgOp_timeRev m hF, kgOp_timeRev m hG]; exact hFG _)
    (fun p hp => hF0 _ (by simp; linarith))
    (fun p hp => hG0 _ (by simp; linarith))
  funext p
  have := congrFun key (timeRevL p)
  simpa using this

end Lightlike.GreenOperators
