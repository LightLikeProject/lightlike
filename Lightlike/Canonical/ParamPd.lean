import Mathlib
import Lightlike.Canonical.LieDeriv

/-!
# Parameter-dependent functions: partial derivatives in the coordinates commute with the parameter

For `G : ℝ → (Fin d → ℝ) → ℝ` jointly smooth, `pd e (G t) y` is jointly smooth and its `t`-derivative is
`pd e` of the `t`-derivative (symmetry of the second derivative on `ℝ × ℝᵈ`).
-/

open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- A function of `(t, y)`, smooth jointly. -/
def JointSmooth (G : ℝ → (Fin d → ℝ) → ℝ) : Prop := ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2)

lemma pd_eq_fderiv {G : ℝ → (Fin d → ℝ) → ℝ} (hG : JointSmooth G) (e : Fin d) (t : ℝ) (y : Fin d → ℝ) :
    Lightlike.pd e (G t) y = fderiv ℝ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) (t, y) (0, Pi.single e 1) := by
  have hF : DifferentiableAt ℝ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) (t, y) :=
    (hG.differentiable (by simp)) _
  have hι : HasFDerivAt (fun z : Fin d → ℝ => ((t, z) : ℝ × (Fin d → ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (Fin d → ℝ)) y := (hasFDerivAt_prodMk_right t y)
  have := (hF.hasFDerivAt.comp y hι).fderiv
  simp only [Lightlike.pd]
  rw [show G t = (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) ∘ (fun z : Fin d → ℝ => ((t, z) : ℝ × (Fin d → ℝ))) from rfl,
    this]
  simp

lemma jointSmooth_pd {G : ℝ → (Fin d → ℝ) → ℝ} (hG : JointSmooth G) (e : Fin d) :
    JointSmooth (fun t y => Lightlike.pd e (G t) y) := by
  have : (fun p : ℝ × (Fin d → ℝ) => Lightlike.pd e (G p.1) p.2) =
      fun p => fderiv ℝ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) p (0, Pi.single e 1) := by
    funext p; exact pd_eq_fderiv hG e p.1 p.2
  unfold JointSmooth
  rw [this]
  exact (hG.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma deriv_t_eq {G : ℝ → (Fin d → ℝ) → ℝ} (hG : JointSmooth G) (t : ℝ) (y : Fin d → ℝ) :
    deriv (fun s => G s y) t = fderiv ℝ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) (t, y) (1, 0) := by
  have hF : DifferentiableAt ℝ (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) (t, y) :=
    (hG.differentiable (by simp)) _
  have hι : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × (Fin d → ℝ))) ((1, 0) : ℝ × (Fin d → ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact (hF.hasFDerivAt.comp_hasDerivAt t hι).deriv

/-- **Partial derivatives in the coordinates commute with the parameter derivative.** -/
lemma deriv_pd_comm {G : ℝ → (Fin d → ℝ) → ℝ} (hG : JointSmooth G) (e : Fin d) (t y) :
    deriv (fun s => Lightlike.pd e (G s) y) t =
      Lightlike.pd e (fun z => deriv (fun s => G s z) t) y := by
  set F := fun p : ℝ × (Fin d → ℝ) => G p.1 p.2 with hFdef
  have hF2 : ContDiffAt ℝ 2 F (t, y) := (hG.of_le (by simp)).contDiffAt
  have hD : DifferentiableAt ℝ (fderiv ℝ F) (t, y) :=
    ((hG.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) _
  have hι : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × (Fin d → ℝ))) ((1, 0) : ℝ × (Fin d → ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have h1 : HasDerivAt (fun s => fderiv ℝ F (s, y)) (fderiv ℝ (fderiv ℝ F) (t, y) (1, 0)) t :=
    hD.hasFDerivAt.comp_hasDerivAt t hι
  have lhs : deriv (fun s => Lightlike.pd e (G s) y) t =
      fderiv ℝ (fderiv ℝ F) (t, y) (1, 0) (0, Pi.single e 1) := by
    have := (h1.clm_apply (hasDerivAt_const t ((0 : ℝ), (Pi.single e 1 : Fin d → ℝ)))).deriv
    simp only [pd_eq_fderiv hG e]
    rw [← hFdef]
    simpa using this
  have hfun : (fun z => deriv (fun s => G s z) t) = fun z => fderiv ℝ F (t, z) (1, 0) := by
    funext z; exact deriv_t_eq hG t z
  have hι2 : HasFDerivAt (fun z : Fin d → ℝ => ((t, z) : ℝ × (Fin d → ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (Fin d → ℝ)) y := hasFDerivAt_prodMk_right t y
  have h2 : HasFDerivAt (fun z => fderiv ℝ F (t, z)) ((fderiv ℝ (fderiv ℝ F) (t, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin d → ℝ))) y := hD.hasFDerivAt.comp y hι2
  have rhs : Lightlike.pd e (fun z => deriv (fun s => G s z) t) y =
      fderiv ℝ (fderiv ℝ F) (t, y) (0, Pi.single e 1) (1, 0) := by
    rw [hfun]
    simp only [Lightlike.pd]
    have := (h2.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Fin d → ℝ)) y)).fderiv
    rw [this]
    simp
  rw [lhs, rhs]
  exact (hF2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) _ _

end Lightlike.Canonical

end
