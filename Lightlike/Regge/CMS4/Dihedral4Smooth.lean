import Mathlib
import Lightlike.Regge.CMS4.Dihedral4Deriv
import Lightlike.Regge.Conv3.DihedralTaylor2

/-!
# Smoothness and a uniform Taylor bound for the dihedral angle of a 4-simplex

The dihedral angle `dihS s p q r t u` is a function of the matrix `s : V → V → ℝ` of squared
lengths. At every admissible matrix (both tetrahedra non-degenerate, angle not `0` or `π`) it is
smooth, of every order, in `s`; on a compact set of admissible matrices it has a uniform
third-order Taylor bound. It is the dimension-4 counterpart of `Conv3.contDiffAt_Dsq_all` and
`Conv3.dihSq_taylor3`.

## Main results

* `Valid4`, `isOpen_valid4`: the admissible matrices form an open set.
* `contDiffAt_dihS_all`, `contDiffAt_dihS`: smoothness of `dihS` in `s`.
* `dihS_taylor3`: the uniform bound `|dihS (s + δ) - dihS s - D dihS(s) δ - ½ D² dihS(s)(δ,δ)| ≤ M ‖δ‖³`.
-/

open Real Set Metric

namespace Lightlike.Regge4

variable {V : Type*} [Fintype V]

/-- The matrix `s` of squared lengths is admissible at the hinge `pqr` of `pqrtu`: both
tetrahedra are non-degenerate and the dihedral angle is not `0` or `π`. -/
def Valid4 (p q r t u : V) (s : V → V → ℝ) : Prop :=
  0 < gram3S s p q r t ∧ 0 < gram3S s p q r u ∧ 0 < 1 - cosS s p q r t u ^ 2

private theorem contDiff_gram (n : ℕ∞) (p q r t : V) :
    ContDiff ℝ n (fun s : V → V → ℝ => gram3S s p q r t) := by
  unfold gram3S ipS det3
  fun_prop

private theorem contDiff_mixed (n : ℕ∞) (p q r t u : V) :
    ContDiff ℝ n (fun s : V → V → ℝ => mixedS s p q r t u) := by
  unfold mixedS ipS det3
  fun_prop

theorem isOpen_valid4 (p q r t u : V) : IsOpen {s : V → V → ℝ | Valid4 p q r t u s} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨h1, h2, h3⟩ := hs
  have g1 := (contDiff_gram 0 p q r t).continuous
  have g2 := (contDiff_gram 0 p q r u).continuous
  have m := (contDiff_mixed 0 p q r t u).continuous
  have hsq : √(gram3S s p q r t * gram3S s p q r u) ≠ 0 := (sqrt_pos.mpr (mul_pos h1 h2)).ne'
  have c3 : ContinuousAt (fun s : V → V → ℝ => 1 - cosS s p q r t u ^ 2) s := by
    unfold cosS
    exact continuousAt_const.sub ((m.continuousAt.div (g1.continuousAt.mul g2.continuousAt).sqrt
      hsq).pow 2)
  exact ((g1.continuousAt.eventually (lt_mem_nhds h1)).and
    ((g2.continuousAt.eventually (lt_mem_nhds h2)).and
      (c3.eventually (lt_mem_nhds h3)))).mono fun _ h => h

/-- **The dihedral angle is smooth** (of every order `n`) in the squared lengths at every
admissible matrix. -/
theorem contDiffAt_dihS_all (n : ℕ∞) {p q r t u : V} {s : V → V → ℝ} (hs : Valid4 p q r t u s) :
    ContDiffAt ℝ n (fun s : V → V → ℝ => dihS s p q r t u) s := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hc1 : cosS s p q r t u ≠ 1 := fun h => by rw [h] at h3; norm_num at h3
  have hc2 : cosS s p q r t u ≠ -1 := fun h => by rw [h] at h3; norm_num at h3
  have hsq : √(gram3S s p q r t * gram3S s p q r u) ≠ 0 := (sqrt_pos.mpr (mul_pos h1 h2)).ne'
  have hc : ContDiffAt ℝ n (fun s : V → V → ℝ => cosS s p q r t u) s := by
    unfold cosS
    exact (contDiff_mixed n p q r t u).contDiffAt.div
      (((contDiff_gram n p q r t).mul (contDiff_gram n p q r u)).contDiffAt.sqrt
        (mul_pos h1 h2).ne') hsq
  exact (Real.contDiffAt_arccos hc2 hc1).comp s hc

theorem contDiffAt_dihS {p q r t u : V} {s : V → V → ℝ} (hs : Valid4 p q r t u s) :
    ContDiffAt ℝ 3 (fun s : V → V → ℝ => dihS s p q r t u) s :=
  contDiffAt_dihS_all 3 hs

/-- **Uniform third-order bound for the dihedral angle of a 4-simplex.** On a compact set `K` of
admissible matrices of squared lengths there are `M` and `r > 0` with
`|dihS (s + δ) - dihS s - D dihS(s) δ - ½ D² dihS(s)(δ, δ)| ≤ M ‖δ‖³` for `s ∈ K`, `‖δ‖ ≤ r`. -/
theorem dihS_taylor3 {p q r t u : V} {K : Set (V → V → ℝ)} (hK : IsCompact K)
    (hKV : ∀ s ∈ K, Valid4 p q r t u s) :
    ∃ M ρ : ℝ, 0 < ρ ∧ ∀ s ∈ K, ∀ δ : V → V → ℝ, ‖δ‖ ≤ ρ →
      |dihS (s + δ) p q r t u - dihS s p q r t u
        - fderiv ℝ (fun s : V → V → ℝ => dihS s p q r t u) s δ
        - (1 / 2) * fderiv ℝ (fderiv ℝ (fun s : V → V → ℝ => dihS s p q r t u)) s δ δ| ≤
        M * ‖δ‖ ^ 3 := by
  have hF : ContDiffOn ℝ 3 (fun s : V → V → ℝ => dihS s p q r t u) {s | Valid4 p q r t u s} :=
    fun s hs => (contDiffAt_dihS hs).contDiffWithinAt
  exact Lightlike.Regge.Conv3.taylor3_uniform (isOpen_valid4 p q r t u) hF hK
    (fun s hs => hKV s hs)

end Lightlike.Regge4
