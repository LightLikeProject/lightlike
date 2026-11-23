import Lightlike.Cosmology.FLRW

/-!
# The collapsing flat dust universe solves Friedmann's equations (GE3, non-vacuity)

For `c ∈ ℝ`, `a t = (c - t)^(2/3)` on `t < c` and `ρ t = 1 / (6 π G (c - t)^2)`, both Friedmann equations hold with
`k = 0`, `Λ = 0`, `p = 0` (dust). The Hubble rate is `a'/a = -2 / (3 (c - t)) < 0`: the universe collapses, so comoving
geodesics converge, which is the example showing that the hypotheses of `raychaudhuri_focusing_strongEC` can be met with
`Θ < 0`.
-/

open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike
namespace Cosmology

/-- Scale factor of the collapsing flat dust universe. -/
def collapseA (c : ℝ) (t : ℝ) : ℝ := (c - t) ^ (2 / 3 : ℝ)

/-- Dust density of the collapsing flat universe. -/
def collapseRho (Gn c : ℝ) (t : ℝ) : ℝ := 1 / (6 * Real.pi * Gn * (c - t) ^ 2)

theorem collapseA_hasDerivAt (c : ℝ) {t : ℝ} (ht : t < c) :
    HasDerivAt (collapseA c) (-(2 / 3) * (c - t) ^ (-(1 / 3) : ℝ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have h := h1.rpow_const (p := (2 / 3 : ℝ)) (Or.inl (sub_pos.2 ht).ne')
  have e : (2 / 3 : ℝ) - 1 = -(1 / 3) := by norm_num
  rw [e] at h
  have e2 : -(2 / 3) * (c - t) ^ (-(1 / 3) : ℝ) = -1 * (2 / 3) * (c - t) ^ (-(1 / 3) : ℝ) := by ring
  rw [e2]
  exact h

theorem collapseA_deriv(c : ℝ) {t : ℝ} (ht : t < c) :
    deriv (collapseA c) t = -(2 / 3) * (c - t) ^ (-(1 / 3) : ℝ) :=
  (collapseA_hasDerivAt c ht).deriv

theorem collapseA_deriv_deriv (c : ℝ) {t : ℝ} (ht : t < c) :
    deriv (deriv (collapseA c)) t = -(2 / 9) * (c - t) ^ (-(4 / 3) : ℝ) := by
  have hev : deriv (collapseA c) =ᶠ[𝓝 t] fun s => -(2 / 3) * (c - s) ^ (-(1 / 3) : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs using collapseA_deriv c hs
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun s : ℝ => c - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have h := (h1.rpow_const (p := (-(1 / 3) : ℝ)) (Or.inl (sub_pos.2 ht).ne')).const_mul (-(2 / 3))
  have e : (-(1 / 3) : ℝ) - 1 = -(4 / 3) := by norm_num
  rw [e] at h
  rw [h.deriv]
  ring

theorem collapseA_pos (c : ℝ) {t : ℝ} (ht : t < c) : 0 < collapseA c t :=
  Real.rpow_pos_of_pos (sub_pos.2 ht) _

/-- `a'/a = -2 / (3 (c - t))`. -/
theorem collapseA_hubble (c : ℝ) {t : ℝ} (ht : t < c) :
    deriv (collapseA c) t / collapseA c t = -2 / (3 * (c - t)) := by
  have hu : 0 < c - t := sub_pos.2 ht
  rw [collapseA_deriv c ht]
  unfold collapseA
  have : (c - t) ^ (2 / 3 : ℝ) = (c - t) ^ (-(1 / 3) : ℝ) * (c - t) := by
    rw [← Real.rpow_add_one hu.ne']; norm_num
  rw [this]
  have hp : 0 < (c - t) ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hu _
  field_simp

/-- `a''/a = -2 / (9 (c - t)^2)`. -/
theorem collapseA_accel (c : ℝ) {t : ℝ} (ht : t < c) :
    deriv (deriv (collapseA c)) t / collapseA c t = -2 / (9 * (c - t) ^ 2) := by
  have hu : 0 < c - t := sub_pos.2 ht
  rw [collapseA_deriv_deriv c ht]
  unfold collapseA
  have e1 : (c - t) ^ (-(4 / 3) : ℝ) = (c - t) ^ (-(1 / 3) : ℝ) * (c - t) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hu]; norm_num
  have e2 : (c - t) ^ (2 / 3 : ℝ) = (c - t) ^ (-(1 / 3) : ℝ) * (c - t) := by
    rw [← Real.rpow_add_one hu.ne']; norm_num
  rw [e1, e2, Real.rpow_neg_one]
  have hp : 0 < (c - t) ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hu _
  field_simp

/-- **The collapsing dust universe solves both Friedmann equations** (`k = 0`, `Λ = 0`, `p = 0`, `G > 0`). -/
theorem collapse_friedmann {Gn : ℝ} (hG : 0 < Gn) (c : ℝ) {t : ℝ} (ht : t < c) :
    FirstFriedmann (collapseA c) (collapseRho Gn c) 0 0 Gn t ∧
      SecondFriedmann (collapseA c) (collapseRho Gn c) (fun _ => 0) 0 Gn t := by
  have hu : 0 < c - t := sub_pos.2 ht
  have hpi := Real.pi_pos
  constructor
  · unfold FirstFriedmann
    rw [collapseA_hubble c ht]
    unfold collapseRho
    field_simp
    ring
  · unfold SecondFriedmann
    rw [collapseA_accel c ht]
    unfold collapseRho
    field_simp
    ring

end Cosmology
end Lightlike
