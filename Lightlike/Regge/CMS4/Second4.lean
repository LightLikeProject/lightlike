import Lightlike.Regge.CMS4.Pert4d
import Lightlike.Regge.CMS4.Dihedral4Curve

/-!
# The second-order coefficient of the moved class angle sum vanishes (dimension 4)

The moved star has squared lengths `q + t c + t² ρ` (`Qt_eq`) and its class angle sum is `2π` near
`t = 0` (`clsAng_eventually_const`). Expanding each dihedral angle to second order
(`dihS_curve_expansion`) and adding over the class, the `t²` coefficient is zero.

## Main results

* `angC2t`: the second-order coefficient of the moved dihedral angle.
* `tendsto_angQt_second`: the second-order Taylor remainder of the moved dihedral angle, divided by
  `t²`, tends to `0` as `t → 0⁺`.
* `second_gauge4`: `clsSum4 c (angC2t g m) = 0` in every admissible class.
-/

open Lightlike Real Filter Topology
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The second-order coefficient of the dihedral angle of the moved star of `(σ, h)`:
`D(incAng4) (q) (ρ) + ½ D²(incAng4) (q) (c, c)` with `ρ = Rt`. -/
noncomputable def angC2t (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : ℝ :=
  fderiv ℝ (incAng4 h) (incQ4 g m σ h) (Rt g m σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (incQ4 g m σ h) (incC4 g m σ h) (incC4 g m σ h)

/-- **Second-order expansion of the moved dihedral angle.** -/
theorem tendsto_angQt_second {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (σ : Fin 24) (h : Fin 10) :
    Tendsto (fun t : ℝ => (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
      - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) / t ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hdet : IsUnit (g m).det := isUnit_iff_ne_zero.2 hG.det_pos.ne'
  obtain ⟨M, r0, hr0, hE⟩ := dihS_curve_expansion (p := hP h) (q := hQ h) (r := hR h)
    (t := hS h) (u := hU h) (K := {incQ4 g m σ h}) isCompact_singleton
    (fun s hs' => by rw [Set.mem_singleton_iff] at hs'; rw [hs']; exact valid4_incQ g hG σ h)
    (B := max ‖incC4 g m σ h‖ ‖Rt g m σ h‖) (le_max_of_le_left (norm_nonneg _))
  refine squeeze_zero_norm' (a := fun t => |M| * t) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hr0] with t ht
    have hb := hE (incQ4 g m σ h) rfl (incC4 g m σ h) (Rt g m σ h) (le_max_left _ _)
      (le_max_right _ _) t ht.1 ht.2.le
    rw [← Qt_eq g hs m hdet σ h t] at hb
    have e : incAng4 h = dihF (hP h) (hQ h) (hR h) (hS h) (hU h) := rfl
    have hb' : |incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h) - t * angC14 g m σ h
        - t ^ 2 * angC2t g m σ h| ≤ M * t ^ 3 := by
      simpa only [e, angC14, angC2t, incAng4] using hb
    have ht2 : 0 < t ^ 2 := pow_pos ht.1 2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    calc _ ≤ M * t ^ 3 := hb'
      _ ≤ |M| * t ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self M) (pow_pos ht.1 3).le
      _ = |M| * t * t ^ 2 := by ring
  · have : Tendsto (fun t : ℝ => |M| * t) (𝓝 0) (𝓝 (|M| * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

open Classical in
/-- **The second-order coefficient of the moved class angle sum vanishes.** For a symmetric metric
field with `g m` positive definite, in every admissible class the `t²` coefficients of the moved
dihedral angles (`angC2t`) add up to zero. -/
theorem second_gauge4 {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hc : ClsOK c) : clsSum4 c (angC2t g m) = 0 := by
  have hT : Tendsto (fun t : ℝ => ∑ σ : Fin 24, ∑ h : Fin 10, if InClass4 c σ h then
      (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
        - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) / t ^ 2 else 0) (𝓝[>] 0) (𝓝 0) := by
    have hterm : ∀ (σ : Fin 24) (h : Fin 10), Tendsto (fun t : ℝ => if InClass4 c σ h then
      (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
        - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) / t ^ 2 else 0) (𝓝[>] 0) (𝓝 0) := by
      intro σ h
      by_cases hh : InClass4 c σ h
      · simp only [hh, ↓reduceIte]
        exact tendsto_angQt_second g hG hs σ h
      · simp only [hh, ↓reduceIte]
        exact tendsto_const_nhds
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 24)) fun σ _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 10)) fun h _ => hterm σ h
    simpa using this
  have hfo := first_order4 g hG hs c hc
  have h0 := clsAng_zero g hG hs c hc
  have h00 : clsSum4 c (fun σ h => incAng4 h (incQ4 g m σ h)) = 2 * π := angle_sum4 g hG c hc
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∑ σ : Fin 24, ∑ h : Fin 10, if InClass4 c σ h then
      (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
        - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) / t ^ 2 else 0)
      = - clsSum4 c (angC2t g m) := by
    have h1 := (clsAng_eventually_const g hG hs c hc).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
    have ht0' : (0 : ℝ) < t := ht0
    have key : clsAng g m c t - clsSum4 c (fun σ h => incAng4 h (incQ4 g m σ h))
        - t * clsSum4 c (angC14 g m) - t ^ 2 * clsSum4 c (angC2t g m)
        = ∑ σ : Fin 24, ∑ h : Fin 10, if InClass4 c σ h then
          (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
            - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) else 0 := by
      have pt : ∀ σ h, (if InClass4 c σ h then incAng4 h (Qt g m σ h t) else 0)
          - (if InClass4 c σ h then incAng4 h (incQ4 g m σ h) else 0)
          - t * (if InClass4 c σ h then angC14 g m σ h else 0)
          - t ^ 2 * (if InClass4 c σ h then angC2t g m σ h else 0)
          = if InClass4 c σ h then (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
            - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) else 0 := by
        intro σ h; split_ifs <;> simp
      simp only [clsAng, clsSum4, Finset.mul_sum, ← Finset.sum_sub_distrib, pt]
    rw [ht, h00, hfo] at key
    have : ∑ σ : Fin 24, ∑ h : Fin 10, (if InClass4 c σ h then
      (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
        - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) / t ^ 2 else 0)
        = (∑ σ : Fin 24, ∑ h : Fin 10, if InClass4 c σ h then
          (incAng4 h (Qt g m σ h t) - incAng4 h (incQ4 g m σ h)
            - t * angC14 g m σ h - t ^ 2 * angC2t g m σ h) else 0) / t ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> simp
    rw [this, ← key]
    field_simp
    ring
  have hlim : Tendsto (fun _ : ℝ => - clsSum4 c (angC2t g m)) (𝓝[>] 0) (𝓝 0) :=
    hT.congr' hev
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  linarith

end Lightlike.Regge4
