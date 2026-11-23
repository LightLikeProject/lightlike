import Lightlike.Regge.CMS4.Pert4b
import Lightlike.Regge.CMS4.FanInt4

/-!
# The moved star closes: its class angle sum is a multiple of `2π` for small `t`

For a chain of incidences of a class `c` that closes up (`ch n = ch 0`) with positively oriented
consecutive quotient vectors, the moved lattice vectors `Psi t z` still have a positive axis Gram
determinant and positive orientation for small `t`. By `fan_int4` the angle sum of the moved star
over the chain lies in `2π ℤ`.

## Main results

* `Psi_zero`, `continuous_Psi`: the moved vectors are continuous in `t` and equal `z` at `t = 0`.
* `eventually_chain_int`: for small `t` the angle sum over a closed positive chain is in `2π ℤ`.
-/

open Lightlike Real Filter Topology
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- At `t = 0` the moved vector is the original one. -/
theorem Psi_zero (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (z : Fin 4 → ℝ) : Psi g m c 0 z = z := by
  simp [Psi, Phi]

/-- The moved vectors are continuous in `t`. -/
theorem continuous_Psi (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (z : Fin 4 → ℝ) :
    Continuous fun t : ℝ => Psi g m c t z := by
  unfold Psi Phi
  fun_prop

/-- The axis Gram determinant of two moved vectors is continuous in `t`. -/
theorem continuous_gramW_Psi (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (z1 z2 : Fin 4 → ℝ) :
    Continuous fun t : ℝ => gramW (g m) (Psi g m c t z1) (Psi g m c t z2) := by
  have h1 := continuous_Psi g m c z1
  have h2 := continuous_Psi g m c z2
  unfold gramW
  exact ((h1.dotProduct (continuous_const.matrix_mulVec h1)).mul
      (h2.dotProduct (continuous_const.matrix_mulVec h2))).sub
    ((h1.dotProduct (continuous_const.matrix_mulVec h2)).mul
      (h2.dotProduct (continuous_const.matrix_mulVec h1)))

/-- The orientation determinant of four moved vectors is continuous in `t`. -/
theorem continuous_det4_Psi (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (z1 z2 z3 z4 : Fin 4 → ℝ) :
    Continuous fun t : ℝ =>
      det4 (Psi g m c t z1) (Psi g m c t z2) (Psi g m c t z3) (Psi g m c t z4) := by
  have h1 := continuous_Psi g m c z1
  have h2 := continuous_Psi g m c z2
  have h3 := continuous_Psi g m c z3
  have h4 := continuous_Psi g m c z4
  simp only [det4_expand, d3]
  fun_prop

/-- **For small `t` the angle sum of the moved star over a closed positive chain is in `2π ℤ`.** -/
theorem eventually_chain_int {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (n : ℕ) (hn : 0 < n) (ch : ℕ → Fin 24 × Fin 10)
    (hmem : ∀ i < n, ch i ∈ incsOf c)
    (hadj : ∀ i < n, (orient c (ch i)).2 = (orient c (ch (i + 1))).1)
    (hpos : ∀ i < n, 0 < det4Z (cw1 c) (ax2 c) (orient c (ch i)).1 (orient c (ch i)).2)
    (hcl : ch n = ch 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ k : ℤ,
      ∑ i ∈ Finset.range n, incAng4 (ch i).2 (Qt g m (ch i).1 (ch i).2 t) = 2 * π * k := by
  have hD0 := gramW_class_pos g hG c (ch 0) (hmem 0 hn)
  have eD : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < gramW (g m) (Psi g m c t (fun i => (cw1 c i : ℝ)))
      (Psi g m c t (fun i => (ax2 c i : ℝ))) := by
    have hc := (continuous_gramW_Psi g m c (fun i => (cw1 c i : ℝ))
      (fun i => (ax2 c i : ℝ))).continuousAt (x := 0)
    refine hc.eventually (lt_mem_nhds ?_)
    simpa only [Psi_zero] using hD0
  have eP : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i ∈ Finset.range n,
      0 < det4 (Psi g m c t (fun i => (cw1 c i : ℝ))) (Psi g m c t (fun i => (ax2 c i : ℝ)))
        (Psi g m c t (fun k => ((orient c (ch i)).1 k : ℝ)))
        (Psi g m c t (fun k => ((orient c (ch i)).2 k : ℝ))) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hc := (continuous_det4_Psi g m c (fun i => (cw1 c i : ℝ)) (fun i => (ax2 c i : ℝ))
      (fun k => ((orient c (ch i)).1 k : ℝ)) (fun k => ((orient c (ch i)).2 k : ℝ))).continuousAt
      (x := 0)
    refine hc.eventually (lt_mem_nhds ?_)
    simp only [Psi_zero]
    rw [det4_cast]
    exact_mod_cast hpos i hi'
  filter_upwards [eD, eP] with t hD hP
  set v : ℕ → Fin 4 → ℝ := fun i => Psi g m c t (fun k => ((orient c (ch i)).1 k : ℝ)) with hv
  have hnext : ∀ i < n, Psi g m c t (fun k => ((orient c (ch i)).2 k : ℝ)) = v (i + 1) := by
    intro i hi
    simp only [hv, hadj i hi]
  have hposv : ∀ i < n, 0 < det4 (Psi g m c t (fun i => (cw1 c i : ℝ)))
      (Psi g m c t (fun i => (ax2 c i : ℝ))) (v i) (v (i + 1)) := by
    intro i hi
    rw [← hnext i hi]
    exact hP i (Finset.mem_range.2 hi)
  have hcv : v n = v 0 := by simp only [hv, hcl]
  obtain ⟨k, hk⟩ := fan_int4 hG hD n hn v hposv hcv
  refine ⟨k, ?_⟩
  rw [← hk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [incAng4_Qt_class g hs c (ch i) (hmem i hi') t hD, hnext i hi']

end Lightlike.Regge4
