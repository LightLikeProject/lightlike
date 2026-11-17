import Lightlike.Regge.Conv3.DsqLipschitz
import Lightlike.Regge.Conv3.JetSlice

/-!
# The true squared lengths of a star are the jet polynomial up to `ε⁵`

The six squared geodesic lengths `d(v + ε k_a, v + ε k_b)²` of a tetrahedron of the Kuhn star around a
hinge with midpoint `v` (`trueLen`) differ from the squared lengths `incLen` of the jet polynomial of
`g` at `v` by at most `C ε⁵`, uniformly for `v` in a compact subset of the domain
(`trueLen_sub_incLen`). The proof applies `IsRiemMetric.edge_sq_poly` to each of the six edges; the
vertices of the star have sup norm at most `1` relative to the hinge midpoint (`kpos_norm_le`).

## Main results

* `trueLen_sub_incLen`: the `O(ε⁵)` bound, uniform in the hinge midpoint.

**Limits.** The constants are not explicit; the bound is for the six edges of one tetrahedron of the
standard Kuhn star.
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- Every vertex of the star of a hinge, relative to the hinge midpoint, has sup norm at most `1`. -/
theorem kpos_norm_le (σ h : Fin 6) (a : Fin 4) : ‖kpos σ h a‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  fin_cases σ <;> fin_cases h <;> fin_cases a <;> fin_cases i <;>
    simp [kpos, kv, perms, hP, hQ] <;> norm_num

/-- The six squared geodesic lengths of the incidence `(σ, h)` of the star of the hinge with midpoint
`v`, at scale `ε`: `d(v + ε k_a, v + ε k_b)²` for the six edges. -/
noncomputable def trueLen (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (ε : ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => Geodesic.dist g U (v + ε • (s - (1 / 2 : ℝ) • Δ))
    (v + ε • (s + (1 / 2 : ℝ) • Δ)) ^ 2) σ h

/-- **The true squared lengths of a star are the jet polynomial up to `ε⁵`.** For a Riemannian metric `g`
on `U` and a compact `K ⊆ U` there are `C`, `r > 0` such that for every hinge midpoint `v ∈ K`,
`0 < ε ≤ r` and every incidence, the sup norm of `trueLen g U v ε σ h - incLen g v ε σ h` is at most
`C ε⁵`. -/
theorem trueLen_sub_incLen (hg : IsRiemMetric g U) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ σ h : Fin 6,
      ‖trueLen g U v ε σ h - incLen g v ε σ h‖ ≤ C * ε ^ 5 := by
  obtain ⟨C, r, hr, hC⟩ := hg.edge_sq_poly hK hKU
  have hC0 : 0 ≤ |C| := abs_nonneg C
  refine ⟨|C|, r, hr, fun v hv ε hε hεr σ h => ?_⟩
  -- one edge
  have edge : ∀ ka kb : Fin 3 → ℝ, ‖ka‖ ≤ 1 → ‖kb‖ ≤ 1 →
      |Geodesic.dist g U (v + ε • ((fun i => (ka i + kb i) / 2) - (1 / 2 : ℝ) • (fun i => kb i - ka i)))
          (v + ε • ((fun i => (ka i + kb i) / 2) + (1 / 2 : ℝ) • (fun i => kb i - ka i))) ^ 2
        - edgePoly g v (ε • (fun i => (ka i + kb i) / 2)) (ε • (fun i => kb i - ka i))| ≤
        |C| * ε ^ 5 := by
    intro ka kb hka hkb
    have e1 : (fun i => (ka i + kb i) / 2) - (1 / 2 : ℝ) • (fun i => kb i - ka i) = ka := by
      ext i; simp; ring
    have e2 : (fun i => (ka i + kb i) / 2) + (1 / 2 : ℝ) • (fun i => kb i - ka i) = kb := by
      ext i; simp; ring
    rw [e1, e2]
    have hwa : ‖ε • ka‖ ≤ ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]; nlinarith [norm_nonneg ka]
    have hwb : ‖ε • kb‖ ≤ ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]; nlinarith [norm_nonneg kb]
    have := hC v hv (ε • ka) (ε • kb) ε hwa hwb hεr
    have e3 : (fun i => ((ε • ka) i + (ε • kb) i) / 2) = ε • (fun i => (ka i + kb i) / 2) := by
      ext i; simp; ring
    have e4 : ε • kb - ε • ka = ε • (fun i => kb i - ka i) := by
      ext i; simp; ring
    rw [e3, e4] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i <;>
  · simp only [trueLen, incLen, incVec, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Fin.reduceFinMk, Fin.isValue]
    exact edge _ _ (kpos_norm_le _ _ _) (kpos_norm_le _ _ _)

end Lightlike.Regge.Conv3
