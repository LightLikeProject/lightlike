import Lightlike.Regge.Conv3.FlatStarIdentity
import Lightlike.Regge.Conv3.KuhnCore
import Lightlike.Regge.Conv3.JetCore

/-!
# The pointwise Saint-Venant identity for the Kuhn star

At a point where a perturbation `h` of the Euclidean metric has value `H` and symmetric second derivatives
`dd k l i j = ∂_k ∂_l h_ij`, the interpolated squared lengths of the star of a Kuhn hinge change, to second
order in the mesh, by `rf dd s Δ = ½ ∂²h(s, s)(Δ, Δ) + (1/24) ∂²h(Δ, Δ)(Δ, Δ)` (`lenR`), and to zeroth order by
`qf H Δ`. Summed over the 36 incidences (tetrahedron, hinge) of the Kuhn star, with the weight
`-qf H (w) / (2 |w|²)` of the hinge length `|w|` and its interpolated first variation `qf H w`,
the hinge length times the first variation of the dihedral angle (`dth`) gives the Saint-Venant pairing
`-¼ Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln` (`sv_pointwise`). This is the pointwise density of the
linearization of the 3D Regge action: its integral is `¼ ⟨curl^t curl h, h⟩` up to sign (Christiansen 2011, eq. (87)),
with `curl^t curl` as defined in his section 2 (the curl of the rows, transposed, the curl of the rows):
`(curl^t curl u)_ij = ε_ikl ε_jmn ∂_k ∂_m u_ln` for symmetric `u`.

## Main results

* `class_A0`, `class_A1`: the zeroth- and first-order interpolated variations have vanishing class sums of `dth`
  (the angle sums stay `2π` for a constant metric and to first order).

* `svPair`: the Saint-Venant pairing `Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln` at a point.
* `sv_pointwise`: the identity, a polynomial identity bilinear in `H` and `dd`.

**Limits.** An identity at one point for symmetric `H` and symmetric second derivatives; no analysis.
The relation of the sign to Christiansen's convention for the deficit angle is not stated here: the numerical
check `scripts/regge/regge3d_linearized_check.py` fixes it (`Q_n → -¼ ⟨curl^t curl h, h⟩` for the deficit
`2π - Σ θ`, which has the sign of the Einstein–Hilbert second variation).
-/

open Real
namespace Lightlike.Regge.Linear3
open Lightlike.Regge.Conv3

/-- The Levi-Civita symbol on `Fin 3`. -/
noncomputable def eps3 (i j k : Fin 3) : ℝ := ((i : ℝ) - j) * ((j : ℝ) - k) * ((k : ℝ) - i) / 2

/-- The vector of the hinge of the incidence `(σ, h)`. -/
noncomputable def hvec (σ h : Fin 6) : Fin 3 → ℝ := fun i => kv (hQ h) (perms σ i) - kv (hP h) (perms σ i)

/-- The Saint-Venant pairing `Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln` at a point. -/
noncomputable def svPair (H : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ n, H i j * (eps3 i k l * eps3 j m n * dd k m l n)

-- needs about 0.7 million heartbeats (measured with `#count_heartbeats`); the cap is about twice that
set_option maxHeartbeats 1500000 in
set_option maxRecDepth 100000 in
theorem sv_pointwise (H : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hH : ∀ i j, H i j = H j i) (hd1 : ∀ k l i j, dd k l i j = dd l k i j)
    (hd2 : ∀ k l i j, dd k l i j = dd k l j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, (-(qf H (hvec σ h)) / (2 * hbase h 0)) * dth h (lenR dd σ h) =
      -(1 / 4) * svPair H dd := by
  simp (config := { maxSteps := 100000000 }) only [Fin.sum_univ_six, lenR_0_0,lenR_0_1,lenR_0_2,lenR_0_3,lenR_0_4,lenR_0_5,lenR_1_0,lenR_1_1,lenR_1_2,lenR_1_3,lenR_1_4,lenR_1_5,lenR_2_0,lenR_2_1,lenR_2_2,lenR_2_3,lenR_2_4,lenR_2_5,lenR_3_0,lenR_3_1,lenR_3_2,lenR_3_3,lenR_3_4,lenR_3_5,lenR_4_0,lenR_4_1,lenR_4_2,lenR_4_3,lenR_4_4,lenR_4_5,lenR_5_0,lenR_5_1,lenR_5_2,lenR_5_3,lenR_5_4,lenR_5_5, hvec, kv, perms, hP, hQ, hR, hS, hbase,
    dth, rf, ddq, qf, svPair, eps3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  simp only [hH 1 0, hH 2 0, hH 2 1, hd1 1 0, hd1 2 0, hd1 2 1, hd2 _ _ 1 0, hd2 _ _ 2 0, hd2 _ _ 2 1]
  ring


/-- The first-derivative form `Σ s_k ∂_k h_ij Δ_i Δ_j` of the interpolated squared length. -/
noncomputable def d1q (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (s Δ : Fin 3 → ℝ) : ℝ :=
  ∑ k, ∑ i, ∑ j, s k * dh k i j * Δ i * Δ j

theorem class_A0 (H : Fin 3 → Fin 3 → ℝ) (hH : ∀ i j, H i j = H j i) (k : Fin 7) :
    clsSum (dirs k) (fun σ h => dth h (incVec (fun _ Δ => qf H Δ) σ h)) = 0 := by
  fin_cases k <;>
  · simp only [clsSum, InClass, dirs, Fin.sum_univ_six, Fin.forall_fin_succ,
      perms, hP, hQ, kv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    norm_num [Matrix.cons_val_zero]
    simp only [incVec, dth, qf, kpos, perms, hP, hQ, hR, hS, kv, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    norm_num
    simp only [hH 1 0, hH 2 0, hH 2 1]
    ring


-- needs about 0.66 million heartbeats (measured with `#count_heartbeats`); the cap is about twice that
set_option maxHeartbeats 1400000 in
theorem class_A1 (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (hd : ∀ k i j, dh k i j = dh k j i) (k : Fin 7) :
    clsSum (dirs k) (fun σ h => dth h (incVec (fun s Δ => d1q dh s Δ) σ h)) = 0 := by
  fin_cases k <;>
  · simp only [clsSum, InClass, dirs, Fin.sum_univ_six, Fin.forall_fin_succ,
      perms, hP, hQ, kv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    norm_num [Matrix.cons_val_zero]
    simp only [incVec, dth, d1q, kpos, perms, hP, hQ, hR, hS, kv, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    norm_num
    simp only [hd _ 1 0, hd _ 2 0, hd _ 2 1]
    ring

end Lightlike.Regge.Linear3
