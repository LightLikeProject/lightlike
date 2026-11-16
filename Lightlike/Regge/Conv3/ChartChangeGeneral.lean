import Lightlike.Regge.Conv3.ChartChangeCoeffs
import Lightlike.Regge.Conv3.ChartChangeDChr
import Lightlike.Regge.Conv3.FlatStarJet
import Lightlike.Regge.Conv3.JetSlice

/-!
# The jet-level star identity at a general point

For a Riemannian metric `g` on `U` and any `m ∈ U`, `JetStarCore g m` holds (`jetStarCore_of_chart`), with
no condition on the first derivatives of `g`. The proof reduces to the flat case of `FlatStarJet.lean`
by the change of chart that removes the first derivatives:

* the second-order part `r` of the edge polynomial is `|Γ(s, Δ)|²_g` plus the flat second-order part of
  the shifted second derivatives `Sdd` (`edgeR_eq_displaced`, `incR_split`);
* the displaced flat star has angle sums `2π` for small displacement, so the first- and second-order
  coefficients of the angle sums of the displaced part vanish (`disp_coeffs`);
* `flat_star_identity` applies to `Sdd` (`sum_Einc_of_posDef`), and the scalar curvature of `g` at `m` is
  the scalar curvature of the flat jet with second derivatives `Sdd` (`scalar_eq_flat`, from
  `dChr_eq_flat`).

## Main results

* `scalar_eq_flat`: `R = 2 Rnum(g m, Sdd)/det²` at every point.
* `jetStarCore_of_chart`: the jet-level star identity at every point of a Riemannian metric.

**Limits.** The statement is local to one point `m` and to the Kuhn star of one edge scaled by `ε`; it
says nothing about the convergence of a Regge action or about a triangulation of a manifold. The
catalogue label is `structural`; the transformation law of the curvature used is the tensor
transformation law (carroll-1997, eq. (2.19)).
-/

open Real Matrix Lightlike
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)}

/-- **Scalar curvature at a general point as the flat formula for the shifted second derivatives.**
`R = 2 Rnum(g m, Sdd) / det²`: the scalar curvature at `m` equals the scalar curvature of a jet with
vanishing first derivatives and second derivatives `Sdd`. -/
theorem scalar_eq_flat (hg : IsCoordMetric g U) (hm : m ∈ U) :
    scalarCurvature g m = 2 * Rnum (fun i j => g m i j) (Sdd g m) / (g m).det ^ 2 := by
  rw [scalarCurvature_jet hg hm]
  have hinv : (g m)⁻¹ = ((g m).det)⁻¹ • (g m).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hof : Matrix.of (fun i j => g m i j) = g m := rfl
  simp only [dChr_eq_flat hg hm, Rnum, hof, hinv, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- **The second-order lengths split into the displaced part and the shifted flat part:**
`incR = incRd + lenR (Sdd g m)`. -/
theorem incR_split (σ h : Fin 6) : incR g m σ h = incRd g m σ h + lenR (Sdd g m) σ h := by
  ext i
  fin_cases i <;>
    simp [incR, incRd, lenR, incVec, edgeR_eq_displaced, Pi.add_apply]

/-- `Dh` is additive in its direction at an admissible base point. -/
theorem Dh_add {L : Fin 6 → ℝ} (hL : Valid L) (a b : Fin 6 → ℝ) :
    Dh (L, a + b) = Dh (L, a) + Dh (L, b) := by
  rw [← fderiv_Dsq (a + b) hL, ← fderiv_Dsq a hL, ← fderiv_Dsq b hL, map_add]

/-- **The second-order angle coefficient splits.** -/
theorem angC2_split (hg : IsRiemMetric g U) (hm : m ∈ U) (σ h : Fin 6) :
    angC2 g m σ h = angC2d g m σ h + Dh (incQ g m σ h, lenR (Sdd g m) σ h) := by
  have hV := valid_incQ (hg.posDef m hm) σ h
  unfold angC2 angC2d
  rw [incR_split, Dh_add hV]
  ring


/-- `clsSum` is additive. -/
theorem clsSum_add (w : Fin 3 → ℝ) (A B : Fin 6 → Fin 6 → ℝ) :
    clsSum w (fun σ h => A σ h + B σ h) = clsSum w A + clsSum w B := by
  classical
  simp only [clsSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

/-- The shifted second derivatives are symmetric in the first pair. -/
theorem Sdd_comm_kl (hg : IsCoordMetric g U) (hm : m ∈ U) (k l i j : Fin 3) :
    Sdd g m k l i j = Sdd g m l k i j := by
  have gs10 := g_symm_m hg hm 1 0
  have gs20 := g_symm_m hg hm 2 0
  have gs21 := g_symm_m hg hm 2 1
  simp only [Sdd, ddv_comm_kl hg hm k l i j, Fin.sum_univ_three, gs10, gs20, gs21]
  ring

/-- The shifted second derivatives are symmetric in the second pair. -/
theorem Sdd_comm_ij (hg : IsCoordMetric g U) (hm : m ∈ U) (k l i j : Fin 3) :
    Sdd g m k l i j = Sdd g m k l j i := by
  have gs10 := g_symm_m hg hm 1 0
  have gs20 := g_symm_m hg hm 2 0
  have gs21 := g_symm_m hg hm 2 1
  simp only [Sdd, ddv_comm_ij hg hm k l i j, Fin.sum_univ_three, gs10, gs20, gs21]
  ring

/-- **The sum over the 36 incidences for any symmetric second derivatives**, at a positive
definite Gram matrix. -/
theorem sum_Einc_of_posDef (hg : IsRiemMetric g U) (hm : m ∈ U)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (hd1 : ∀ k l i j, dd k l i j = dd l k i j)
    (hd2 : ∀ k l i j, dd k l i j = dd k l j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, Einc (lenQ (fun i j => g m i j) σ h) (lenR dd σ h) =
      Rnum (fun i j => g m i j) dd / (g m).det := by
  have hP := hg.posDef m hm
  have hs := posDef_symm hP
  have hdet : 0 < (g m).det := hP.det_pos
  have hGs : ∀ i j, (fun i j => g m i j) i j = (fun i j => g m i j) j i := fun i j => by
    have := congrFun (congrFun hs j) i
    simpa using this
  have hdetne : (Matrix.of (fun i j => g m i j)).det ≠ 0 := hdet.ne'
  have hsg : ∀ i j, g m j i = g m i j := fun i j => by
    have := congrFun (congrFun hs j) i
    simpa using this.symm
  have hP1 := face_ne hP (u := ![1,0,0]) (v := ![0,1,0])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 0 0 * g m 1 1 - g m 0 1 ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  have hP2 := face_ne hP (u := ![1,0,0]) (v := ![0,1,1])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 0 0 * (g m 1 1 + 2 * g m 1 2 + g m 2 2) - (g m 0 1 + g m 0 2) ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  have hP3 := face_ne hP (u := ![0,0,1]) (v := ![1,1,0])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 2 2 * (g m 0 0 + 2 * g m 0 1 + g m 1 1) - (g m 0 2 + g m 1 2) ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  have hP4 := face_ne hP (u := ![0,1,0]) (v := ![0,0,1])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 1 1 * g m 2 2 - g m 1 2 ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  have hP5 := face_ne hP (u := ![1,0,0]) (v := ![0,0,1])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 0 0 * g m 2 2 - g m 0 2 ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  have hP6 := face_ne hP (u := ![0,1,0]) (v := ![1,0,1])
    (by intro a b h; have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
        constructor <;> linarith)
    (P := g m 1 1 * (g m 0 0 + 2 * g m 0 2 + g m 2 2) - (g m 0 1 + g m 1 2) ^ 2)
    (by simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, hsg 0 1, hsg 0 2, hsg 1 2]
        ring)
  exact flat_star_identity (fun i j => g m i j) dd hGs hd1 hd2
      (fun h => hP1 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP2 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP3 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP4 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP5 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP6 (by beta_reduce at h ⊢; linear_combination h)) hdetne

/-- **The jet-level star identity at a general point.** For a Riemannian metric `g` on `U` and any
`m ∈ U` (no condition on the first derivatives), `JetStarCore g m` holds. It is the statement a proof
of the 3D convergence of the Regge action needs at every hinge; it says nothing about the convergence
itself, nor about a triangulation of a manifold. -/
theorem jetStarCore_of_chart (hg : IsRiemMetric g U) (hm : m ∈ U) : JetStarCore g m where
  valid σ h := valid_incQ (hg.posDef m hm) σ h
  angle_sum k := jet_angle_sum (hg.posDef m hm) k
  first_order k := (disp_coeffs hg hm k).1
  curvature := by
    have hP := hg.posDef m hm
    have hdet : 0 < (g m).det := hP.det_pos
    have hw : ∀ k, √(edgeQ g m (dirs k)) * clsSum (dirs k) (angC2 g m)
        = clsSum (dirs k) (fun σ h => √(incQ g m σ h 0) * Dh (incQ g m σ h, lenR (Sdd g m) σ h)) := by
      intro k
      have h2 := (disp_coeffs hg hm k).2
      have e : clsSum (dirs k) (angC2 g m) =
          clsSum (dirs k) (fun σ h => Dh (incQ g m σ h, lenR (Sdd g m) σ h)) := by
        have : angC2 g m = fun σ h => angC2d g m σ h + Dh (incQ g m σ h, lenR (Sdd g m) σ h) := by
          ext σ h; exact angC2_split hg hm σ h
        rw [this, clsSum_add, h2, zero_add]
      rw [e, clsSum, clsSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hc : InClass (dirs k) σ h
      · simp only [hc, ite_true]
        rw [inClass_incQ_zero hc]
      · simp [hc]
    simp only [hw]
    rw [class_partition]
    have hsum : ∀ σ h : Fin 6, √(incQ g m σ h 0) * Dh (incQ g m σ h, lenR (Sdd g m) σ h)
        = -(Einc (lenQ (fun i j => g m i j) σ h) (lenR (Sdd g m) σ h)) / √((g m).det) := by
      intro σ h
      rw [sqrt_Dh_inc hP σ h (lenR (Sdd g m) σ h), incQ_eq_lenQ]
      rfl
    simp only [hsum, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [sum_Einc_of_posDef hg hm (Sdd g m) (Sdd_comm_kl hg.coord hm) (Sdd_comm_ij hg.coord hm),
      scalar_eq_flat hg.coord hm]
    have hsd : √((g m).det) ^ 2 = (g m).det := Real.sq_sqrt hdet.le
    have hpos : 0 < √((g m).det) := Real.sqrt_pos.2 hdet
    have hd := hdet.ne'
    set R := Rnum (fun i j => g m i j) (Sdd g m)
    set d := (g m).det
    set r := √d
    have : d = r ^ 2 := hsd.symm
    rw [this]
    field_simp

end Lightlike.Regge.Conv3
