import Lightlike.Regge.Conv3.FlatStarIdentity
import Lightlike.Regge.Conv3.JetCurvature
import Lightlike.Regge.Conv3.JetSlice

/-!
# The jet-level star identity at a point with vanishing metric gradient

For a Riemannian metric `g` on an open set of `ℝ³` and a point `m` where all first partial derivatives
of `g` vanish (for example the centre of normal coordinates), the jet-level star identity
`JetStarCore g m` holds, whatever the positive definite matrix `g m` and the second derivatives are.

At such a point the first-order part `c` of the squared edge lengths vanishes and the Christoffel
symbols vanish, so the second-order coefficient of a class angle sum is the first variation
`Dh(q, r)` of the dihedral angle along the second-order lengths `r`, which are linear in the
second derivatives of `g`. The sum over the 36 incidences of `√a · Dh(q, r)` is, by
`sqrt_Dh_inc`, minus the sum of the polynomial derivative combinations `Einc` divided by `√det g`,
and `flat_star_identity` evaluates that sum as `Rnum / det`, which is `det R / 2`.

**Scope.** This is not the general chart. The convergence of the 3D Regge action needs the same
statement at every hinge, where the first derivatives of `g` do not vanish; that case is open.

## Main results

* `jetStarCore_of_flat`: `JetStarCore g m` when all first partial derivatives of `g` vanish at `m`.
* `scalar_flat`: the scalar curvature at such a point is `2 Rnum / det²`.
-/

open Real Matrix Lightlike
open scoped ContDiff
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)} {m : Fin 3 → ℝ}

/-- The second partial derivatives `∂_l ∂_k g_ij (m)`. -/
noncomputable def ddv (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (k l i j : Fin 3) : ℝ := pd l (fun y => pd k (fun z => g z i j) y) m

/-- The second partial derivative as the second Fréchet derivative applied to basis vectors. -/
theorem ddv_eq_fderiv2 (hg : IsCoordMetric g U) (hm : m ∈ U) (k l i j : Fin 3) :
    ddv g m k l i j = fderiv ℝ (fderiv ℝ (fun y => g y i j)) m (Pi.single l 1) (Pi.single k 1) := by
  have hc : ContDiffAt ℝ 2 (fun y => g y i j) m :=
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hm)).of_le (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => g y i j)) m :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold ddv pd
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **Symmetry of mixed second partial derivatives** of a smooth metric. -/
theorem ddv_comm_kl (hg : IsCoordMetric g U) (hm : m ∈ U) (k l i j : Fin 3) :
    ddv g m k l i j = ddv g m l k i j := by
  have hc : ContDiffAt ℝ 2 (fun y => g y i j) m :=
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hm)).of_le (by norm_cast)
  have := hc.isSymmSndFDerivAt (by simp)
  rw [ddv_eq_fderiv2 hg hm, ddv_eq_fderiv2 hg hm]
  exact this _ _

/-- A coordinate metric is symmetric on a neighbourhood of every point of its domain. -/
theorem g_symm_eventually (hg : IsCoordMetric g U) (hm : m ∈ U) (i j : Fin 3) :
    (fun y => g y i j) =ᶠ[nhds m] fun y => g y j i := by
  filter_upwards [hg.isOpen.mem_nhds hm] with y hy
  have := congrFun (congrFun (hg.symm y hy) j) i
  simpa using this

/-- The partial derivatives of `g_ij` and `g_ji` agree. -/
theorem pd_symm_ij (hg : IsCoordMetric g U) (hm : m ∈ U) (k i j : Fin 3) :
    pd k (fun y => g y i j) m = pd k (fun y => g y j i) m := by
  unfold pd; rw [(g_symm_eventually hg hm i j).fderiv_eq]

/-- The second partial derivatives of `g_ij` and `g_ji` agree. -/
theorem ddv_comm_ij (hg : IsCoordMetric g U) (hm : m ∈ U) (k l i j : Fin 3) :
    ddv g m k l i j = ddv g m k l j i := by
  have hev : (fun y => pd k (fun z => g z i j) y) =ᶠ[nhds m] fun y => pd k (fun z => g z j i) y := by
    filter_upwards [hg.isOpen.mem_nhds hm] with y hy
    unfold pd
    rw [(g_symm_eventually hg hy i j).fderiv_eq]
  have h2 := hev.fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun F : (Fin 3 → ℝ) →L[ℝ] ℝ => F (Pi.single l 1)) h2

section Flat

variable (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0)
include hdg

/-- At a point with vanishing first derivatives, the first-derivative matrix `dmat` vanishes. -/
theorem dmat_flat (u : Fin 3 → ℝ) : dmat g m u = 0 := by
  ext i j; simp [dmat, hdg]

/-- At a point with vanishing first derivatives, the Christoffel symbols vanish. -/
theorem christoffel_flat (i j k : Fin 3) : christoffel g i j k m = 0 := by
  simp [christoffel, hdg]

/-- At a point with vanishing first derivatives, the Christoffel contraction vanishes. -/
theorem chr_flat (u v : Fin 3 → ℝ) : chr g m u v = 0 := by
  ext i; simp [chr, christoffel_flat hdg]

/-- At a point with vanishing first derivatives, the `ε³` part of the edge polynomial vanishes. -/
theorem edgeC_flat (s Δ : Fin 3 → ℝ) : edgeC g m s Δ = 0 := by
  simp [edgeC, dmat_flat hdg]

end Flat

/-- The Gram part of the edge polynomial is `qf`. -/
theorem edgeQ_eq_qf (Δ : Fin 3 → ℝ) : edgeQ g m Δ = qf (fun i j => g m i j) Δ := by
  simp [edgeQ, qf, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- At a point with vanishing first derivatives, the `ε⁴` part of the edge polynomial is `rf` of the second derivatives. -/
theorem edgeR_flat (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) (s Δ : Fin 3 → ℝ) :
    edgeR g m s Δ = rf (ddv g m) s Δ := by
  simp only [edgeR, chr_flat hdg, rf, ddq, ddv, ddmat, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.of_apply]
  simp
  ring

/-- The Gram squared lengths of an incidence are `lenQ` of the Gram matrix. -/
theorem incQ_eq_lenQ (σ h : Fin 6) : incQ g m σ h = lenQ (fun i j => g m i j) σ h := by
  simp only [incQ, lenQ, edgeQ_eq_qf]

/-- At a point with vanishing first derivatives, the `ε³` coefficients of the squared lengths vanish. -/
theorem incC_flat (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) (σ h : Fin 6) :
    incC g m σ h = 0 := by
  ext i
  fin_cases i <;> simp [incC, incVec, edgeC_flat hdg]

/-- At a point with vanishing first derivatives, the `ε⁴` coefficients are `lenR` of the second derivatives. -/
theorem incR_flat (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) (σ h : Fin 6) :
    incR g m σ h = lenR (ddv g m) σ h := by
  simp only [incR, lenR, edgeR_flat hdg]

/-- The first variation of the dihedral angle in the zero direction is `0`. -/
theorem Dh_zero' (L : Fin 6 → ℝ) : Dh (L, 0) = 0 := by
  have := Dh_smul L (0 : Fin 6 → ℝ) 0
  simpa using this

/-- At a point with vanishing first derivatives, the first-order coefficient of every incidence vanishes. -/
theorem angC1_flat (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) (σ h : Fin 6) :
    angC1 g m σ h = 0 := by
  simp [angC1, incC_flat hdg, Dh_zero']

/-- At a point with vanishing first derivatives, the second-order coefficient is `Dh(q, r)`. -/
theorem angC2_flat (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) (σ h : Fin 6) :
    angC2 g m σ h = Dh (incQ g m σ h, incR g m σ h) := by
  simp [angC2, incC_flat hdg]

/-- In the class of direction `w`, the squared hinge length of an incidence is `edgeQ g m w`. -/
theorem inClass_incQ_zero {w : Fin 3 → ℝ} {σ h : Fin 6} (hw : InClass w σ h) :
    incQ g m σ h 0 = edgeQ g m w := by
  have : (fun i => (kpos σ h (hQ h) i - kpos σ h (hP h) i)) = w := by
    ext i
    have := hw i
    simp only [kpos]
    linarith
  simp only [incQ, incVec, Matrix.cons_val_zero]
  rw [this]

/-- **Scalar curvature at a point with vanishing metric gradient**, in terms of the adjugate and the second derivatives: `R = 2 Rnum / det²`. -/
theorem scalar_flat (hg : IsCoordMetric g U) (hm : m ∈ U)
    (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) :
    scalarCurvature g m = 2 * Rnum (fun i j => g m i j) (ddv g m) / (g m).det ^ 2 := by
  rw [scalarCurvature_jet hg hm]
  have e : ∀ a b c d, pd a (fun y => pd b (fun z => g z c d) y) m = ddv g m b a c d :=
    fun _ _ _ _ => rfl
  have hinv : (g m)⁻¹ = ((g m).det)⁻¹ • (g m).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hof : Matrix.of (fun i j => g m i j) = g m := rfl
  simp only [dChr, christoffel_flat hdg, hdg, e, neg_zero, zero_mul, Finset.sum_const_zero, zero_add,
    mul_zero, sub_zero, add_zero, hinv, Rnum, hof, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_three]
  ring

/-- Two independent vectors have a positive Gram determinant for a positive definite `G`. -/
theorem gram2_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) {u v : Fin 3 → ℝ}
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) :
    0 < (u ⬝ᵥ (G *ᵥ u)) * (v ⬝ᵥ (G *ᵥ v)) - (u ⬝ᵥ (G *ᵥ v)) ^ 2 := by
  have hs := posDef_symm hG
  have hu : u ≠ 0 := fun e => by simpa [e] using (huv 1 0 (by simp [e])).1
  have ha := posDef_dpos hG hu
  have hsym : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
  set c := (u ⬝ᵥ (G *ᵥ v)) / (u ⬝ᵥ (G *ᵥ u)) with hc
  have hne : v - c • u ≠ 0 := by
    intro e
    have := huv (-c) 1 (by rw [neg_smul]; rw [sub_eq_zero] at e; rw [e]; simp)
    exact one_ne_zero this.2
  have hp := posDef_dpos hG hne
  have e2 : (v - c • u) ⬝ᵥ (G *ᵥ (v - c • u)) =
      ((u ⬝ᵥ (G *ᵥ u)) * (v ⬝ᵥ (G *ᵥ v)) - (u ⬝ᵥ (G *ᵥ v)) ^ 2) / (u ⬝ᵥ (G *ᵥ u)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym v u]
    rw [hc]
    field_simp
    ring
  rw [e2] at hp
  exact (div_pos_iff_of_pos_right ha).1 hp

/-- A positive Gram determinant of two independent vectors gives a nonzero value. -/
theorem face_ne {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) {u v : Fin 3 → ℝ}
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) {P : ℝ}
    (hP : P = (u ⬝ᵥ (G *ᵥ u)) * (v ⬝ᵥ (G *ᵥ v)) - (u ⬝ᵥ (G *ᵥ v)) ^ 2) : P ≠ 0 := by
  rw [hP]; exact (gram2_pos hG huv).ne'

/-- **`JetStarCore` at a point with vanishing metric gradient.** Let `g` be a Riemannian
metric on `U` and `m ∈ U` a point where all first partial derivatives of `g` vanish (for example
the centre of normal coordinates). Then the jet-level star identity `JetStarCore g m` holds, in the
chart in which `g` is given: the Gram matrix `g m` is an arbitrary positive definite matrix and the
second derivatives are arbitrary. This is not the general chart: the convergence theorem needs
the same statement at every hinge, where the first derivatives of `g` do not vanish. -/
theorem jetStarCore_of_flat (hg : IsRiemMetric g U) (hm : m ∈ U)
    (hdg : ∀ k i j, pd k (fun y => g y i j) m = 0) : JetStarCore g m where
  valid σ h := valid_incQ (hg.posDef m hm) σ h
  angle_sum k := jet_angle_sum (hg.posDef m hm) k
  first_order k := by
    have : angC1 g m = fun _ _ => 0 := by ext σ h; exact angC1_flat hdg σ h
    rw [this]; simp [clsSum]
  curvature := by
    have hP := hg.posDef m hm
    have hs := posDef_symm hP
    have hdet : 0 < (g m).det := hP.det_pos
    have hGs : ∀ i j, (fun i j => g m i j) i j = (fun i j => g m i j) j i := fun i j => by
      have := congrFun (congrFun hs j) i
      simpa using this
    have hdetne : (Matrix.of (fun i j => g m i j)).det ≠ 0 := hdet.ne'
    have hw : ∀ k, √(edgeQ g m (dirs k)) * clsSum (dirs k) (angC2 g m)
        = clsSum (dirs k) (fun σ h => √(incQ g m σ h 0) * Dh (incQ g m σ h, incR g m σ h)) := by
      intro k
      rw [clsSum, clsSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hc : InClass (dirs k) σ h
      · simp only [hc, ite_true]
        rw [inClass_incQ_zero hc, angC2_flat hdg]
      · simp [hc]
    simp only [hw]
    rw [class_partition]
    have hsum : ∀ σ h : Fin 6, √(incQ g m σ h 0) * Dh (incQ g m σ h, incR g m σ h)
        = -(Einc (lenQ (fun i j => g m i j) σ h) (lenR (ddv g m) σ h)) / √((g m).det) := by
      intro σ h
      rw [sqrt_Dh_inc hP σ h (incR g m σ h), incQ_eq_lenQ, incR_flat hdg]
      rfl
    simp only [hsum]
    simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
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
    have eng := flat_star_identity (fun i j => g m i j) (ddv g m) hGs (ddv_comm_kl hg.coord hm)
      (ddv_comm_ij hg.coord hm) (fun h => hP1 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP2 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP3 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP4 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP5 (by beta_reduce at h ⊢; linear_combination h))
      (fun h => hP6 (by beta_reduce at h ⊢; linear_combination h)) hdetne
    have hof : (Matrix.of fun i j => g m i j) = g m := rfl
    rw [eng, scalar_flat hg.coord hm hdg, hof]
    have hsd : √((g m).det) ^ 2 = (g m).det := Real.sq_sqrt hdet.le
    have hpos : 0 < √((g m).det) := Real.sqrt_pos.2 hdet
    have hd := hdet.ne'
    set R := Rnum (fun i j => g m i j) (ddv g m)
    set d := (g m).det
    set r := √d
    have : d = r ^ 2 := hsd.symm
    rw [this]
    field_simp

end Lightlike.Regge.Conv3
