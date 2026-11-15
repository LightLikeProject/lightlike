import Lightlike.SpinFoam.IntertwinerCount
import Lightlike.SU2.Su2Exp

/-!
# Rank-one projectors: the invariant of three spins

A Hermitian idempotent matrix of trace one is `u uᴴ` for a unit vector `u`
(`exists_vecMulVec_of_trace_one`). Applied to `avgP ![a, b, c]`, whose trace is the triangle
indicator (`trace_avgP_three`), the invariant space of three spins is one-dimensional when
`(a b c)` is a triad and zero otherwise.
-/

open Matrix Finset MeasureTheory Lightlike.SU2 Lightlike.Spin4
open scoped ComplexOrder

namespace Lightlike.SpinFoam

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A Hermitian idempotent with trace zero vanishes. -/
lemma eq_zero_of_trace_zero {P : Matrix ι ι ℂ} (hH : Pᴴ = P) (hP : P * P = P)
    (ht : trace P = 0) : P = 0 := by
  refine trace_conjTranspose_mul_self_eq_zero_iff.mp ?_
  rw [hH, hP, ht]

omit [DecidableEq ι] in
/-- **A Hermitian idempotent of trace one is a rank-one projector** `u uᴴ` with `uᴴ u = 1`. -/
theorem exists_vecMulVec_of_trace_one {P : Matrix ι ι ℂ} (hH : Pᴴ = P) (hP : P * P = P)
    (ht : trace P = 1) :
    ∃ u : ι → ℂ, star u ⬝ᵥ u = 1 ∧ P = vecMulVec u (star u) := by
  have hex : ∃ j, P j j ≠ 0 := by
    by_contra h
    push Not at h
    simp [trace, h] at ht
  obtain ⟨j, hj⟩ := hex
  have hjj : P j j = ∑ k, star (P k j) * P k j := by
    conv_lhs => rw [← hP]
    simp only [mul_apply]
    refine sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hH j) k
    simp only [conjTranspose_apply] at this
    rw [← this]
  have hre : (P j j).re ≠ 0 ∨ (P j j).im ≠ 0 := by
    by_contra h; push Not at h; exact hj (Complex.ext h.1 h.2)
  have hpos : 0 < (P j j).re := by
    have h1 : P j j = ((P j j).re : ℂ) := by
      have := congrFun (congrFun hH j) j
      simp only [conjTranspose_apply] at this
      exact (Complex.conj_eq_iff_re.mp this).symm
    have h2 : 0 ≤ (P j j).re := by
      rw [hjj]
      simp only [Complex.re_sum]
      exact sum_nonneg fun k _ => by
        rw [show star (P k j) * P k j = ((Complex.normSq (P k j) : ℝ) : ℂ) by
          simp [Complex.normSq_eq_conj_mul_self, mul_comm]]
        simp [Complex.normSq_nonneg]
    rcases h2.lt_or_eq with h | h
    · exact h
    · exfalso; apply hj; rw [h1, ← h]; simp
  set c : ℝ := (P j j).re with hc
  have hPjj : P j j = (c : ℂ) := by
    have := congrFun (congrFun hH j) j
    simp only [conjTranspose_apply] at this
    exact (Complex.conj_eq_iff_re.mp this).symm
  obtain ⟨u, hu⟩ : ∃ u : ι → ℂ, u = fun k => (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * P k j := ⟨_, rfl⟩
  have hsq : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  have hsqne : ((Real.sqrt c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  have huu : star u ⬝ᵥ u = 1 := by
    rw [hu]
    simp only [dotProduct, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h1 : ∀ k, (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (P k j) *
        ((((Real.sqrt c)⁻¹ : ℝ) : ℂ) * P k j) =
        (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * (star (P k j) * P k j) := by
      intro k; simp only [Complex.star_def]; ring
    simp only [h1, ← mul_sum, ← hjj, hPjj]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hpos.le,
      inv_mul_cancel₀ hpos.ne']
    simp
  have hPu : P *ᵥ u = u := by
    funext k
    rw [hu]
    simp only [mulVec, dotProduct]
    simp only [mul_left_comm _ (((Real.sqrt c)⁻¹ : ℝ) : ℂ)]
    rw [← mul_sum]
    congr 1
    have := congrFun (congrFun hP k) j
    simpa [mul_apply] using this
  set Q : Matrix ι ι ℂ := vecMulVec u (star u) with hQ
  have hQH : Qᴴ = Q := by
    ext a b; simp [hQ, vecMulVec_apply, conjTranspose_apply, mul_comm]
  have hPQ : P * Q = Q := by
    rw [hQ, Matrix.mul_vecMulVec, hPu]
  have hQP : Q * P = Q := by
    have := congrArg Matrix.conjTranspose hPQ
    rwa [conjTranspose_mul, hQH, hH] at this
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.vecMulVec_mul_vecMulVec, huu, one_smul]
  have hR : P - Q = 0 := by
    refine eq_zero_of_trace_zero (P := P - Q) ?_ ?_ ?_
    · rw [conjTranspose_sub, hH, hQH]
    · rw [sub_mul, mul_sub, mul_sub, hP, hPQ, hQP, hQQ]; abel
    · rw [trace_sub, ht, hQ, trace_vecMulVec, dotProduct_comm, huu]; simp
  exact ⟨u, huu, sub_eq_zero.mp hR⟩


/-! ## The conjugate representation is conjugate to the representation -/

variable {n : ℕ}

/-- The matrix `w = [[0, 1], [-1, 0]]` of `SU(2)`, with `conj g = w g wᴴ`. -/
def wM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The spin-`n/2` matrix of `w`. -/
noncomputable def Wm (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := spinMat n wM

/-- **Entrywise conjugation on `SU(2)`**: `conj g = w g wᴴ`. -/
lemma map_star_su2 (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ).map star = wM * g * wMᴴ := by
  obtain ⟨h11, h01, -⟩ := su2_entries g
  have e00 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    rw [h11]
  have e01 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [h01]; simp
  have e10 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    rw [h01]; simp
  have e11 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [h11]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [wM, Matrix.map_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
    simp [e00, e01, e10, e11]

/-- Entrywise conjugation of the argument conjugates the spin matrix (the embedding is real). -/
lemma spinMat_map_star (g : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin (n + 1)) :
    spinMat n (g.map star) a b = star (spinMat n g a b) := by
  have he : ∀ (s : Str n) (k : Fin (n + 1)), star (emb n s k) = emb n s k := fun s k => by
    simp only [emb_apply]; split_ifs <;> simp [star_nrm]
  simp only [spinMat, mul_apply, star_sum, star_mul', conjTranspose_apply, he, kron_apply,
    star_prod, map_apply]

/-- **Conjugate matrix elements of `D` are matrix elements of `W D Wᴴ`.** -/
lemma star_spinMat_eq (g : SU2) (a b : Fin (n + 1)) :
    star (spinMat n g a b) =
      ∑ c, ∑ d, Wm n a c * spinMat n g c d * star (Wm n b d) := by
  rw [← spinMat_map_star, map_star_su2, spinMat_mul, spinMat_mul, ← spinMat_conjTranspose]
  simp only [Wm, mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Index pairs of the edge of spin `n/2`. -/
abbrev YI (n : ℕ) := Fin (n + 1) × Fin (n + 1)

/-- **Edge expansion**: `χ_n(g h⁻¹)` as a sum of products of matrix elements of `g` and `h`
only, coupled by the matrices `W`. -/
lemma spinChar_mul_inv_expand (n : ℕ) (g h : SU2) :
    spinChar n (g * h⁻¹) = ∑ y : YI n, ∑ z : YI n,
      (Wm n y.1 y.2 * star (Wm n z.1 z.2)) * (spinMat n g y.1 z.1 * spinMat n h y.2 z.2) := by
  have h1 : spinChar n (g * h⁻¹) = ∑ a, ∑ b, spinMat n g a b * star (spinMat n h a b) := by
    unfold spinChar
    have : ((g * h⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
    rw [this, spinMat_mul, ← spinMat_conjTranspose]
    simp [trace, mul_apply, conjTranspose_apply]
  rw [h1]
  simp only [star_spinMat_eq, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun c _ => sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  ring

/-! ## The invariant of three spins -/

section Three

open Lightlike.Pentagon

/-- The invariant vector of three spins: `avgP = u uᴴ`, `u` a unit vector for a triad and `0`
otherwise. -/
theorem avgP_three_rank_one (J : Fin 3 → ℕ) :
    ∃ u : LIdx J → ℂ, avgP J = vecMulVec u (star u) ∧
      (Tri (J 0) (J 1) (J 2) → star u ⬝ᵥ u = 1) ∧ (¬ Tri (J 0) (J 1) (J 2) → u = 0) := by
  have htr : trace (avgP J) = if Tri (J 0) (J 1) (J 2) then 1 else 0 := by
    rw [← integral_prod_spinChar J]
    simpa [Fin.prod_univ_three] using integral_spinChar_three (J 0) (J 1) (J 2)
  by_cases hT : Tri (J 0) (J 1) (J 2)
  · rw [ite_eq_left hT] at htr
    obtain ⟨u, hu, hP⟩ := exists_vecMulVec_of_trace_one avgP_conjTranspose avgP_mul_avgP htr
    exact ⟨u, hP, fun _ => hu, fun h => absurd hT h⟩
  · rw [ite_eq_right hT] at htr
    refine ⟨0, ?_, fun h => absurd h hT, fun _ => rfl⟩
    rw [eq_zero_of_trace_zero avgP_conjTranspose avgP_mul_avgP htr]
    ext p q; simp

/-- Non-vacuity: `(2,2,2)` is a triad, so the invariant vector is a unit vector. -/
example : Tri 2 2 2 := by unfold Tri; decide

/-- Wrong-model control: `(1,1,1)` is not a triad, so the invariant vector vanishes. -/
example : ¬ Tri 1 1 1 := by unfold Tri; decide

end Three

/-! ## The tetrahedron as a group integral -/

section Tetra

/-- Edges of the tetrahedron: `0:01, 1:02, 2:03, 3:12, 4:13, 5:23`; tail and head vertices. -/
def tl : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- Head vertex of each edge. -/
def hd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- **The tetrahedron integrand** `∏_{i<j} χ_{j_ij}(g_i g_j⁻¹)` for the six doubled spins `s`. -/
noncomputable def tetraF (s : Fin 6 → ℕ) (g : Fin 4 → SU2) : ℂ :=
  ∏ e, spinChar (s e) (g (tl e) * (g (hd e))⁻¹)

/-- **The tetrahedron as a group integral**: `∫_{SU(2)^4} ∏_{i<j} χ_{j_ij}(g_i g_j⁻¹) dg`. -/
noncomputable def tetraInt (s : Fin 6 → ℕ) : ℂ := ∫ g, tetraF s g ∂haarE (Fin 4)

/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def ev0 : Fin 3 → Fin 6 := ![0, 1, 2]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def sd0 : Fin 3 → Bool := ![true, true, true]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def ev1 : Fin 3 → Fin 6 := ![0, 3, 4]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def sd1 : Fin 3 → Bool := ![false, true, true]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def ev2 : Fin 3 → Fin 6 := ![1, 3, 5]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def sd2 : Fin 3 → Bool := ![false, false, true]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def ev3 : Fin 3 → Fin 6 := ![2, 4, 5]
/-- Vertex data of the tetrahedron (`ev`: the three edges, `sd`: tail or head). -/
def sd3 : Fin 3 → Bool := ![false, false, false]

/-- The index of a vertex tensor read off the edge index pairs. -/
def vidx (s : Fin 6 → ℕ) (ev : Fin 3 → Fin 6) (sd : Fin 3 → Bool) (y : (e : Fin 6) → YI (s e)) :
    LIdx (fun k => s (ev k)) := fun k => if sd k then (y (ev k)).1 else (y (ev k)).2

end Tetra

section Reduction

/-- The six edge expansions multiplied out: the integrand is a sum over index pairs of every edge. -/
lemma tetraF_expand (s : Fin 6 → ℕ) (g : Fin 4 → SU2) :
    tetraF s g = ∑ y : (e : Fin 6) → YI (s e), ∑ z : (e : Fin 6) → YI (s e),
      ∏ e, ((Wm (s e) (y e).1 (y e).2 * star (Wm (s e) (z e).1 (z e).2)) *
        (spinMat (s e) (g (tl e)) (y e).1 (z e).1 * spinMat (s e) (g (hd e)) (y e).2 (z e).2)) := by
  unfold tetraF
  simp_rw [spinChar_mul_inv_expand]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]

/-- The coupling coefficient of the index pairs `y`, `z` of all edges. -/
noncomputable def cc (s : Fin 6 → ℕ) (y z : (e : Fin 6) → YI (s e)) : ℂ :=
  ∏ e, (Wm (s e) (y e).1 (y e).2 * star (Wm (s e) (z e).1 (z e).2))

/-- Entries of the diagonal action are products of spin-matrix entries. -/
lemma rhoN_entry {N : ℕ} (J : Fin N → ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (k l : LIdx J) :
    rhoN J g k l = ∏ a, spinMat (J a) g (k a) (l a) := rfl

/-- **Regrouping by vertices**: the product over the six edges of the matrix elements is the
product over the four vertices of the diagonal action on the three incident spins. -/
lemma tetra_term (s : Fin 6 → ℕ) (g : Fin 4 → SU2) (y z : (e : Fin 6) → YI (s e)) :
    ∏ e, ((Wm (s e) (y e).1 (y e).2 * star (Wm (s e) (z e).1 (z e).2)) *
        (spinMat (s e) (g (tl e)) (y e).1 (z e).1 * spinMat (s e) (g (hd e)) (y e).2 (z e).2)) =
      cc s y z *
        (rhoN (fun k => s (ev0 k)) (g 0) (vidx s ev0 sd0 y) (vidx s ev0 sd0 z) *
         rhoN (fun k => s (ev1 k)) (g 1) (vidx s ev1 sd1 y) (vidx s ev1 sd1 z) *
         rhoN (fun k => s (ev2 k)) (g 2) (vidx s ev2 sd2 y) (vidx s ev2 sd2 z) *
         rhoN (fun k => s (ev3 k)) (g 3) (vidx s ev3 sd3 y) (vidx s ev3 sd3 z)) := by
  simp only [cc, rhoN_entry, vidx, Finset.prod_mul_distrib, Fin.prod_univ_succ,
    Fin.prod_univ_zero, ev0, ev1, ev2, ev3, sd0, sd1, sd2, sd3, tl, hd]
  simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  ring

end Reduction

section Contraction

open Lightlike.Pentagon

/-- The unit vector of three spins (zero when they are not a triad). -/
noncomputable def uV (J : Fin 3 → ℕ) : LIdx J → ℂ := (avgP_three_rank_one J).choose

/-- The averaged projector of three spins is the rank-one projector onto `uV`. -/
lemma avgP_eq_uV (J : Fin 3 → ℕ) : avgP J = vecMulVec (uV J) (star (uV J)) :=
  (avgP_three_rank_one J).choose_spec.1

/-- The weight of the index pairs of all edges. -/
noncomputable def aa (s : Fin 6 → ℕ) (y : (e : Fin 6) → YI (s e)) : ℂ :=
  ∏ e, Wm (s e) (y e).1 (y e).2

/-- The tetrahedral network: the four vertex vectors contracted along the six edges by `W`. -/
noncomputable def Zt (s : Fin 6 → ℕ) : ℂ :=
  ∑ y : (e : Fin 6) → YI (s e), aa s y *
    (uV (fun k => s (ev0 k)) (vidx s ev0 sd0 y) * uV (fun k => s (ev1 k)) (vidx s ev1 sd1 y) *
     uV (fun k => s (ev2 k)) (vidx s ev2 sd2 y) * uV (fun k => s (ev3 k)) (vidx s ev3 sd3 y))

/-- The coupling coefficient factorises as `aa y * conj (aa z)`. -/
lemma cc_eq (s : Fin 6 → ℕ) (y z : (e : Fin 6) → YI (s e)) : cc s y z = aa s y * star (aa s z) := by
  simp only [cc, aa, star_prod, Finset.prod_mul_distrib]

/-- The integrand term of the tetrahedron expansion is continuous on `SU(2)^4`. -/
lemma continuous_tetra_term (s : Fin 6 → ℕ) (y z : (e : Fin 6) → YI (s e)) :
    Continuous fun g : Fin 4 → SU2 => ∏ e, ((Wm (s e) (y e).1 (y e).2 *
        star (Wm (s e) (z e).1 (z e).2)) *
        (spinMat (s e) (g (tl e)) (y e).1 (z e).1 * spinMat (s e) (g (hd e)) (y e).2 (z e).2)) := by
  refine continuous_finsetProd _ fun e _ => continuous_const.mul ?_
  exact ((continuous_spinMat_apply _ _ _).comp (continuous_apply (tl e))).mul
    ((continuous_spinMat_apply _ _ _).comp (continuous_apply (hd e)))

/-- **The tetrahedron integral is `Z · Z̄`** for the tetrahedral network `Z`. -/
theorem tetraInt_eq (s : Fin 6 → ℕ) : tetraInt s = Zt s * star (Zt s) := by
  have hint : ∀ y z : (e : Fin 6) → YI (s e), Integrable (fun g : Fin 4 → SU2 => ∏ e,
      ((Wm (s e) (y e).1 (y e).2 * star (Wm (s e) (z e).1 (z e).2)) *
        (spinMat (s e) (g (tl e)) (y e).1 (z e).1 * spinMat (s e) (g (hd e)) (y e).2 (z e).2)))
      (haarE (Fin 4)) := fun y z => integrableE_of_continuous (continuous_tetra_term s y z)
  have hvert : ∀ y z : (e : Fin 6) → YI (s e), ∫ g : Fin 4 → SU2, ∏ e,
      ((Wm (s e) (y e).1 (y e).2 * star (Wm (s e) (z e).1 (z e).2)) *
        (spinMat (s e) (g (tl e)) (y e).1 (z e).1 * spinMat (s e) (g (hd e)) (y e).2 (z e).2))
        ∂haarE (Fin 4) =
      aa s y * star (aa s z) *
        (avgP (fun k => s (ev0 k)) (vidx s ev0 sd0 y) (vidx s ev0 sd0 z) *
         avgP (fun k => s (ev1 k)) (vidx s ev1 sd1 y) (vidx s ev1 sd1 z) *
         avgP (fun k => s (ev2 k)) (vidx s ev2 sd2 y) (vidx s ev2 sd2 z) *
         avgP (fun k => s (ev3 k)) (vidx s ev3 sd3 y) (vidx s ev3 sd3 z)) := by
    intro y z
    simp_rw [tetra_term, ← cc_eq]
    rw [integral_const_mul]
    congr 1
    have key := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin 4 => haarSU2)
      (f := ![fun x : SU2 => rhoN (fun k => s (ev0 k)) (x : Matrix (Fin 2) (Fin 2) ℂ)
          (vidx s ev0 sd0 y) (vidx s ev0 sd0 z),
        fun x : SU2 => rhoN (fun k => s (ev1 k)) (x : Matrix (Fin 2) (Fin 2) ℂ)
          (vidx s ev1 sd1 y) (vidx s ev1 sd1 z),
        fun x : SU2 => rhoN (fun k => s (ev2 k)) (x : Matrix (Fin 2) (Fin 2) ℂ)
          (vidx s ev2 sd2 y) (vidx s ev2 sd2 z),
        fun x : SU2 => rhoN (fun k => s (ev3 k)) (x : Matrix (Fin 2) (Fin 2) ℂ)
          (vidx s ev3 sd3 y) (vidx s ev3 sd3 z)])
    simpa [Fin.prod_univ_succ, haarE, avgP, matInt_apply, mul_assoc] using key
  unfold tetraInt
  simp_rw [tetraF_expand]
  rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun z _ => hint y z))]
  simp_rw [integral_finsetSum _ (fun z _ => hint _ z), hvert, avgP_eq_uV, vecMulVec_apply]
  unfold Zt
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [star_mul', Pi.star_apply]
  ring

end Contraction

section WEntries

open Lightlike.SU2

/-- The string with every label flipped. -/
def flipStr (s : Str n) : Str n := fun i => 1 - s i

/-- Flipping all bits twice is the identity. -/
lemma flipStr_flipStr (s : Str n) : flipStr (flipStr s) = s := by
  funext i; simp only [flipStr]; revert i; intro i; generalize s i = x; revert x; decide

/-- Flipping all bits turns `k` downs into `n - k`. -/
lemma downs_flipStr (s : Str n) : downs (flipStr s) = n - downs s := by
  have hc : ∀ x : Fin 2, (1 - x = 1) ↔ ¬ x = 1 := by decide
  have h : univ.filter (fun i => flipStr s i = 1) = (univ.filter fun i => s i = 1)ᶜ := by
    ext i; simp only [flipStr, mem_filter, mem_univ, true_and, mem_compl, hc]
  unfold downs; rw [h, card_compl, Fintype.card_fin]

/-- Complementary classes have the same cardinality. -/
lemma clsCard_flip {a : ℕ} (ha : a ≤ n) : clsCard n (n - a) = clsCard n a := by
  unfold clsCard cls
  refine card_bij (fun s _ => flipStr s) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    rw [downs_flipStr, hs]; omega
  · intro s _ t _ h
    rw [← flipStr_flipStr s, h, flipStr_flipStr]
  · intro t ht
    refine ⟨flipStr t, ?_, flipStr_flipStr t⟩
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    rw [downs_flipStr, ht]

/-- The entries of `wM` on the antidiagonal. -/
lemma wM_flip (x : Fin 2) : wM x (1 - x) = if x = 1 then (-1 : ℂ) else 1 := by
  fin_cases x <;> simp [wM]

/-- `wM` vanishes off the antidiagonal. -/
lemma wM_zero (x y : Fin 2) (h : y ≠ 1 - x) : wM x y = 0 := by
  fin_cases x <;> fin_cases y <;> simp_all [wM]

/-- The Kronecker power of `wM` as a signed permutation of bit strings. -/
lemma kron_wM (s t : Str n) :
    kron n wM s t = if t = flipStr s then (-1 : ℂ) ^ downs s else 0 := by
  rw [kron_apply]
  split_ifs with h
  · subst h
    simp only [flipStr, wM_flip, prod_ite, prod_const, downs, one_pow, mul_one]
  · obtain ⟨i, hi⟩ : ∃ i, t i ≠ flipStr s i :=
      by_contra fun hc => h (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
    exact prod_eq_zero (mem_univ i) (wM_zero _ _ hi)

/-- **The spin matrix of `w`**: `W_{a c} = (-1)^a` for `c = n - a` and `0` otherwise. -/
lemma Wm_apply (a c : Fin (n + 1)) :
    Wm n a c = if (c : ℕ) = n - a then (-1 : ℂ) ^ (a : ℕ) else 0 := by
  have hin : ∀ s : Str n, ∑ t, kron n wM s t * emb n t c =
      (-1 : ℂ) ^ downs s * (if n - downs s = (c : ℕ) then nrm n c else 0) := by
    intro s
    rw [sum_eq_single (flipStr s)]
    · rw [kron_wM, ite_eq_left rfl, emb_apply, downs_flipStr]
    · intro t _ ht; rw [kron_wM, ite_eq_right ht, zero_mul]
    · intro h; exact absurd (mem_univ _) h
  have h1 : Wm n a c = ∑ s : Str n, star (emb n s a) * ((-1 : ℂ) ^ downs s *
      (if n - downs s = (c : ℕ) then nrm n c else 0)) := by
    unfold Wm spinMat
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine sum_congr rfl fun s _ => ?_
    rw [conjTranspose_apply, Matrix.mul_apply, ← hin]
  have h2 : ∀ s : Str n, star (emb n s a) * ((-1 : ℂ) ^ downs s *
      (if n - downs s = (c : ℕ) then nrm n c else 0)) =
      if downs s = (a : ℕ) then
        nrm n a * ((-1 : ℂ) ^ (a : ℕ) * (if n - (a : ℕ) = (c : ℕ) then nrm n c else 0)) else 0 := by
    intro s
    rw [emb_apply]
    by_cases h : downs s = (a : ℕ)
    · simp [h, star_nrm]
    · simp [h]
  rw [h1, sum_congr rfl fun s _ => h2 s, ← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : #(univ.filter fun s : Str n => downs s = (a : ℕ)) = clsCard n a := rfl
  have ha : (a : ℕ) ≤ n := Nat.lt_succ_iff.mp a.2
  rw [hcard]
  by_cases h : (c : ℕ) = n - a
  · have h' : n - (a : ℕ) = (c : ℕ) := h.symm
    have hn : nrm n c = nrm n a := by
      have : nrm n (c : ℕ) = nrm n (n - a) := by rw [h]
      rw [this]; unfold nrm; rw [clsCard_flip ha]
    rw [ite_eq_left h, ite_eq_left h', hn]
    linear_combination ((-1 : ℂ) ^ (a : ℕ)) * nrm_mul_nrm ha
  · have h' : ¬ n - (a : ℕ) = (c : ℕ) := fun e => h e.symm
    rw [ite_eq_right h, ite_eq_right h']; simp

end WEntries

end Lightlike.SpinFoam
