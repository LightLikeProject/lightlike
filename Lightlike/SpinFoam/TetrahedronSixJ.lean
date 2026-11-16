import Lightlike.SpinFoam.Tetrahedron
import Lightlike.Spin4.Intertwiner4
import Lightlike.Spin4.CoherentTwoValent

open Matrix Finset MeasureTheory Lightlike.SU2 Lightlike.Spin4 Lightlike.Pentagon
open PhyslibAlpha.Sl2
open scoped Kronecker

/-!
# The tetrahedron integral is the square of a 6j symbol

The integral over `SU(2)^4` of the six characters of a tetrahedron (`tetraInt`) is the square of a 6j
symbol. The proof builds the invariant vector `svec J` of the three spins of a triad from the coupling
matrix `Smat` and the singlet matrix `Wm`, shows that it is invariant and of norm one, and identifies
it with the 3j vector `tV J` up to a phase (`uV_eq_phase_tV`); the four triads of the tetrahedron then
give the sum of products of 3j symbols that defines the 6j symbol.

## Main results

* `Wm_eq_rev`, `spinMat_mul_Wm_mul_transpose`: the singlet matrix has one entry per row and is invariant.
* `svec_invariant`, `svec_norm`: the invariant vector of a triad is invariant and has norm one.
* `uV_eq_phase_tV`, `tV_invariant`, `tV_norm`: the 3j vector spans the same line.
* `Zt_eq_phase_ZR`, `ZR_eq`: the tetrahedron value is a phase times a signed 6j symbol.
* `tetraInt_eq_sixJ_sq`: the tetrahedron integral is the square of the 6j symbol of the six spins.
-/

namespace Lightlike.SpinFoam

variable {n : ℕ}

/-- `W` has a single nonzero entry per row, in the reversed column. -/
lemma Wm_eq_rev (a c : Fin (n + 1)) :
    Wm n a c = if c = Fin.rev a then (-1 : ℂ) ^ (a : ℕ) else 0 := by
  have : ((c : ℕ) = n - a) ↔ c = Fin.rev a := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  rw [Wm_apply]; simp only [this]

/-- The singlet is invariant: `D W Dᵀ = W`. -/
lemma spinMat_mul_Wm_mul_transpose (g : SU2) :
    spinMat n g * Wm n * (spinMat n g)ᵀ = Wm n := by
  have h := cgz_equivariant (n := n) (m := n) (z := 0) (by unfold Tri; omega) g
  ext a b
  have h' := congrFun (congrFun h (a, b)) 0
  simp only [Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, cgz_singlet_apply,
    spinMat_zero', Matrix.one_apply] at h'
  have hsq : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have hf : ∀ x : Fin (n + 1), ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * (((-1 : ℝ) ^ (x : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) = (-1 : ℂ) ^ (x : ℕ) := by
    intro x
    rw [← Complex.ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_pos.mpr (by positivity)).ne']
    push_cast; rfl
  have hR : (∑ j : Fin (0 + 1), cgz n n 0 (a, b) j * if j = 0 then (1 : ℂ) else 0) =
      cgz n n 0 (a, b) 0 := by simp
  rw [hR, cgz_singlet_apply] at h'
  have hL : ∀ x : Fin (n + 1), (∑ y : Fin (n + 1), spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) a x *
      spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) b y * (if (x : ℕ) + y = n then (((-1 : ℝ) ^ (x : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) else 0)) =
      spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) a x * spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) b
        (Fin.rev x) * (((-1 : ℝ) ^ (x : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) := by
    intro x
    rw [sum_eq_single (Fin.rev x)]
    · rw [ite_eq_left (by simp only [Fin.val_rev]; omega)]
    · intro y _ hy
      rw [ite_eq_right (fun e => hy (by rw [Fin.ext_iff, Fin.val_rev]; omega)), mul_zero]
    · intro hx; exact absurd (mem_univ _) hx
  simp only [hL] at h'
  have hLHS : (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * Wm n *
      (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ))ᵀ) a b =
      ∑ x : Fin (n + 1), spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) a x *
        spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) b (Fin.rev x) * (-1 : ℂ) ^ (x : ℕ) := by
    simp only [Matrix.mul_apply, transpose_apply, Wm_eq_rev, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_eq_single (Fin.rev x)]
    · simp [mul_assoc, mul_comm]
    · intro y _ hy
      rw [ite_eq_right (fun e => hy (by rw [e])), mul_zero, zero_mul]
    · intro hx; exact absurd (mem_univ _) hx
  rw [hLHS, Wm_eq_rev]
  have hmul := congrArg (fun z => ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * z) h'
  simp only [Finset.mul_sum] at hmul
  have hcond : ((a : ℕ) + b = n) ↔ b = Fin.rev a := by rw [Fin.ext_iff, Fin.val_rev]; omega
  calc _ = ∑ x : Fin (n + 1), ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) *
        (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) a x *
          spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) b (Fin.rev x) * (((-1 : ℝ) ^ (x : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) :=
        sum_congr rfl fun x _ => by rw [← hf x]; ring
    _ = _ := hmul
    _ = _ := by
      by_cases hc : (a : ℕ) + b = n
      · rw [ite_eq_left hc, ite_eq_left (hcond.mp hc), hf a]
      · rw [ite_eq_right hc, ite_eq_right (fun e => hc (hcond.mpr e)), mul_zero]

/-! ## The invariant vector of a triad -/

/-- Splitting the three labels of a triple of spins into a pair and a single label. -/
def lidxEquiv (J : Fin 3 → ℕ) : LIdx J ≃ Idx (J 0) (J 1) × Fin (J 2 + 1) where
  toFun k := ((k 0, k 1), k 2)
  invFun x := fun i => match i with
    | ⟨0, _⟩ => x.1.1
    | ⟨1, _⟩ => x.1.2
    | ⟨2, _⟩ => x.2
    | ⟨k + 3, h⟩ => absurd h (by omega)
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv x := rfl

/-- The coupling matrix with its last index flipped by `W`. -/
noncomputable def Smat (J : Fin 3 → ℕ) : Matrix (Idx (J 0) (J 1)) (Fin (J 2 + 1)) ℂ :=
  cgz (J 0) (J 1) (J 2) * Wm (J 2)

/-- The vector of an invariant of three spins, built from the coupling matrix. -/
noncomputable def svec (J : Fin 3 → ℕ) : LIdx J → ℂ := fun k => Smat J (k 0, k 1) (k 2)

/-- The matrix `Smat` intertwines the three spin representations. -/
lemma Smat_equivariant {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) (g : SU2) :
    (spinMat (J 0) g ⊗ₖ spinMat (J 1) g) * Smat J * (spinMat (J 2) g)ᵀ = Smat J := by
  have hW := spinMat_mul_Wm_mul_transpose (n := J 2) g
  unfold Smat
  calc _ = (cgz (J 0) (J 1) (J 2) * spinMat (J 2) g) * Wm (J 2) * (spinMat (J 2) g)ᵀ := by
        rw [← Matrix.mul_assoc (spinMat (J 0) g ⊗ₖ spinMat (J 1) g), cgz_equivariant h g]
    _ = cgz (J 0) (J 1) (J 2) * (spinMat (J 2) g * Wm (J 2) * (spinMat (J 2) g)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW]

/-- **The vector `svec` is invariant under the group.** -/
theorem svec_invariant {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) : IsInvariantN J (svec J) := by
  intro g
  funext k
  have hk := congrFun (congrFun (Smat_equivariant h g) (k 0, k 1)) (k 2)
  simp only [Matrix.mul_apply, transpose_apply, kroneckerMap_apply, Fintype.sum_prod_type] at hk
  simp only [Matrix.mulVec, dotProduct]
  rw [← (lidxEquiv J).symm.sum_comp]
  show _ = Smat J (k 0, k 1) (k 2)
  rw [← hk]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun j _ => ?_
  simp only [rhoN_entry, Fin.prod_univ_three, svec]
  have e0 : ((lidxEquiv J).symm ((x, y), j)) 0 = x := rfl
  have e1 : ((lidxEquiv J).symm ((x, y), j)) 1 = y := rfl
  have e2 : ((lidxEquiv J).symm ((x, y), j)) 2 = j := rfl
  rw [e0, e1, e2]
  show _ * Smat J (x, y) j = _
  ring


/-- `W` is unitary: `Wᴴ W = 1`. -/
lemma Wm_conjTranspose_mul : (Wm n)ᴴ * Wm n = 1 := by
  unfold Wm
  rw [spinMat_conjTranspose, ← spinMat_mul]
  have : wMᴴ * wM = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, spinMat_one]

/-- `Smat` is an isometry onto its image: `Sᴴ S = 1` for a triad. -/
lemma Smat_isometry {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) : (Smat J)ᴴ * Smat J = 1 := by
  unfold Smat
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cgz (J 0) (J 1) (J 2))ᴴ,
    cgz_isometry h, Matrix.one_mul, Wm_conjTranspose_mul]

/-- **The norm of `svec`**: `‖svec‖² = J₂ + 1`. -/
lemma svec_norm {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) :
    star (svec J) ⬝ᵥ svec J = ((J 2 + 1 : ℕ) : ℂ) := by
  have hS := Smat_isometry h
  have : star (svec J) ⬝ᵥ svec J =
      ∑ c : Fin (J 2 + 1), ∑ p : Idx (J 0) (J 1), star (Smat J p c) * Smat J p c := by
    simp only [dotProduct]
    rw [← (lidxEquiv J).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [this]
  have hd : ∀ c : Fin (J 2 + 1), ∑ p : Idx (J 0) (J 1), star (Smat J p c) * Smat J p c = 1 := by
    intro c
    have := congrFun (congrFun hS c) c
    simpa [Matrix.mul_apply, conjTranspose_apply] using this
  rw [Finset.sum_congr rfl fun c _ => hd c]
  simp

/-- A unit vector fixed by a rank-one projector `u uᴴ` is a phase times `u`. -/
lemma eq_phase_of_rank_one {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    {u t : ι → ℂ} (hP : P = vecMulVec u (star u)) (hu : star u ⬝ᵥ u = 1) (ht : P *ᵥ t = t)
    (htn : star t ⬝ᵥ t = 1) : ∃ c : ℂ, star c * c = 1 ∧ u = c • t := by
  obtain ⟨c, hc⟩ : ∃ c, c = star u ⬝ᵥ t := ⟨_, rfl⟩
  have h1 : t = c • u := by
    funext i
    rw [← ht, hP]
    simp only [Matrix.mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc]
    simp only [dotProduct, Pi.star_apply, Finset.sum_mul]
    exact sum_congr rfl fun j _ => by ring
  have h2 : star c * c = 1 := by
    have : star t ⬝ᵥ t = star c * c * (star u ⬝ᵥ u) := by
      conv_lhs => rw [h1]
      simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
      refine sum_congr rfl fun i _ => by ring
    rw [htn, hu, mul_one] at this
    exact this.symm
  refine ⟨star c, by rw [star_star, mul_comm]; exact h2, ?_⟩
  funext i
  conv_rhs => rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(u i)) * h2

/-- The 3j vector of three spins in doubled units: `(J₀ J₁ J₂; J₀ - 2k₀, J₁ - 2k₁, J₂ - 2k₂)`. -/
noncomputable def tV (J : Fin 3 → ℕ) (k : LIdx J) : ℂ :=
  ((threeJ (J 0) (J 1) (J 2) ((J 0 : ℤ) - 2 * ((k 0 : Fin (J 0 + 1)) : ℕ))
    ((J 1 : ℤ) - 2 * ((k 1 : Fin (J 1 + 1)) : ℕ)) ((J 2 : ℤ) - 2 * ((k 2 : Fin (J 2 + 1)) : ℕ)) : ℝ) : ℂ)

/-- `svec` is a constant sign times `√(J₂+1)` times the 3j vector. -/
lemma svec_eq {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) (k : LIdx J) :
    svec J k = (((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) * Real.sqrt ((J 2 + 1 : ℕ) : ℝ) : ℝ) : ℂ)
      * tV J k := by
  unfold svec Smat tV
  simp only [Matrix.mul_apply, Wm_eq_rev]
  rw [Finset.sum_eq_single (Fin.rev (k 2))]
  · rw [cgz_eq_threeJ h]
    have hl : ((Fin.rev (k 2) : Fin (J 2 + 1)) : ℕ) = J 2 - (k 2 : ℕ) := by
      rw [Fin.val_rev]; omega
    have hk := (k 2).isLt
    have hm : -((J 2 : ℤ) - 2 * ((Fin.rev (k 2) : Fin (J 2 + 1)) : ℕ)) = (J 2 : ℤ) - 2 * (k 2 : ℕ) := by
      rw [hl]; omega
    rw [hm, ite_eq_left_iff.mpr (fun hne => absurd (Fin.rev_rev _).symm hne), hl]
    push_cast
    have : ((-1 : ℂ)) ^ (J 2 - (k 2 : ℕ)) * (-1 : ℂ) ^ (J 2 - (k 2 : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [pow_add]
    linear_combination ((-1 : ℂ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) * ↑√(↑(J 2) + 1) *
      ↑(threeJ (J 0) (J 1) (J 2) ((J 0 : ℤ) - 2 * ((k 0 : Fin (J 0 + 1)) : ℕ))
        ((J 1 : ℤ) - 2 * ((k 1 : Fin (J 1 + 1)) : ℕ)) ((J 2 : ℤ) - 2 * ((k 2 : Fin (J 2 + 1)) : ℕ)))) * this
  · intro c _ hc
    rw [ite_eq_right_iff.mpr (fun h' => absurd (by rw [h', Fin.rev_rev]) hc), mul_zero]
  · simp

/-- The 3j vector vanishes unless the three spins form a triad. -/
lemma tV_eq_zero {J : Fin 3 → ℕ} (h : ¬ Tri (J 0) (J 1) (J 2)) : tV J = 0 := by
  funext k
  unfold tV
  rw [threeJ_of_not]
  · simp
  · intro hA
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := hA
    exact h ⟨h4, h1, h2, h3⟩

/-- The 3j vector is invariant and has unit norm for a triad. -/
lemma tV_invariant {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) : IsInvariantN J (tV J) := by
  have ha : ((((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) * Real.sqrt ((J 2 + 1 : ℕ) : ℝ) : ℝ) : ℂ))
      ≠ 0 := by
    have : (Real.sqrt ((J 2 + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    simpa using this
  set a : ℂ := (((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) * Real.sqrt ((J 2 + 1 : ℕ) : ℝ) : ℝ) : ℂ)
  have e : tV J = a⁻¹ • svec J := by
    funext k; simp only [Pi.smul_apply, smul_eq_mul, svec_eq h, a]
    field_simp
  intro g
  rw [e, Matrix.mulVec_smul, svec_invariant h g]

/-- The 3j vector of a triad has unit norm. -/
lemma tV_norm {J : Fin 3 → ℕ} (h : Tri (J 0) (J 1) (J 2)) : star (tV J) ⬝ᵥ tV J = 1 := by
  have hn := svec_norm h
  have hs : star (svec J) ⬝ᵥ svec J = (((J 2 + 1 : ℕ) : ℝ) : ℂ) * (star (tV J) ⬝ᵥ tV J) := by
    simp only [dotProduct, Finset.mul_sum, svec_eq h, Pi.star_apply]
    refine sum_congr rfl fun k _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    have : ((Real.sqrt ((J 2 + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (Real.sqrt ((J 2 + 1 : ℕ) : ℝ) : ℂ) =
        (((J 2 + 1 : ℕ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    have hs1 : ((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2)) * ((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hs2 : ((((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) : ℝ)) : ℂ) *
        ((((-1 : ℝ) ^ (J 0 + (J 0 + J 1 - J 2) / 2) : ℝ)) : ℂ) = 1 := by
      exact_mod_cast hs1
    push_cast at this hs2 ⊢
    linear_combination ((starRingEnd ℂ) (tV J k) * tV J k * ((Real.sqrt ((J 2 : ℝ) + 1) : ℝ) : ℂ) ^ 2) * hs2
      + ((starRingEnd ℂ) (tV J k) * tV J k) * this
  rw [hn] at hs
  have hne : (((J 2 + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (J 2)
  have : (((J 2 + 1 : ℕ) : ℝ) : ℂ) * 1 = (((J 2 + 1 : ℕ) : ℝ) : ℂ) * (star (tV J) ⬝ᵥ tV J) := by
    rw [mul_one, ← hs]; push_cast; ring
  exact (mul_left_cancel₀ hne this).symm

/-- **The vertex vector is the 3j vector up to a phase**: `uV J = c • tV J` with `|c| = 1`. -/
theorem uV_eq_phase_tV (J : Fin 3 → ℕ) : ∃ c : ℂ, star c * c = 1 ∧ uV J = c • tV J := by
  by_cases h : Tri (J 0) (J 1) (J 2)
  · have hu := (avgP_three_rank_one J).choose_spec.2.1 h
    exact eq_phase_of_rank_one (avgP_eq_uV J) hu (avgP_mulVec_of_invariant (tV_invariant h))
      (tV_norm h)
  · refine ⟨1, by simp, ?_⟩
    rw [tV_eq_zero h]
    have h0 : uV J = 0 := (avgP_three_rank_one J).choose_spec.2.2 h
    simp [h0]

section Collapse

variable (s : Fin 6 → ℕ)

/-- The index pairs `(a, n - a)` of the six edges that carry the weight `W`. -/
def yOf (a : (e : Fin 6) → Fin (s e + 1)) : (e : Fin 6) → YI (s e) := fun e => (a e, Fin.rev (a e))

/-- The map `yOf` is injective. -/
lemma yOf_injective : Function.Injective (yOf s) := by
  intro a b h
  funext e
  exact congrArg (fun y => (y e).1) h

/-- The weight of `yOf a` is `(-1)^(Σ aₑ)`. -/
lemma aa_yOf (a : (e : Fin 6) → Fin (s e + 1)) :
    aa s (yOf s a) = (-1 : ℂ) ^ (∑ e, (a e : ℕ)) := by
  simp only [aa, yOf, Wm_eq_rev, ite_true]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- The weight vanishes off the image of `yOf`. -/
lemma aa_eq_zero_of_not_mem (y : (e : Fin 6) → YI (s e))
    (hy : y ∉ Finset.univ.image (yOf s)) : aa s y = 0 := by
  by_contra hne
  apply hy
  rw [Finset.mem_image]
  refine ⟨fun e => (y e).1, Finset.mem_univ _, ?_⟩
  funext e
  have h1 : Wm (s e) (y e).1 (y e).2 ≠ 0 := (Finset.prod_ne_zero_iff.mp hne) e (Finset.mem_univ e)
  rw [Wm_eq_rev] at h1
  have h2 : (y e).2 = Fin.rev (y e).1 := by
    by_contra h3; exact h1 (by rw [ite_eq_right_iff.mpr (fun h => absurd h h3)])
  exact Prod.ext rfl h2.symm

/-- The sum over index pairs of all edges collapses to the sum over one index per edge. -/
lemma sum_yOf {M : Type*} [AddCommMonoid M] (f : ((e : Fin 6) → YI (s e)) → M)
    (hf : ∀ y, y ∉ Finset.univ.image (yOf s) → f y = 0) :
    ∑ y, f y = ∑ a : (e : Fin 6) → Fin (s e + 1), f (yOf s a) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (yOf s)))
    (fun y _ hy => hf y hy), Finset.sum_image (fun a _ b _ h => yOf_injective s h)]

end Collapse

section Vertices

variable (s : Fin 6 → ℕ)

/-- The doubled projection of edge `e` for the index `a`: `s e - 2 a e`. -/
def pr (a : (e : Fin 6) → Fin (s e + 1)) (e : Fin 6) : ℤ := (s e : ℤ) - 2 * ((a e : Fin (s e + 1)) : ℕ)

/-- The 3j vector at vertex 0 evaluated at `yOf a`. -/
lemma tV_v0 (a : (e : Fin 6) → Fin (s e + 1)) :
    tV (fun k => s (ev0 k)) (vidx s ev0 sd0 (yOf s a)) =
      ((threeJ (s 0) (s 1) (s 2) (pr s a 0) (pr s a 1) (pr s a 2) : ℝ) : ℂ) := by
  unfold tV vidx yOf pr
  simp [ev0, sd0]

/-- The 3j vector at vertex 1 evaluated at `yOf a`. -/
lemma tV_v1 (a : (e : Fin 6) → Fin (s e + 1)) :
    tV (fun k => s (ev1 k)) (vidx s ev1 sd1 (yOf s a)) =
      ((threeJ (s 0) (s 3) (s 4) (-pr s a 0) (pr s a 3) (pr s a 4) : ℝ) : ℂ) := by
  unfold tV vidx yOf pr
  simp [ev1, sd1, Fin.val_rev]
  have h0 := (a 0).isLt
  congr 1; omega

/-- The 3j vector at vertex 2 evaluated at `yOf a`. -/
lemma tV_v2 (a : (e : Fin 6) → Fin (s e + 1)) :
    tV (fun k => s (ev2 k)) (vidx s ev2 sd2 (yOf s a)) =
      ((threeJ (s 1) (s 3) (s 5) (-pr s a 1) (-pr s a 3) (pr s a 5) : ℝ) : ℂ) := by
  unfold tV vidx yOf pr
  simp [ev2, sd2, Fin.val_rev]
  have h0 := (a 1).isLt
  have h1 := (a 3).isLt
  congr 1 <;> omega

/-- The 3j vector at vertex 3 evaluated at `yOf a`. -/
lemma tV_v3 (a : (e : Fin 6) → Fin (s e + 1)) :
    tV (fun k => s (ev3 k)) (vidx s ev3 sd3 (yOf s a)) =
      ((threeJ (s 2) (s 4) (s 5) (-pr s a 2) (-pr s a 4) (-pr s a 5) : ℝ) : ℂ) := by
  unfold tV vidx yOf pr
  simp [ev3, sd3, Fin.val_rev]
  have h0 := (a 2).isLt
  have h1 := (a 4).isLt
  have h2 := (a 5).isLt
  congr 1 <;> omega

/-- The real number `Z'`: the tetrahedral network with the vertex vectors replaced by 3j vectors. -/
noncomputable def ZR : ℝ :=
  ∑ a : (e : Fin 6) → Fin (s e + 1), (-1 : ℝ) ^ (∑ e, (a e : ℕ)) *
    (threeJ (s 0) (s 1) (s 2) (pr s a 0) (pr s a 1) (pr s a 2) *
     threeJ (s 0) (s 3) (s 4) (-pr s a 0) (pr s a 3) (pr s a 4) *
     threeJ (s 1) (s 3) (s 5) (-pr s a 1) (-pr s a 3) (pr s a 5) *
     threeJ (s 2) (s 4) (s 5) (-pr s a 2) (-pr s a 4) (-pr s a 5))

/-- **`Zt` is a phase times the real network `ZR`.** -/
theorem Zt_eq_phase_ZR : ∃ c : ℂ, star c * c = 1 ∧ Zt s = c * (ZR s : ℂ) := by
  obtain ⟨c0, h0, e0⟩ := uV_eq_phase_tV (fun k => s (ev0 k))
  obtain ⟨c1, h1, e1⟩ := uV_eq_phase_tV (fun k => s (ev1 k))
  obtain ⟨c2, h2, e2⟩ := uV_eq_phase_tV (fun k => s (ev2 k))
  obtain ⟨c3, h3, e3⟩ := uV_eq_phase_tV (fun k => s (ev3 k))
  refine ⟨c0 * c1 * c2 * c3, ?_, ?_⟩
  · simp only [star_mul']
    calc _ = (star c0 * c0) * (star c1 * c1) * (star c2 * c2) * (star c3 * c3) := by ring
      _ = 1 := by rw [h0, h1, h2, h3]; ring
  · have hu : ∀ (J : Fin 3 → ℕ) (c : ℂ), uV J = c • tV J → ∀ k, uV J k = c * tV J k := by
      intro J c h k; rw [h]; rfl
    unfold Zt
    rw [sum_yOf s _ (fun y hy => by rw [aa_eq_zero_of_not_mem s y hy, zero_mul])]
    unfold ZR
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hu _ c0 e0, hu _ c1 e1, hu _ c2 e2, hu _ c3 e3, aa_yOf, tV_v0, tV_v1, tV_v2, tV_v3]
    ring

end Vertices

section SixJ

variable (s : Fin 6 → ℕ)

/-- Exchange of the first and last columns. -/
lemma threeJ_swap₁₃ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₃ j₂ j₁ m₃ m₂ m₁ = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [threeJ_cycle j₁ j₃ j₂ m₁ m₃ m₂, threeJ_swap₂₃]

/-- The projections of the six edges in the arrangement of Physlib's `sixJTerm` for the
spins `(s₀, s₁, s₂, s₅, s₄, s₃)`. -/
def kap (a : (e : Fin 6) → Fin (s e + 1)) : Fin 6 → ℤ :=
  ![-pr s a 0, -pr s a 1, -pr s a 2, pr s a 5, -pr s a 4, pr s a 3]

/-- The sign relating `sixJTerm` at `kap a` to the summand of `ZR`. -/
noncomputable def epsS : ℝ :=
  (-1) ^ (s 0 + s 1 + s 2 + s 4 + (s 0 + s 3 + s 4) / 2 + (s 2 + s 4 + s 5) / 2)

/-- `epsS` squares to `1`. -/
lemma epsS_mul_self : epsS s * epsS s = 1 := by
  unfold epsS; rw [← pow_add, ← two_mul, pow_mul]; simp

/-- The summand of `sixJSym` at `kap a` is `epsS` times the summand of `ZR`. -/
lemma sixJTerm_kap (a : (e : Fin 6) → Fin (s e + 1)) :
    sixJTerm (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) (kap s a) = epsS s *
      ((-1 : ℝ) ^ (∑ e, (a e : ℕ)) *
    (threeJ (s 0) (s 1) (s 2) (pr s a 0) (pr s a 1) (pr s a 2) *
     threeJ (s 0) (s 3) (s 4) (-pr s a 0) (pr s a 3) (pr s a 4) *
     threeJ (s 1) (s 3) (s 5) (-pr s a 1) (-pr s a 3) (pr s a 5) *
     threeJ (s 2) (s 4) (s 5) (-pr s a 2) (-pr s a 4) (-pr s a 5))) := by
  have hq : ((s 0 : ℤ) - kap s a 0 + ((s 1 : ℤ) - kap s a 1) + ((s 2 : ℤ) - kap s a 2) +
      ((s 5 : ℤ) - kap s a 3) + ((s 4 : ℤ) - kap s a 4) + ((s 3 : ℤ) - kap s a 5)) / 2 =
      ((s 0 + s 1 + s 2 + s 4 + ∑ e, (a e : ℕ) : ℕ) : ℤ) - 2 * ((a 0 : ℕ) + (a 1 : ℕ) + (a 2 : ℕ) + (a 4 : ℕ)) := by
    have hs : ∑ e, (a e : ℕ) = (a 0 : ℕ) + (a 1 : ℕ) + (a 2 : ℕ) + (a 3 : ℕ) + (a 4 : ℕ) + (a 5 : ℕ) := by
      simp [Fin.sum_univ_succ]; ring
    rw [hs]
    simp only [kap, pr, Matrix.cons_val]
    omega
  unfold sixJTerm
  rw [hq]
  have hz : (-1 : ℝ) ^ (((s 0 + s 1 + s 2 + s 4 + ∑ e, (a e : ℕ) : ℕ) : ℤ) -
      2 * ((a 0 : ℕ) + (a 1 : ℕ) + (a 2 : ℕ) + (a 4 : ℕ) : ℤ)) =
      (-1 : ℝ) ^ (s 0 + s 1 + s 2 + s 4) * (-1 : ℝ) ^ (∑ e, (a e : ℕ)) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, _root_.zpow_mul]
    simp [pow_add]
  rw [hz]
  simp only [kap, Matrix.cons_val, neg_neg]
  rw [threeJ_swap₂₃ (s 0) (s 3) (s 4) (-pr s a 0) (pr s a 3) (pr s a 4),
    ← threeJ_cycle (s 5) (s 1) (s 3) (pr s a 5) (-pr s a 1) (-pr s a 3),
    threeJ_swap₁₃ (s 2) (s 4) (s 5) (-pr s a 2) (-pr s a 4) (-pr s a 5)]
  unfold epsS
  simp only [pow_add]
  ring

/-- The map `kap` is injective. -/
lemma kap_injective : Function.Injective (kap s) := by
  intro a b h
  funext e
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp only [kap, pr, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
  fin_cases e <;> apply Fin.ext <;> simp <;> omega

/-- `kap a` lies in the projection box of `sixJSym`. -/
lemma kap_mem_box (a : (e : Fin 6) → Fin (s e + 1)) :
    kap s a ∈ sixJBox (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) := by
  rw [mem_sixJBox]
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  have h4 := (a 4).isLt
  have h5 := (a 5).isLt
  simp only [kap, pr, Matrix.cons_val]
  omega

/-- Summands of `sixJSym` outside the image of `kap` vanish (parity). -/
lemma sixJTerm_eq_zero_of_not_image (m : Fin 6 → ℤ)
    (hm : m ∈ sixJBox (s 0) (s 1) (s 2) (s 5) (s 4) (s 3))
    (hn : m ∉ Finset.univ.image (kap s)) :
    sixJTerm (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) m = 0 := by
  by_contra hne
  apply hn
  rw [mem_sixJBox] at hm
  have hne' : threeJ (s 0) (s 1) (s 2) (-m 0) (-m 1) (-m 2) ≠ 0 ∧
      threeJ (s 0) (s 4) (s 3) (m 0) (-m 4) (m 5) ≠ 0 ∧
      threeJ (s 5) (s 1) (s 3) (m 3) (m 1) (-m 5) ≠ 0 ∧
      threeJ (s 5) (s 4) (s 2) (-m 3) (m 4) (m 2) ≠ 0 := by
    unfold sixJTerm at hne
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> apply hne <;> rw [h] <;> ring
  obtain ⟨n1, n2, n3, n4⟩ := hne'
  have A1 := adm3_of_threeJ_ne_zero n1
  have A2 := adm3_of_threeJ_ne_zero n2
  have A3 := adm3_of_threeJ_ne_zero n3
  have A4 := adm3_of_threeJ_ne_zero n4
  obtain ⟨-, -, -, -, -, -, -, q0, q1, q2, -⟩ := A1
  obtain ⟨-, -, -, -, -, -, -, -, q4, q5, -⟩ := A2
  obtain ⟨-, -, -, -, -, -, -, q3, -, -, -⟩ := A3
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hm
  rw [Finset.mem_image]
  refine ⟨fun e => ⟨((s e : ℤ) - (match e with
      | 0 => -m 0 | 1 => -m 1 | 2 => -m 2 | 3 => m 5 | 4 => -m 4 | 5 => m 3) ) / 2 |>.toNat, ?_⟩,
    Finset.mem_univ _, ?_⟩
  · fin_cases e <;> simp <;> omega
  · funext e
    fin_cases e <;> simp [kap, pr] <;> omega

/-- The sum of `sixJTerm` over `kap a` is the 6j symbol. -/
lemma sum_sixJTerm_kap :
    ∑ a : (e : Fin 6) → Fin (s e + 1), sixJTerm (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) (kap s a) =
      sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) := by
  rw [sixJSym, ← Finset.sum_image (f := sixJTerm (s 0) (s 1) (s 2) (s 5) (s 4) (s 3))
    (fun a _ b _ h => kap_injective s h)]
  apply Finset.sum_subset
  · intro m hm
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hm
    exact kap_mem_box s a
  · intro m hm hn
    exact sixJTerm_eq_zero_of_not_image s m hm hn

/-- `ZR` is a sign times the 6j symbol. -/
theorem ZR_eq : ZR s = epsS s * sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) := by
  rw [← sum_sixJTerm_kap, Finset.mul_sum, ZR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sixJTerm_kap]
  linear_combination (-((-1 : ℝ) ^ (∑ e, (a e : ℕ)) *
    (threeJ (s 0) (s 1) (s 2) (pr s a 0) (pr s a 1) (pr s a 2) *
     threeJ (s 0) (s 3) (s 4) (-pr s a 0) (pr s a 3) (pr s a 4) *
     threeJ (s 1) (s 3) (s 5) (-pr s a 1) (-pr s a 3) (pr s a 5) *
     threeJ (s 2) (s 4) (s 5) (-pr s a 2) (-pr s a 4) (-pr s a 5)))) * epsS_mul_self s

end SixJ

/-- **The tetrahedron amplitude is the square of a 6j symbol**: for the six edge spins `s`
(doubled units; edges `01, 02, 03, 12, 13, 23`), the integral over `SU(2)^4` of the product of the
six characters `χ_{s e}(g_i g_j⁻¹)` equals `{s₀₁ s₀₂ s₀₃; s₂₃ s₁₃ s₁₂}²`. -/
theorem tetraInt_eq_sixJ_sq (s : Fin 6 → ℕ) :
    tetraInt s = ((sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) : ℝ) : ℂ) ^ 2 := by
  obtain ⟨c, hc, hZ⟩ := Zt_eq_phase_ZR s
  rw [tetraInt_eq, hZ, ZR_eq]
  have hε : ((epsS s : ℝ) : ℂ) * ((epsS s : ℝ) : ℂ) = 1 := by exact_mod_cast epsS_mul_self s
  have : star (c * (((epsS s * sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) : ℝ)) : ℂ)) =
      star c * (((epsS s * sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) : ℝ)) : ℂ) := by
    simp [star_mul']
  rw [this]
  push_cast at hε ⊢
  linear_combination ((sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) : ℂ) ^ 2) * hε * (star c * c)
    + ((sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3) : ℂ) ^ 2) * hc

end Lightlike.SpinFoam
