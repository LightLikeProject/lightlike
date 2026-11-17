import Lightlike.Asymptotics.EPRL.HomForm

/-!
# The Hom form of an invariant tensor in the `fourJ` basis

An invariant four-leg tensor is supported on total weight zero (`invariant_weight_zero`), a nonzero
`fourJ` is too (`fourJ_support`), and in the projection basis an invariant tensor expands in the
`fourJ` tensors with the Hom-form coefficients and one constant sign (`vec_eq_sum`).

## Main results

* `invariant_weight_zero`: a nonzero total weight forces the component to vanish.
* `fourJ_support`: a nonzero `fourJ` has total projection zero and admissible projections.
* `homForm_apply`: `homForm v (p, q) = (-1)^(q₁+q₂) v(p, rev q)`.
* `vec_eq_sum`: the expansion of an invariant tensor in the `fourJ` tensors, with the sign
  `(-1)^(J₁+J₂+ΣJ/2)`.
* `hsInner_homForm_avgP`: group averaging does not change the pairing with an intertwiner.

## References

* P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  arXiv:1902.08439, §5.4, eqs. (44), (45), (49) (the `fourJ` tensors).
-/

open Matrix
open scoped Matrix
open scoped Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling PhyslibAlpha.Sl2 Finset

variable (J : Fin 4 → ℕ)

section Weight




/-- **An invariant tensor is supported on total weight zero**: if `Σ_a (J_a - 2 k_a) ≠ 0` the
component `v k` vanishes. The rotation `diag(e^{iθ}, e^{-iθ})` multiplies the component by
`e^{iθ Σ_a (J_a - 2k_a)}`; at `θ = π / Σ` this is `-1`. -/
theorem invariant_weight_zero {N : ℕ} (J : Fin N → ℕ) {v : LIdx J → ℂ} (hv : IsInvariantN J v) (k : LIdx J)
    (hk : ∑ a, ((J a : ℤ) - 2 * (k a : ℕ)) ≠ 0) : v k = 0 := by
  set W : ℝ := ∑ a, (((J a : ℝ)) - 2 * (k a : ℕ)) with hW
  have hWne : W ≠ 0 := by
    intro h0
    apply hk
    have : ((∑ a, ((J a : ℤ) - 2 * (k a : ℕ)) : ℤ) : ℝ) = 0 := by
      push_cast; exact h0
    exact_mod_cast this
  set θ : ℝ := Real.pi / W with hθ
  have hz : Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
  have h := congrFun (hv (torus (Complex.exp (θ * Complex.I)) hz)) k
  have hdiag : ∀ a, spinMat (J a) (torus (Complex.exp (θ * Complex.I)) hz : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal fun j : Fin (J a + 1) =>
        Complex.exp ((((J a : ℝ) - 2 * (j : ℕ)) * θ : ℝ) * Complex.I) := fun a =>
    spinMat_torus_exp θ
  have hsum : (rhoN J (torus (Complex.exp (θ * Complex.I)) hz : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) k =
      (∏ a, Complex.exp ((((J a : ℝ) - 2 * (k a : ℕ)) * θ : ℝ) * Complex.I)) * v k := by
    rw [mulVec, dotProduct, Finset.sum_eq_single k]
    · simp only [rhoN, Matrix.of_apply, hdiag, diagonal_apply_eq]
    · intro l _ hl
      obtain ⟨a, ha⟩ : ∃ a, k a ≠ l a := not_forall.mp fun hc => hl (funext fun x => (hc x).symm)
      have : (∏ a, spinMat (J a) (torus (Complex.exp (θ * Complex.I)) hz : Matrix (Fin 2) (Fin 2) ℂ)
          (k a) (l a)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hdiag a, diagonal_apply_ne _ ha])
      simp only [rhoN, Matrix.of_apply, this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hsum] at h
  have hprod : (∏ a, Complex.exp ((((J a : ℝ) - 2 * (k a : ℕ)) * θ : ℝ) * Complex.I)) =
      Complex.exp ((W * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [hW, Finset.sum_mul]
    push_cast
    rw [Finset.sum_mul]
  have hWθ : W * θ = Real.pi := by rw [hθ]; field_simp
  rw [hprod, hWθ] at h
  simp only [Complex.exp_pi_mul_I] at h
  have h2 : (2 : ℂ) * v k = 0 := by linear_combination (-1 : ℂ) * h
  simpa using h2


end Weight



/-- **Support of `fourJ`**: a nonzero `fourJ` has total projection zero and admissible projections on
every leg. -/
theorem fourJ_support {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ}
    (h : fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ ≠ 0) :
    m₁ + m₂ + m₃ + m₄ = 0 ∧ AdmProj j₁ m₁ ∧ AdmProj j₂ m₂ ∧ AdmProj j₃ m₃ ∧ AdmProj j₄ m₄ := by
  unfold fourJ at h
  obtain ⟨μ, hμ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
  have h1 : threeJ j₁ j₂ k m₁ m₂ μ ≠ 0 := by
    intro h0; apply hne; rw [mul_assoc, h0, zero_mul, mul_zero]
  have h2 : threeJ k j₃ j₄ (-μ) m₃ m₄ ≠ 0 := by
    intro h0; apply hne; simp [h0]
  have c1 := adm3_of_threeJ_ne_zero h1
  have c2 := adm3_of_threeJ_ne_zero h2
  obtain ⟨hs1, a1, a2, a3, a4, -, -, hp1, hp2, -, -, -, -, -⟩ := c1
  obtain ⟨hs2, -, -, b1, b2, b3, b4, -, hp3, hp4, -, -, -, -⟩ := c2
  exact ⟨by omega, ⟨a1, a2, hp1⟩, ⟨a3, a4, hp2⟩, ⟨b1, b2, hp3⟩, ⟨b3, b4, hp4⟩⟩


/-- The projections `κ_l = J_l - 2 k_l` of the legs. -/
def projOf (k : LIdx J) : Fin 4 → ℤ := fun l => (J l : ℤ) - 2 * (k l : ℕ)

/-- `homForm` at `(p, q)` is the signed component `(-1)^{q₁+q₂} v(p, rev q)`. -/
lemma homForm_apply (v : LIdx J → ℂ) (p : Idx (J 0) (J 1)) (q : Idx (J 2) (J 3)) :
    homForm J v p q = (-1 : ℂ) ^ ((q.1 : ℕ) + q.2) *
      v ((legEquiv J).symm (p, (Fin.rev q.1, Fin.rev q.2))) := by
  have hW : ∀ (n : ℕ) (b q : Fin (n + 1)),
      (Wm n)ᴴ b q = if b = Fin.rev q then (-1 : ℂ) ^ (q : ℕ) else 0 := by
    intro n b q
    rw [Matrix.conjTranspose_apply, Wm_eq_rev]
    split_ifs <;> simp
  rw [homForm, singlet2, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, hW, asMat]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    pow_add]
  ring

/-- **A four-leg invariant tensor expands in the `fourJ` basis**: for every component,
`v_k = (-1)^{J₂+J₃+ΣJ/2} Σ_z c_z ι^{(z)}(κ(k))`, with `c_z = ⟨ι_z, homForm v⟩` the Hom-form
coefficients (the sign is the constant that relates the Hom form to the all-outgoing form on the
total-weight-zero support). -/
theorem vec_eq_sum {v : LIdx J → ℂ} (hv : IsInvariantN J v) (k : LIdx J) :
    v k = (-1 : ℂ) ^ (J 1 + J 2 + (∑ a, J a) / 2) *
      ∑ z ∈ channel (J 0) (J 1) (J 2) (J 3),
        hsInner (ivec (J 0) (J 1) (J 2) (J 3) z) (homForm J v) * fourJNode J z (projOf J k) := by
  by_cases hw : ∑ l, ((J l : ℤ) - 2 * (k l : ℕ)) = 0
  · set p : Idx (J 0) (J 1) := (k 0, k 1) with hp
    set q : Idx (J 2) (J 3) := (Fin.rev (k 2), Fin.rev (k 3)) with hq
    have hF := homForm_isIntertwiner J hv
    have hexp := eq_sum_ivec hF
    have hlhs := homForm_apply J v p q
    have hk : (legEquiv J).symm (p, (Fin.rev q.1, Fin.rev q.2)) = k := by
      rw [Equiv.symm_apply_eq]
      simp only [hp, hq, Fin.rev_rev]
      rfl
    rw [hk] at hlhs
    have h1 := congrFun (congrFun hexp p) q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h1
    have e2 : (2 * ((q.1 : ℕ) : ℤ) - (J 2 : ℤ)) = (J 2 : ℤ) - 2 * (k 2 : ℕ) := by
      have := (k 2).isLt
      simp only [hq, Fin.val_rev]
      omega
    have e3 : (2 * ((q.2 : ℕ) : ℤ) - (J 3 : ℤ)) = (J 3 : ℤ) - 2 * (k 3 : ℕ) := by
      have := (k 3).isLt
      simp only [hq, Fin.val_rev]
      omega
    have hbr : ∀ z ∈ channel (J 0) (J 1) (J 2) (J 3), ivec (J 0) (J 1) (J 2) (J 3) z p q =
        (-1 : ℂ) ^ (J 1 + J 3 + (p.1 : ℕ) + p.2) * fourJNode J z (projOf J k) := by
      intro z hz
      have h := fourJ_eq_ivec (J₁ := J 0) (J₂ := J 1) (J₃ := J 2) (J₄ := J 3) hz p q
      have hF : fourJNode J z (projOf J k) =
          ((fourJ (J 0) (J 1) (J 2) (J 3) z ((J 0 : ℤ) - 2 * (p.1 : ℕ)) ((J 1 : ℤ) - 2 * (p.2 : ℕ))
            (2 * (q.1 : ℕ) - (J 2 : ℤ)) (2 * (q.2 : ℕ) - (J 3 : ℤ)) : ℝ) : ℂ) := by
        simp only [fourJNode, projOf, e2, e3, hp]
      rw [hF, h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hsgn : (-1 : ℂ) ^ ((q.1 : ℕ) + q.2) * (-1 : ℂ) ^ (J 1 + J 3 + (p.1 : ℕ) + p.2) =
        (-1 : ℂ) ^ (J 1 + J 2 + (∑ a, J a) / 2) := by
      rw [← pow_add, neg_one_pow_eq_pow_mod_two,
        neg_one_pow_eq_pow_mod_two (n := J 1 + J 2 + (∑ a, J a) / 2)]
      congr 1
      have h2 := (k 2).isLt
      have h3 := (k 3).isLt
      rw [Fin.sum_univ_four] at hw
      rw [Fin.sum_univ_four]
      simp only [hq, hp, Fin.val_rev]
      omega
    calc v k = (-1 : ℂ) ^ ((q.1 : ℕ) + q.2) * homForm J v p q := by
            rw [hlhs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
      _ = (-1 : ℂ) ^ ((q.1 : ℕ) + q.2) * ∑ z ∈ channel (J 0) (J 1) (J 2) (J 3),
            hsInner (ivec (J 0) (J 1) (J 2) (J 3) z) (homForm J v) *
              ((-1 : ℂ) ^ (J 1 + J 3 + (p.1 : ℕ) + p.2) * fourJNode J z (projOf J k)) := by
            rw [h1]
            congr 1
            exact Finset.sum_congr rfl fun z hz => by rw [hbr z hz]
      _ = _ := by
            rw [← hsgn, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => ?_
            ring
  · have hv0 : v k = 0 := invariant_weight_zero J hv k hw
    have hz : ∀ z, fourJNode J z (projOf J k) = 0 := by
      intro z
      by_contra hne
      have hs := (fourJ_support (by simpa [fourJNode] using hne)).1
      apply hw
      unfold projOf at hs
      rw [Fin.sum_univ_four]
      exact hs
    simp [hv0, hz]

open MeasureTheory in
/-- **Group averaging does not change the pairing with an intertwiner**:
`⟨R, homForm (P u)⟩ = ⟨R, homForm u⟩` for `P = ∫ ρ(g) dg` and `R` an `SU(2)` intertwiner. -/
theorem hsInner_homForm_avgP {R : Matrix (Idx (J 0) (J 1)) (Idx (J 2) (J 3)) ℂ}
    (hR : IsIntertwiner (J 0) (J 1) (J 2) (J 3) R) (u : LIdx J → ℂ) :
    hsInner R (homForm J (avgP J *ᵥ u)) = hsInner R (homForm J u) := by
  have hav : ∀ k : LIdx J, (avgP J *ᵥ u) k = ∫ X : SU2, (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) k ∂haarSU2 := by
    intro k
    unfold avgP
    rw [matInt_mulVec _ _ continuous_rhoN_apply]
  have hent : ∀ p q, homForm J (avgP J *ᵥ u) p q =
      ∫ X : SU2, homForm J (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) p q ∂haarSU2 := by
    intro p q
    simp only [homForm_apply, hav]
    rw [integral_const_mul]
  have hcont : ∀ i j, Continuous fun X : SU2 =>
      homForm J (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) i j := by
    intro i j
    simp only [homForm_apply]
    exact continuous_const.mul (continuous_rhoN_mulVec_apply u _)
  have hconst : ∀ X : SU2, hsInner R (homForm J (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u)) =
      hsInner R (homForm J u) := fun X => by
    rw [homForm_rhoN, hsInner_conj_of_isIntertwiner J hR]
  calc hsInner R (homForm J (avgP J *ᵥ u))
      = ∫ X : SU2, hsInner R (homForm J (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u)) ∂haarSU2 := by
        unfold hsInner
        simp only [hent]
        rw [integral_finsetSum _ fun i _ => ?_]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => ?_]
          · exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
          · exact (integrable_of_continuous (hcont i j)).const_mul _
        · refine integrable_finsetSum _ fun j _ => ?_
          exact (integrable_of_continuous (hcont i j)).const_mul _
    _ = hsInner R (homForm J u) := by
        simp only [hconst]
        simp

end Lightlike.Asymptotics.EPRL
