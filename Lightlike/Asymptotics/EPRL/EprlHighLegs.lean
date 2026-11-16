import Lightlike.Asymptotics.EPRL.EprlHighLift
import Lightlike.Asymptotics.EPRL.EprlHighVertex
import Lightlike.Asymptotics.EPRL.EprlHighProj

/-!
# The leg functions of the `γ > 1` node integrand

The node integrand of the coherent EPRL vertex for the lowest Clebsch–Gordan component is a product over
the four legs of the node (`liftLow_entry`): the entry of `D(G) Φ̃(homForm ⊗_l s_l) D'(G)ᴴ` is the product
of `D(G) Y s_l` on the two outgoing legs and `(Y s_l) E D(G)ᴴ` on the two incoming ones, with the singlet
form `E = Wᴴ ⊗ Wᴴ` and `Y = Y_low`. This file writes the product as a function of the pair of
projections `(μ, ν)` of the node, through `legFun`, with the signs of the outgoing legs
(`nodeLeg`, `nodeLeg_projOf`, `legFam`, `nodeLeg_eq_prod`), and shows that it is continuous in the group
element.

The `Spin(4)` action and the dual action are leg by leg on a product vector (`act4_mulVec_prod`,
`vecMul_act4_prod`), and the singlet forms are too (`vecMul_singlet_prod`).

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4.
-/

open Matrix Finset MeasureTheory
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- A vector on `V_{n/2} ⊗ V_{m/2}` as a function of the pair of projections `(μ, ν)`, zero off the
weights of the representation. -/
noncomputable def legFun (n m : ℕ) (w : Idx n m → ℂ) (μ ν : ℤ) : ℂ :=
  ∑ a : Fin (n + 1), ∑ b : Fin (m + 1),
    if μ = (n : ℤ) - 2 * (a : ℕ) ∧ ν = (m : ℤ) - 2 * (b : ℕ) then w (a, b) else 0

lemma legFun_proj (n m : ℕ) (w : Idx n m → ℂ) (a : Fin (n + 1)) (b : Fin (m + 1)) :
    legFun n m w ((n : ℤ) - 2 * (a : ℕ)) ((m : ℤ) - 2 * (b : ℕ)) = w (a, b) := by
  unfold legFun
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      have : ¬ ((m : ℤ) - 2 * (b : ℕ) = (m : ℤ) - 2 * (b' : ℕ)) := fun h =>
        hb' (Fin.ext (by omega))
      simp [this]
    · simp
  · intro a' _ ha'
    have : ¬ ((n : ℤ) - 2 * (a : ℕ) = (n : ℤ) - 2 * (a' : ℕ)) := fun h =>
      ha' (Fin.ext (by omega))
    simp [this]
  · simp

lemma exists_of_legFun_ne_zero (n m : ℕ) (w : Idx n m → ℂ) (μ ν : ℤ) (h : legFun n m w μ ν ≠ 0) :
    ∃ (a : Fin (n + 1)) (b : Fin (m + 1)), μ = (n : ℤ) - 2 * (a : ℕ) ∧ ν = (m : ℤ) - 2 * (b : ℕ) := by
  by_contra hne
  apply h
  unfold legFun
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  exact ite_eq_right_iff.mpr fun hh => absurd ⟨a, b, hh.1, hh.2⟩ hne

/-- **The Spin(4) action on a pair of legs acts leg by leg on a product vector**. -/
theorem act4_mulVec_prod (n₁ n₂ m₁ m₂ : ℕ) (G : Spin4) (a : Idx n₁ m₁ → ℂ) (b : Idx n₂ m₂ → ℂ) :
    act4 n₁ n₂ m₁ m₂ G *ᵥ (fun P : Idx n₁ n₂ × Idx m₁ m₂ => a (P.1.1, P.2.1) * b (P.1.2, P.2.2)) =
      fun P => (spin4Mat n₁ m₁ G *ᵥ a) (P.1.1, P.2.1) * (spin4Mat n₂ m₂ G *ᵥ b) (P.1.2, P.2.2) := by
  have h := congrFun (kronecker_mulVec_prod (spin4Mat n₁ m₁ G) (spin4Mat n₂ m₂ G) a b)
  funext P
  have h1 := h ((shuffle n₁ m₁ n₂ m₂).symm P)
  rw [spin4Mat_kronecker, Matrix.submatrix_mulVec_equiv] at h1
  simpa [shuffle, Function.comp_def] using h1


/-- The dual action `v ↦ v (act4 G)ᴴ` is leg by leg on a product vector. -/
theorem vecMul_act4_prod (n₁ n₂ m₁ m₂ : ℕ) (G : Spin4) (a : Idx n₁ m₁ → ℂ) (b : Idx n₂ m₂ → ℂ) :
    (fun P : Idx n₁ n₂ × Idx m₁ m₂ => a (P.1.1, P.2.1) * b (P.1.2, P.2.2)) ᵥ* (act4 n₁ n₂ m₁ m₂ G)ᴴ =
      fun P => (a ᵥ* (spin4Mat n₁ m₁ G)ᴴ) (P.1.1, P.2.1) * (b ᵥ* (spin4Mat n₂ m₂ G)ᴴ) (P.1.2, P.2.2) := by
  have h1 := act4_mulVec_prod n₁ n₂ m₁ m₂ G (star a) (star b)
  have hs : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) (v : κ → ℂ) (i : ι),
      (starRingEnd ℂ) ((M *ᵥ star v) i) = (v ᵥ* Mᴴ) i := by
    intro ι κ _ _ M v i
    have := congrFun (Matrix.star_mulVec M (star v)) i
    simpa using this
  have hv : (fun P : Idx n₁ n₂ × Idx m₁ m₂ => a (P.1.1, P.2.1) * b (P.1.2, P.2.2)) =
      star (fun P : Idx n₁ n₂ × Idx m₁ m₂ => star a (P.1.1, P.2.1) * star b (P.1.2, P.2.2)) := by
    funext P; simp
  funext P
  rw [hv, ← Matrix.star_mulVec, h1]
  simp only [Pi.star_apply, star_mul']
  rw [show star ((spin4Mat n₁ m₁ G *ᵥ star a) (P.1.1, P.2.1)) =
      (a ᵥ* (spin4Mat n₁ m₁ G)ᴴ) (P.1.1, P.2.1) from hs _ _ _,
    show star ((spin4Mat n₂ m₂ G *ᵥ star b) (P.1.2, P.2.2)) =
      (b ᵥ* (spin4Mat n₂ m₂ G)ᴴ) (P.1.2, P.2.2) from hs _ _ _]


/-- The singlet forms act leg by leg on a product vector. -/
theorem vecMul_singlet_prod (n m : Fin 4 → ℕ) (c : Idx (n 2) (m 2) → ℂ) (d : Idx (n 3) (m 3) → ℂ) :
    (fun P : Idx (n 2) (n 3) × Idx (m 2) (m 3) => c (P.1.1, P.2.1) * d (P.1.2, P.2.2)) ᵥ*
        (singlet2 n ⊗ₖ singlet2 m) =
      fun P => (c ᵥ* ((Wm (n 2))ᴴ ⊗ₖ (Wm (m 2))ᴴ)) (P.1.1, P.2.1) *
        (d ᵥ* ((Wm (n 3))ᴴ ⊗ₖ (Wm (m 3))ᴴ)) (P.1.2, P.2.2) := by
  have h := congrFun (vecMul_kronecker_prod c d ((Wm (n 2))ᴴ ⊗ₖ (Wm (m 2))ᴴ)
    ((Wm (n 3))ᴴ ⊗ₖ (Wm (m 3))ᴴ))
  funext P
  have h1 := h ((shuffle (n 2) (m 2) (n 3) (m 3)).symm P)
  unfold singlet2
  rw [kronecker_shuffle, Matrix.submatrix_vecMul_equiv]
  simpa [Function.comp_def, shuffle] using h1


/-- **The node integrand for `γ > 1` is a product over the four legs**: the entry of
`D(G) Φ̃(homForm ⊗_l s_l) D'(G)ᴴ` at `(P, Q)` is the product of the leg functions `K_0, K_1` (the
outgoing legs, `D(G) Y s_l`) and `B_2, B_3` (the incoming legs, `(Y s_l) E D(G)ᴴ`, with the singlet
form `E = Wᴴ ⊗ Wᴴ`). -/
theorem liftLow_entry (n m : Fin 4 → ℕ) (h₂ : m 2 ≤ n 2) (h₃ : m 3 ≤ n 3)
    (s : (l : Fin 4) → Fin ((n - m) l + 1) → ℂ) (G : Spin4)
    (P : Idx (n 0) (n 1) × Idx (m 0) (m 1)) (Q : Idx (n 2) (n 3) × Idx (m 2) (m 3)) :
    (act4 (n 0) (n 1) (m 0) (m 1) G *
        eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (homForm (n - m) (prodVec (n - m) s)) * (act4 (n 2) (n 3) (m 2) (m 3) G)ᴴ) P Q =
      (spin4Mat (n 0) (m 0) G *ᵥ (eprlMapLow (n 0) (m 0) *ᵥ s 0)) (P.1.1, P.2.1) *
        (spin4Mat (n 1) (m 1) G *ᵥ (eprlMapLow (n 1) (m 1) *ᵥ s 1)) (P.1.2, P.2.2) *
      (((eprlMapLow (n 2) (m 2) *ᵥ s 2) ᵥ* ((Wm (n 2))ᴴ ⊗ₖ (Wm (m 2))ᴴ)) ᵥ*
          (spin4Mat (n 2) (m 2) G)ᴴ) (Q.1.1, Q.2.1) *
        (((eprlMapLow (n 3) (m 3) *ᵥ s 3) ᵥ* ((Wm (n 3))ᴴ ⊗ₖ (Wm (m 3))ᴴ)) ᵥ*
          (spin4Mat (n 3) (m 3) G)ᴴ) (Q.1.2, Q.2.2) := by
  rw [eprlLiftLow_homForm_prod n m h₂ h₃ s, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_apply]
  rw [eprlPairLow_mulVec_prod, eprlPairLow_mulVec_prod, vecMul_singlet_prod, act4_mulVec_prod,
    vecMul_act4_prod]
  ring


lemma edgeSign_proj (n : ℕ) (a : Fin (n + 1)) :
    edgeSign n ((n : ℤ) - 2 * (a : ℕ)) = (-1) ^ (a : ℕ) := by
  unfold edgeSign
  have : (((n : ℤ) - ((n : ℤ) - 2 * (a : ℕ))) / 2) = (a : ℕ) := by omega
  rw [this]
  simp


/-- The leg functions of the coherent node integrand for `γ > 1` at the group element `G`. -/
noncomputable def nodeLeg (n m : Fin 4 → ℕ) (g : Fin 4 → SU2) (G : Spin4) (μ ν : Fin 4 → ℤ) : ℂ :=
  (((edgeSign (n 0) (μ 0) * edgeSign (m 0) (ν 0) : ℝ) : ℂ) *
      legFun (n 0) (m 0) (spin4Mat (n 0) (m 0) G *ᵥ (eprlMapLow (n 0) (m 0) *ᵥ
        cohState ((n - m) 0) (g 0))) (μ 0) (ν 0)) *
    (((edgeSign (n 1) (μ 1) * edgeSign (m 1) (ν 1) : ℝ) : ℂ) *
      legFun (n 1) (m 1) (spin4Mat (n 1) (m 1) G *ᵥ (eprlMapLow (n 1) (m 1) *ᵥ
        cohState ((n - m) 1) (g 1))) (μ 1) (ν 1)) *
    legFun (n 2) (m 2) (((eprlMapLow (n 2) (m 2) *ᵥ cohState ((n - m) 2) (g 2)) ᵥ*
      ((Wm (n 2))ᴴ ⊗ₖ (Wm (m 2))ᴴ)) ᵥ* (spin4Mat (n 2) (m 2) G)ᴴ) (-μ 2) (-ν 2) *
    legFun (n 3) (m 3) (((eprlMapLow (n 3) (m 3) *ᵥ cohState ((n - m) 3) (g 3)) ᵥ*
      ((Wm (n 3))ᴴ ⊗ₖ (Wm (m 3))ᴴ)) ᵥ* (spin4Mat (n 3) (m 3) G)ᴴ) (-μ 3) (-ν 3)


/-- At the projections of two components the leg functions give the entry of the node integrand, with
the signs `(-1)^{k₀ + k₁ + l₀ + l₁}` of the outgoing legs. -/
theorem nodeLeg_projOf (n m : Fin 4 → ℕ) (h₂ : m 2 ≤ n 2) (h₃ : m 3 ≤ n 3) (g : Fin 4 → SU2)
    (G : Spin4) (k : LIdx n) (l : LIdx m) :
    nodeLeg n m g G (projOf n k) (projOf m l) =
      (-1 : ℂ) ^ ((k 0 : ℕ) + k 1 + l 0 + l 1) *
        (act4 (n 0) (n 1) (m 0) (m 1) G *
          eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
            (homForm (n - m) (prodVec (n - m) fun i => cohState ((n - m) i) (g i))) *
          (act4 (n 2) (n 3) (m 2) (m 3) G)ᴴ) ((k 0, k 1), (l 0, l 1))
          ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) := by
  rw [liftLow_entry n m h₂ h₃ _ G]
  have e2 : ∀ (J : Fin 4 → ℕ) (i : Fin 4) (a : LIdx J), -(projOf J a i) =
      (J i : ℤ) - 2 * ((Fin.rev (a i) : Fin (J i + 1)) : ℕ) := by
    intro J i a
    have := (a i).isLt
    simp only [projOf, Fin.val_rev]
    omega
  unfold nodeLeg
  simp only [e2]
  have p0 : projOf n k 0 = (n 0 : ℤ) - 2 * ((k 0 : Fin (n 0 + 1)) : ℕ) := rfl
  have p1 : projOf n k 1 = (n 1 : ℤ) - 2 * ((k 1 : Fin (n 1 + 1)) : ℕ) := rfl
  have q0 : projOf m l 0 = (m 0 : ℤ) - 2 * ((l 0 : Fin (m 0 + 1)) : ℕ) := rfl
  have q1 : projOf m l 1 = (m 1 : ℤ) - 2 * ((l 1 : Fin (m 1 + 1)) : ℕ) := rfl
  rw [p0, p1, q0, q1, legFun_proj, legFun_proj, legFun_proj, legFun_proj, edgeSign_proj,
    edgeSign_proj, edgeSign_proj, edgeSign_proj]
  push_cast
  ring


lemma continuous_spin4Mat_apply (n m : ℕ) (p q : Idx n m) :
    Continuous fun G : Spin4 => spin4Mat n m G p q := by
  simp only [spin4Mat_apply]
  exact (((continuous_spinMat_apply n _ _).comp continuous_fst).mul
    ((continuous_spinMat_apply m _ _).comp continuous_snd))

lemma continuous_mulVec_spin4 (n m : ℕ) (w : Idx n m → ℂ) (p : Idx n m) :
    Continuous fun G : Spin4 => (spin4Mat n m G *ᵥ w) p := by
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun q _ => (continuous_spin4Mat_apply n m p q).mul continuous_const

lemma continuous_vecMul_spin4 (n m : ℕ) (w : Idx n m → ℂ) (p : Idx n m) :
    Continuous fun G : Spin4 => (w ᵥ* (spin4Mat n m G)ᴴ) p := by
  simp only [Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
  exact continuous_finsetSum _ fun q _ =>
    continuous_const.mul (continuous_star.comp (continuous_spin4Mat_apply n m p q))

lemma continuous_legFun (n m : ℕ) (w : Spin4 → Idx n m → ℂ) (hw : ∀ p, Continuous fun G => w G p)
    (μ ν : ℤ) : Continuous fun G => legFun n m (w G) μ ν := by
  unfold legFun
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  by_cases h : μ = (n : ℤ) - 2 * (a : ℕ) ∧ ν = (m : ℤ) - 2 * (b : ℕ)
  · simp only [h, and_self, ite_true]
    exact hw _
  · simp only [h, ite_false]
    exact continuous_const

/-- The leg functions of the node integrand are continuous in the group element. -/
theorem continuous_nodeLeg (n m : Fin 4 → ℕ) (g : Fin 4 → SU2) (μ ν : Fin 4 → ℤ) :
    Continuous fun G : Spin4 => nodeLeg n m g G μ ν := by
  unfold nodeLeg
  refine (((continuous_const.mul (continuous_legFun _ _ _ (fun p => ?_) _ _)).mul
    (continuous_const.mul (continuous_legFun _ _ _ (fun p => ?_) _ _))).mul
    (continuous_legFun _ _ _ (fun p => ?_) _ _)).mul (continuous_legFun _ _ _ (fun p => ?_) _ _)
  · exact continuous_mulVec_spin4 _ _ _ p
  · exact continuous_mulVec_spin4 _ _ _ p
  · exact continuous_vecMul_spin4 _ _ _ p
  · exact continuous_vecMul_spin4 _ _ _ p


/-- The four leg functions of a node, as one family indexed by the leg. -/
noncomputable def legFam (n m : Fin 4 → ℕ) (g : Fin 4 → SU2) (G : Spin4) : Fin 4 → ℤ → ℤ → ℂ :=
  ![fun μ ν => ((edgeSign (n 0) μ * edgeSign (m 0) ν : ℝ) : ℂ) *
      legFun (n 0) (m 0) (spin4Mat (n 0) (m 0) G *ᵥ (eprlMapLow (n 0) (m 0) *ᵥ
        cohState ((n - m) 0) (g 0))) μ ν,
    fun μ ν => ((edgeSign (n 1) μ * edgeSign (m 1) ν : ℝ) : ℂ) *
      legFun (n 1) (m 1) (spin4Mat (n 1) (m 1) G *ᵥ (eprlMapLow (n 1) (m 1) *ᵥ
        cohState ((n - m) 1) (g 1))) μ ν,
    fun μ ν => legFun (n 2) (m 2) (((eprlMapLow (n 2) (m 2) *ᵥ cohState ((n - m) 2) (g 2)) ᵥ*
      ((Wm (n 2))ᴴ ⊗ₖ (Wm (m 2))ᴴ)) ᵥ* (spin4Mat (n 2) (m 2) G)ᴴ) (-μ) (-ν),
    fun μ ν => legFun (n 3) (m 3) (((eprlMapLow (n 3) (m 3) *ᵥ cohState ((n - m) 3) (g 3)) ᵥ*
      ((Wm (n 3))ᴴ ⊗ₖ (Wm (m 3))ᴴ)) ᵥ* (spin4Mat (n 3) (m 3) G)ᴴ) (-μ) (-ν)]

theorem nodeLeg_eq_prod (n m : Fin 4 → ℕ) (g : Fin 4 → SU2) (G : Spin4) (μ ν : Fin 4 → ℤ) :
    nodeLeg n m g G μ ν = ∏ l, legFam n m g G l (μ l) (ν l) := by
  simp [nodeLeg, legFam, Fin.prod_univ_four]

end Lightlike.Asymptotics.EPRL
