import Lightlike.OperatorAlgebras.CARProjections

/-!
# Flipping modes of a CAR system

For CAR operators `a k`, `c k` with `p k = a k + c k` (a self-adjoint unitary), `(1 - n k) p k = p k n k` for the number
operator `n k = c k a k`. Hence for a finite set `F` of modes and any vector `v` there is a list `J ⊆ F` of modes such that the
product `W` of the `p j`, `j ∈ J`, has `‖PF F (W v)‖² ≥ 2^{-|F|} ‖v‖²`: one mode at a time, `p k` exchanges the two
halves `(1 - n k) v` and `n k v` of the norm.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARProjections

variable {κ : Type*} {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ] [DecidableEq κ]
  (a c : κ → (Γ →L[ℂ] Γ))

/-- The Majorana-type operator `p k = a k + c k`. -/
def pOp (k : κ) : Γ →L[ℂ] Γ := a k + c k

variable {a c}
variable (hcc : ∀ i j, c i * c j + c j * c i = 0) (haa : ∀ i j, a i * a j + a j * a i = 0)
  (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0)

omit [CompleteSpace Γ] [DecidableEq κ] in
/-- Auxiliary lemma `sq_eq_zero_of_anticomm` for the fermionic Shale theorem. -/
lemma sq_eq_zero_of_anticomm {A : Γ →L[ℂ] Γ} (h : A * A + A * A = 0) : A * A = 0 := by
  have h3 : (2 : ℂ) • (A * A) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

include hca hcc haa in
/-- Auxiliary lemma `pOp_sq` for the fermionic Shale theorem. -/
lemma pOp_sq (k : κ) : pOp a c k * pOp a c k = 1 := by
  have h1 := hca k k
  simp only [if_true] at h1
  have h2 := sq_eq_zero_of_anticomm (hcc k k)
  have h3 := sq_eq_zero_of_anticomm (haa k k)
  unfold pOp
  rw [add_mul, mul_add, mul_add, h2, h3]
  rw [← h1]; abel

include hca hcc haa in
/-- `p k` anticommutes with `a l` and `c l` for `l ≠ k`. -/
lemma pOp_anticomm_a {k l : κ} (hkl : l ≠ k) : pOp a c k * a l + a l * pOp a c k = 0 := by
  have e1 := haa k l
  have e2 := hca l k
  rw [if_neg hkl] at e2
  unfold pOp
  calc (a k + c k) * a l + a l * (a k + c k) = (a k * a l + a l * a k) + (a l * c k + c k * a l) := by noncomm_ring
    _ = 0 := by rw [e1, e2, add_zero]

include hca hcc haa in
/-- Auxiliary lemma `pOp_anticomm_c` for the fermionic Shale theorem. -/
lemma pOp_anticomm_c {k l : κ} (hkl : l ≠ k) : pOp a c k * c l + c l * pOp a c k = 0 := by
  have e1 := hcc k l
  have e2 := hca k l
  rw [if_neg (Ne.symm hkl)] at e2
  unfold pOp
  calc (a k + c k) * c l + c l * (a k + c k) = (c k * c l + c l * c k) + (a k * c l + c l * a k) := by noncomm_ring
    _ = 0 := by rw [e1, e2, add_zero]

omit [CompleteSpace Γ] [DecidableEq κ] in
/-- An operator anticommuting with `Y` and `Z` commutes with `Y * Z`. -/
lemma commute_of_anticomm {X Y Z : Γ →L[ℂ] Γ} (h1 : X * Y + Y * X = 0) (h2 : X * Z + Z * X = 0) :
    X * (Y * Z) = (Y * Z) * X := by
  have e1 : X * Y = -(Y * X) := eq_neg_of_add_eq_zero_left h1
  have e2 : X * Z = -(Z * X) := eq_neg_of_add_eq_zero_left h2
  rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]

include hca hcc haa in
/-- `p k` commutes with the number operator `n l = c l * a l` for `l ≠ k`. -/
lemma pOp_comm_n {k l : κ} (hkl : l ≠ k) : pOp a c k * (c l * a l) = (c l * a l) * pOp a c k :=
  (commute_of_anticomm (pOp_anticomm_c hcc haa hca hkl) (pOp_anticomm_a hcc haa hca hkl))

include hca hcc haa in
/-- `(1 - n k) p k = p k n k`. -/
lemma Q_pOp (k : κ) : (1 - c k * a k) * pOp a c k = pOp a c k * (c k * a k) := by
  have h1 := hca k k
  simp only [if_true] at h1
  have h2 := sq_eq_zero_of_anticomm (hcc k k)
  have h3 := sq_eq_zero_of_anticomm (haa k k)
  have h1' : a k * c k = 1 - c k * a k := eq_sub_of_add_eq h1
  unfold pOp
  have e1 : (1 - c k * a k) * (a k + c k) = a k := by
    have t1 : c k * a k * a k = 0 := by rw [mul_assoc, h3, mul_zero]
    have t2 : c k * a k * c k = c k := by
      rw [mul_assoc, h1', mul_sub, mul_one, ← mul_assoc, h2, zero_mul, sub_zero]
    rw [sub_mul, mul_add, one_mul, one_mul, mul_add, t1, t2]; abel
  have e2 : (a k + c k) * (c k * a k) = a k := by
    have t1 : c k * (c k * a k) = 0 := by rw [← mul_assoc, h2, zero_mul]
    have t2 : a k * (c k * a k) = a k := by
      rw [← mul_assoc, h1', sub_mul, one_mul, mul_assoc, h3, mul_zero, sub_zero]
    rw [add_mul, t1, t2, add_zero]
  rw [e1, e2]

variable (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ)

include hca hcc haa hadj in
/-- `p k` preserves the norm. -/
lemma norm_pOp (k : κ) (x : Γ) : ‖pOp a c k x‖ = ‖x‖ := by
  have hadj' : ∀ j x y, ⟪c j x, y⟫_ℂ = ⟪x, a j y⟫_ℂ := fun j x y => by
    rw [← inner_conj_symm, ← hadj, inner_conj_symm]
  have hsym : ∀ x y, ⟪pOp a c k x, y⟫_ℂ = ⟪x, pOp a c k y⟫_ℂ := fun x y => by
    simp only [pOp, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hadj, hadj']
    ring
  have h1 : ⟪pOp a c k x, pOp a c k x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [hsym, ← ContinuousLinearMap.mul_apply, pOp_sq hcc haa hca]; simp
  have h2 := congrArg RCLike.re h1
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The product of the `p j`, `j ∈ J`. -/
def Wlist (J : List κ) : Γ →L[ℂ] Γ := (J.map (pOp a c)).prod

include hca hcc haa hadj in
/-- `PF F` commutes with `p k` for `k ∉ F`. -/
lemma PF_comm_pOp (hP : IsProjFamily (fun k => c k * a k)) {F : Finset κ} {k : κ} (hk : k ∉ F) :
    PF hP F * pOp a c k = pOp a c k * PF hP F := by
  induction F using Finset.induction_on with
  | empty => rw [PF_empty, mul_one, one_mul]
  | insert l F hl ih =>
    have hkl : l ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hkF : k ∉ F := fun h => hk (Finset.mem_insert_of_mem h)
    rw [PF_insert hP hl]
    have hQ : Q (fun k => c k * a k) l * pOp a c k = pOp a c k * Q (fun k => c k * a k) l := by
      simp only [Q, sub_mul, mul_sub, one_mul, mul_one]
      rw [(pOp_comm_n hcc haa hca hkl)]
    rw [mul_assoc, ih hkF, ← mul_assoc, hQ, mul_assoc]

include hca hcc haa hadj in
/-- **Flipping modes**: for a finite set `F` of modes and any vector `v` some product `W` of the `p j`, `j ∈ F`, has
`‖PF F (W v)‖² ≥ 2^{-|F|} ‖v‖²`. -/
theorem exists_flip (hP : IsProjFamily (fun k => c k * a k)) (F : Finset κ) (v : Γ) :
    ∃ J : List κ, (∀ j ∈ J, j ∈ F) ∧ ‖v‖ ^ 2 / 2 ^ F.card ≤ ‖PF hP F (Wlist (a := a) (c := c) J v)‖ ^ 2 := by
  induction F using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp [PF_empty, Wlist]⟩
  | insert k F hk ih =>
    obtain ⟨J, hJ, hbound⟩ := ih
    set v' := PF hP F (Wlist (a := a) (c := c) J v) with hv'
    have hsum : ‖Q (fun k => c k * a k) k v'‖ ^ 2 + ‖(c k * a k) v'‖ ^ 2 = ‖v'‖ ^ 2 := by
      rw [norm_sq_Q hP]; ring
    have hB : ‖PF hP (insert k F) (Wlist (a := a) (c := c) (k :: J) v)‖ = ‖(c k * a k) v'‖ := by
      have e1 : Wlist (a := a) (c := c) (k :: J) = pOp a c k * Wlist (a := a) (c := c) J := by
        simp [Wlist]
      rw [PF_insert hP hk, e1]
      have e2 : PF hP F ((pOp a c k * Wlist (a := a) (c := c) J) v) = pOp a c k (PF hP F (Wlist (a := a) (c := c) J v)) := by
        rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← mul_assoc, PF_comm_pOp hcc haa hca hadj hP hk,
          mul_assoc]
        rfl
      have e3 : (Q (fun k => c k * a k) k * PF hP F) ((pOp a c k * Wlist (a := a) (c := c) J) v) =
          Q (fun k => c k * a k) k (pOp a c k (PF hP F (Wlist (a := a) (c := c) J v))) := by
        rw [ContinuousLinearMap.mul_apply, e2]
      rw [e3]
      have := Q_pOp hcc haa hca k
      have e4 : Q (fun k => c k * a k) k (pOp a c k v') = pOp a c k ((c k * a k) v') := by
        have := congrArg (fun T => T v') this
        simpa [Q] using this
      rw [e4, norm_pOp hcc haa hca hadj]
    by_cases hcase : ‖v'‖ ^ 2 / 2 ≤ ‖Q (fun k => c k * a k) k v'‖ ^ 2
    · refine ⟨J, fun j hj => Finset.mem_insert_of_mem (hJ j hj), ?_⟩
      rw [PF_insert hP hk, ContinuousLinearMap.mul_apply, Finset.card_insert_of_notMem hk, pow_succ]
      calc ‖v‖ ^ 2 / (2 ^ F.card * 2) = (‖v‖ ^ 2 / 2 ^ F.card) / 2 := by rw [div_div]
        _ ≤ ‖v'‖ ^ 2 / 2 := by gcongr
        _ ≤ _ := hcase
    · refine ⟨k :: J, fun j hj => ?_, ?_⟩
      · rcases List.mem_cons.1 hj with rfl | hj'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hJ j hj')
      · rw [hB, Finset.card_insert_of_notMem hk, pow_succ]
        calc ‖v‖ ^ 2 / (2 ^ F.card * 2) = (‖v‖ ^ 2 / 2 ^ F.card) / 2 := by rw [div_div]
          _ ≤ ‖v'‖ ^ 2 / 2 := by gcongr
          _ ≤ _ := by linarith [not_le.1 hcase]

omit [CompleteSpace Γ] [DecidableEq κ] in
/-- An operator anticommuting with every `p j`, `j ∈ J`, commutes with the product up to the sign `(-1)^{|J|}`. -/
lemma comm_Wlist (X : Γ →L[ℂ] Γ) (J : List κ) (h : ∀ j ∈ J, X * pOp a c j + pOp a c j * X = 0) :
    X * Wlist (a := a) (c := c) J = (-1 : ℂ) ^ J.length • (Wlist (a := a) (c := c) J * X) := by
  induction J with
  | nil => simp [Wlist]
  | cons j J ih =>
    have e1 : X * pOp a c j = -(pOp a c j * X) := eq_neg_of_add_eq_zero_left (h j (by simp))
    have ih' := ih (fun l hl => h l (List.mem_cons_of_mem _ hl))
    have e : Wlist (a := a) (c := c) (j :: J) = pOp a c j * Wlist (a := a) (c := c) J := by simp [Wlist]
    rw [e, ← mul_assoc, e1, neg_mul, mul_assoc, ih', mul_smul_comm, List.length_cons, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, smul_neg, mul_assoc]

/-- An operator commuting with every number operator `n l`, `l ∈ D`, commutes with `PF D`. -/
lemma comm_PF (hP : IsProjFamily (fun k => c k * a k)) (X : Γ →L[ℂ] Γ) (D : Finset κ)
    (h : ∀ l ∈ D, X * (c l * a l) = (c l * a l) * X) : X * PF hP D = PF hP D * X := by
  induction D using Finset.induction_on with
  | empty => rw [PF_empty, mul_one, one_mul]
  | insert l D hl ih =>
    rw [PF_insert hP hl]
    have h1 : X * Q (fun k => c k * a k) l = Q (fun k => c k * a k) l * X := by
      simp only [Q, mul_sub, sub_mul, mul_one, one_mul]
      rw [h l (Finset.mem_insert_self _ _)]
    rw [← mul_assoc, h1, mul_assoc, ih (fun l' hl' => h l' (Finset.mem_insert_of_mem hl')), mul_assoc]

omit [CompleteSpace Γ] [DecidableEq κ] in
/-- **The step estimate**: if `A Ω = Ak Ω`, `A Y = ε Y A` and `Ak Y = ε' Y Ak` with `|ε| = |ε'| = 1`, and `Ak` has norm
at most `r`, then `‖A (Y Ω)‖ ≤ r ‖Y Ω‖`. -/
lemma norm_step {A Ak Y : Γ →L[ℂ] Γ} {ε ε' : ℂ} (hε : ‖ε‖ = 1) (hε' : ‖ε'‖ = 1) (hA : A * Y = ε • (Y * A))
    (hAk : Ak * Y = ε' • (Y * Ak)) {Ω : Γ} (hΩ : A Ω = Ak Ω) {r : ℝ} (hr : ∀ v, ‖Ak v‖ ≤ r * ‖v‖) :
    ‖A (Y Ω)‖ ≤ r * ‖Y Ω‖ := by
  have h1 : A (Y Ω) = ε • Y (A Ω) := by
    have := congrArg (fun T : Γ →L[ℂ] Γ => T Ω) hA
    simpa using this
  have h2 : Ak (Y Ω) = ε' • Y (Ak Ω) := by
    have := congrArg (fun T : Γ →L[ℂ] Γ => T Ω) hAk
    simpa using this
  have h3 : ‖A (Y Ω)‖ = ‖Ak (Y Ω)‖ := by
    rw [h1, h2, hΩ, norm_smul, norm_smul, hε, hε']
  rw [h3]; exact hr _

end Lightlike.OperatorAlgebras.CARProjections
