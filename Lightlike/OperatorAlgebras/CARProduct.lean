import Lightlike.OperatorAlgebras.CARFlip

/-!
# A uniform lower bound for the vacuum projections

For commuting number-operator projections `PF F` of a CAR system and weights `w k ≥ 0` (the occupation of mode `k`) with
classes `μ k`, suppose that on a vector `v` the modes of different classes decouple: `‖a k (PF D v)‖² ≤ w k ‖PF D v‖²`
whenever no mode of `D` has the class of `k`. Then for a set `D₀` of modes and a finite set `s` of modes whose classes
differ from those of `D₀`, with each class carrying total weight at most `1/2`,
`‖PF (D₀ ∪ s) v‖² ≥ ‖PF D₀ v‖² exp(-2 ∑_{k ∈ s} w k)` (`norm_sq_PF_union_ge`). This is the relative Bonferroni bound, one
class at a time, together with `1 - t ≥ exp(-2t)` on `[0, 1/2]`.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARProjections

variable {κ : Type*} {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ] [DecidableEq κ]
  {n : κ → (Γ →L[ℂ] Γ)} (hP : IsProjFamily n)

include hP in
/-- `PF` of a disjoint union is the product. -/
lemma PF_union {D E : Finset κ} (hDE : Disjoint D E) : PF hP (D ∪ E) = PF hP E * PF hP D := by
  induction E using Finset.induction_on with
  | empty => simp [PF_empty]
  | insert k E hk ih =>
    have hDE' : Disjoint D E := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hDE
    have hkD : k ∉ D := fun h => Finset.disjoint_left.1 hDE h (Finset.mem_insert_self _ _)
    have hk' : k ∉ D ∪ E := by simp [hk, hkD]
    rw [Finset.union_insert, PF_insert hP hk', ih hDE', PF_insert hP hk, mul_assoc]

variable {a c : κ → (Γ →L[ℂ] Γ)} (hcc : ∀ i j, c i * c j + c j * c i = 0) (haa : ∀ i j, a i * a j + a j * a i = 0)
  (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0)
  (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ)
  (hP : IsProjFamily (fun k => c k * a k)) (w μ : κ → ℝ) (v : Γ)

include hcc haa hca hadj in
/-- **One class**: if no mode of `D` has the class of any mode of `E` and `‖a k (PF D v)‖² ≤ w k ‖PF D v‖²` for `k ∈ E`,
then `‖PF (D ∪ E) v‖² ≥ (1 - ∑_{k ∈ E} w k) ‖PF D v‖²`. -/
lemma norm_sq_PF_union_class {D E : Finset κ} (hsep : ∀ l ∈ D, ∀ k ∈ E, μ l ≠ μ k)
    (hH : ∀ k ∈ E, ‖a k (PF hP D v)‖ ^ 2 ≤ w k * ‖PF hP D v‖ ^ 2) :
    (1 - ∑ k ∈ E, w k) * ‖PF hP D v‖ ^ 2 ≤ ‖PF hP (D ∪ E) v‖ ^ 2 := by
  have hdisj : Disjoint D E := Finset.disjoint_left.2 fun k hD hE => hsep k hD k hE rfl
  rw [PF_union hP hdisj, ContinuousLinearMap.mul_apply]
  have h1 := norm_sq_PF_ge hP E (PF hP D v)
  have h2 : ∑ k ∈ E, ‖(c k * a k) (PF hP D v)‖ ^ 2 ≤ ∑ k ∈ E, w k * ‖PF hP D v‖ ^ 2 :=
    Finset.sum_le_sum fun k hk => by
      rw [ContinuousLinearMap.mul_apply, norm_sq_cre_ann a c hcc haa hca hadj]
      exact hH k hk
  rw [← Finset.sum_mul] at h2
  nlinarith

/-- Auxiliary lemma `one_sub_ge_exp` for the fermionic Shale theorem. -/
lemma one_sub_ge_exp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : Real.exp (-2 * t) ≤ 1 - t := by
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have h3 : Real.exp (-2 * t) = (Real.exp (2 * t))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [h3]
  have hpos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [inv_le_comm₀ hpos (by linarith)]
  calc (1 - t)⁻¹ ≤ 1 + 2 * t := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    _ ≤ Real.exp (2 * t) := h2

include hcc haa hca hadj in
/-- **The class-by-class lower bound.** -/
theorem norm_sq_PF_union_ge (hw : ∀ k, 0 ≤ w k) (D₀ s : Finset κ) (hsep : ∀ l ∈ D₀, ∀ k ∈ s, μ l ≠ μ k)
    (hH : ∀ k ∈ s, ∀ (D : Finset κ), (∀ l ∈ D, μ l ≠ μ k) → ‖a k (PF hP D v)‖ ^ 2 ≤ w k * ‖PF hP D v‖ ^ 2)
    (hT : ∀ m, ∑ k ∈ s.filter (fun k => μ k = m), w k ≤ 1 / 2) :
    Real.exp (-2 * ∑ k ∈ s, w k) * ‖PF hP D₀ v‖ ^ 2 ≤ ‖PF hP (D₀ ∪ s) v‖ ^ 2 := by
  classical
  have key : ∀ M : Finset ℝ, (∏ m ∈ M, (1 - ∑ k ∈ s.filter (fun k => μ k = m), w k)) * ‖PF hP D₀ v‖ ^ 2 ≤
      ‖PF hP (D₀ ∪ s.filter (fun k => μ k ∈ M)) v‖ ^ 2 := by
    intro M
    induction M using Finset.induction_on with
    | empty => simp
    | insert m M hm ih =>
      have hfilt : s.filter (fun k => μ k ∈ insert m M) =
          s.filter (fun k => μ k ∈ M) ∪ s.filter (fun k => μ k = m) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]; tauto
      have hunion : D₀ ∪ s.filter (fun k => μ k ∈ insert m M) =
          (D₀ ∪ s.filter (fun k => μ k ∈ M)) ∪ s.filter (fun k => μ k = m) := by
        rw [hfilt, Finset.union_assoc]
      rw [hunion]
      have hsep' : ∀ l ∈ D₀ ∪ s.filter (fun k => μ k ∈ M), ∀ k ∈ s.filter (fun k => μ k = m), μ l ≠ μ k := by
        intro l hl k hk
        have hk' := Finset.mem_filter.1 hk
        rcases Finset.mem_union.1 hl with hl | hl
        · exact hsep l hl k hk'.1
        · have := Finset.mem_filter.1 hl
          intro e
          exact hm (by rw [← hk'.2, ← e]; exact this.2)
      have hstep := norm_sq_PF_union_class hcc haa hca hadj hP w μ v hsep' (fun k hk => by
        refine hH k (Finset.mem_filter.1 hk).1 _ (fun l hl => ?_)
        exact hsep' l hl k hk)
      rw [Finset.prod_insert hm, mul_assoc]
      have hnn : 0 ≤ 1 - ∑ k ∈ s.filter (fun k => μ k = m), w k := by linarith [hT m]
      calc (1 - ∑ k ∈ s.filter (fun k => μ k = m), w k) * ((∏ m ∈ M, (1 - ∑ k ∈ s.filter (fun k => μ k = m), w k)) *
              ‖PF hP D₀ v‖ ^ 2)
          ≤ (1 - ∑ k ∈ s.filter (fun k => μ k = m), w k) * ‖PF hP (D₀ ∪ s.filter (fun k => μ k ∈ M)) v‖ ^ 2 :=
            mul_le_mul_of_nonneg_left ih hnn
        _ ≤ _ := hstep
  have hfull := key (s.image μ)
  have hfilt : s.filter (fun k => μ k ∈ s.image μ) = s := by
    ext k; simp only [Finset.mem_filter, Finset.mem_image]; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, k, h, rfl⟩
  rw [hfilt] at hfull
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hfull
  have hsum : ∑ m ∈ s.image μ, ∑ k ∈ s.filter (fun k => μ k = m), w k = ∑ k ∈ s, w k :=
    Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem μ hk) w
  rw [← hsum, Finset.mul_sum, Real.exp_sum]
  · gcongr with m hm
    have h0 : 0 ≤ ∑ k ∈ s.filter (fun k => μ k = m), w k := Finset.sum_nonneg fun k _ => hw k
    have := one_sub_ge_exp h0 (hT m)
    simpa [mul_comm] using this

end Lightlike.OperatorAlgebras.CARProjections
