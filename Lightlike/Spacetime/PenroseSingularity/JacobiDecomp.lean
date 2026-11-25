import Mathlib

/-!
# The null complement is spanned by a screen frame and the null vector (G1-012, step D3b, algebra)

In a space of dimension `m + 2` with a nondegenerate symmetric form `B`, a null `w ≠ 0` and `m` vectors
`J i` orthogonal to `w` with invertible Gram matrix span `w^⊥` together with `w`.
-/

open Module Matrix

noncomputable section

namespace Lightlike.Penrose

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {m : ℕ}

theorem exists_decomp_perp_null (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (hdim : finrank ℝ V = m + 2) (J : Fin m → V) (w : V)
    (hww : B w w = 0) (hw0 : w ≠ 0) (hwJ : ∀ i, B w (J i) = 0)
    (hQ : (Matrix.of fun i j => B (J i) (J j)).det ≠ 0) (u : V) (hu : B w u = 0) :
    ∃ (a : Fin m → ℝ) (c : ℝ), u = ∑ i, a i • J i + c • w := by
  set F : Fin (m + 1) → V := Fin.cons w J with hF
  -- linear independence
  have hli : LinearIndependent ℝ F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_succ] at hc
    simp only [hF, Fin.cons_zero, Fin.cons_succ] at hc
    -- pair with `J l`
    have hpair : ∀ l, ∑ i : Fin m, c i.succ * B (J i) (J l) = 0 := by
      intro l
      have := congrArg (fun x => B x (J l)) hc
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, map_sum,
        LinearMap.sum_apply, LinearMap.zero_apply, map_zero] at this
      rw [hwJ l] at this
      simpa using this
    have hvec : (fun i : Fin m => c i.succ) ᵥ* (Matrix.of fun i j => B (J i) (J j)) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using hpair l
    have hinj : Function.Injective fun v : Fin m → ℝ => v ᵥ* (Matrix.of fun i j => B (J i) (J j)) :=
      Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hQ))
    have hzero : (fun i : Fin m => c i.succ) = 0 := hinj (by simpa using hvec)
    -- then `c 0 • w = 0`
    have hc0 : c 0 • w = 0 := by
      have : ∑ i : Fin m, c i.succ • J i = 0 := by
        simp [Finset.sum_eq_zero_iff, funext_iff.1 hzero]
      rw [this, add_zero] at hc
      exact hc
    have hc00 : c 0 = 0 := by
      rcases smul_eq_zero.1 hc0 with h | h
      · exact h
      · exact absurd h hw0
    intro i
    refine Fin.cases hc00 (fun j => ?_) i
    exact congrFun hzero j
  have hspan : finrank ℝ (Submodule.span ℝ (Set.range F)) = m + 1 := by
    rw [finrank_span_eq_card hli]; simp
  have hle : Submodule.span ℝ (Set.range F) ≤ B.orthogonal (Submodule.span ℝ {w}) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [hF, hww]
    · simp [hF, hwJ]
  have hrank : finrank ℝ (B.orthogonal (Submodule.span ℝ {w})) = m + 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton hw0, hdim]
    omega
  have heq : Submodule.span ℝ (Set.range F) = B.orthogonal (Submodule.span ℝ {w}) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hrank])
  have hmem : u ∈ B.orthogonal (Submodule.span ℝ {w}) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    simp [hu]
  rw [← heq] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  refine ⟨fun i => c i.succ, c 0, ?_⟩
  rw [← hc, Fin.sum_univ_succ]
  simp only [hF, Fin.cons_zero, Fin.cons_succ]
  abel
/-- **`Π = C Q⁻¹ Cᵀ`**: the Gram matrix of the `P i` in terms of their pairings with the `J k`. -/
theorem gram_P_eq (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (hdim : finrank ℝ V = m + 2) (J : Fin m → V) (w : V)
    (hww : B w w = 0) (hw0 : w ≠ 0) (hwJ : ∀ i, B w (J i) = 0)
    (hQ : (Matrix.of fun i j => B (J i) (J j)).det ≠ 0) (P : Fin m → V) (hP : ∀ i, B w (P i) = 0) :
    (Matrix.of fun i j => B (P i) (P j)) =
      (Matrix.of fun i k => B (P i) (J k)) * (Matrix.of fun i j => B (J i) (J j))⁻¹ *
        (Matrix.of fun i k => B (P i) (J k))ᵀ := by
  set Q : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => B (J i) (J j) with hQdef
  have hdec : ∀ i, ∃ (a : Fin m → ℝ) (c : ℝ), P i = ∑ k, a k • J k + c • w := fun i =>
    exists_decomp_perp_null B hsymm hnd hdim J w hww hw0 hwJ hQ (P i) (hP i)
  choose a c hac using hdec
  set A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i k => a i k with hA
  have hBw : ∀ x : V, ∀ i, B (J i) w = 0 := fun x i => by rw [hsymm]; exact hwJ i
  have hCk : ∀ i k, B (P i) (J k) = (A * Q) i k := by
    intro i k
    rw [hac i]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hwJ k]
    simp [Matrix.mul_apply, hA, hQdef]
  have hCA : (Matrix.of fun i k => B (P i) (J k)) = A * Q := by
    ext i k; exact hCk i k
  have hQs : Qᵀ = Q := by
    ext i j; simp [hQdef, hsymm]
  have hPP : (Matrix.of fun i j => B (P i) (P j)) = A * Q * Aᵀ := by
    ext i j
    rw [Matrix.of_apply, hac j]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
    have h1 : B (P i) w = 0 := by rw [hsymm]; exact hP i
    rw [h1]
    simp only [hCk, mul_zero, add_zero, Matrix.mul_apply, Matrix.transpose_apply, hA, Matrix.of_apply]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  rw [hPP, hCA, Matrix.transpose_mul, hQs]
  calc A * Q * Aᵀ = A * Q * (Q⁻¹ * Q) * Aᵀ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    _ = A * Q * Q⁻¹ * Q * Aᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

end Lightlike.Penrose
