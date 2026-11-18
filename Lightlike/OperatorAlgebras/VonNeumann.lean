import Lightlike.OperatorAlgebras.Resolvent

/-!
# Von Neumann's extension theory: the closed symmetric case

For a closed symmetric densely defined operator `A` (`ClosedSymm A`): `‖(A - z) x‖ ≥ |Im z| ‖x‖`, the range of `A - z` is closed
for non-real `z`, and its orthogonal complement is the deficiency space `N_{z̄}`; hence `A` is self-adjoint iff both deficiency spaces
`N_{±i}` vanish (`isSelfAdjoint_of_deficiency_bot`). The statements follow von Neumann's theorem as stated in Bonneau, Faraut and
Valent, arXiv:quant-ph/0103153, Section 4, Theorem 1 (case `n₊ = n₋ = 0`).
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **A closed symmetric densely defined operator**. -/
structure ClosedSymm (A : H →ₗ.[ℂ] H) : Prop where
  /-- The domain is dense. -/
  dense : Dense (A.domain : Set H)
  /-- The graph is closed. -/
  closed : A.IsClosed
  /-- Symmetry. -/
  symm : ∀ x y : A.domain, ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ

/-- `⟪A x, x⟫` is real for a symmetric `A`. -/
lemma cs_inner_self_im (hA : ClosedSymm A) (x : A.domain) :
    (⟪A x, (x : H)⟫_ℂ).im = 0 := by
  have h := hA.symm x x
  have h2 : (starRingEnd ℂ) ⟪A x, (x : H)⟫_ℂ = ⟪A x, (x : H)⟫_ℂ := by
    rw [inner_conj_symm (𝕜 := ℂ)]; exact h.symm
  exact (Complex.conj_eq_iff_im.1 h2)

/-- **The lower bound of `A - z`**: `‖(A - z) x‖ ≥ |Im z| ‖x‖` on the domain of a closed symmetric `A`. -/
lemma cs_norm_sub_smul_ge (hA : ClosedSymm A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖(A x : H) - z • (x : H)‖ := by
  set u : H := (A x : H) - (z.re : ℂ) • (x : H) with hu
  have hdecomp : (A x : H) - z • (x : H) = u - ((z.im : ℂ) * Complex.I) • (x : H) := by
    rw [hu, sub_sub, ← add_smul]
    congr 2
    apply Complex.ext <;> simp
  have hw : (⟪u, (x : H)⟫_ℂ).im = 0 := by
    rw [hu, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp only [Complex.sub_im, cs_inner_self_im hA x, Complex.conj_ofReal]
    simp [← Complex.ofReal_pow]
  have key : ‖(A x : H) - z • (x : H)‖ ^ 2 = ‖u‖ ^ 2 + (z.im * ‖(x : H)‖) ^ 2 := by
    rw [hdecomp, norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
    have hre : RCLike.re (((z.im : ℂ) * Complex.I) * ⟪u, (x : H)⟫_ℂ) = 0 := by
      show (((z.im : ℂ) * Complex.I) * ⟪u, (x : H)⟫_ℂ).re = 0
      simp [Complex.mul_re, hw]
    rw [hre]
    simp only [mul_zero, sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h2 : (|z.im| * ‖(x : H)‖) ^ 2 ≤ ‖(A x : H) - z • (x : H)‖ ^ 2 := by
    rw [key, mul_pow, sq_abs]
    nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖(x : H)‖, sq_nonneg z.im]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2


/-- **The range of `A - z` is closed** for a closed symmetric `A` and non-real `z`. -/
lemma cs_range_shiftMap_closed (hA : ClosedSymm A) {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed ((LinearMap.range (shiftMap A z) : Submodule ℂ H) : Set H) := by
  have hb : 0 < |z.im| := abs_pos.2 hz
  refine IsSeqClosed.isClosed fun y₀ y hy hlim => ?_
  choose x hx using fun n => LinearMap.mem_range.1 (hy n)
  -- the preimages are Cauchy
  have hcau : CauchySeq fun n => (x n : H) := by
    have hy' : CauchySeq y₀ := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hy' ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hy' (|z.im| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := cs_norm_sub_smul_ge hA z (x m - x n)
    have h2 : shiftMap A z (x m - x n) = y₀ m - y₀ n := by rw [map_sub, hx, hx]
    rw [shiftMap_apply] at h2
    rw [h2] at h1
    have h3 : |z.im| * dist (x m : H) (x n : H) ≤ dist (y₀ m) (y₀ n) := by
      rw [dist_eq_norm, dist_eq_norm]; exact h1
    have := hN m hm n hn
    by_contra hcon
    push Not at hcon
    nlinarith
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hcau
  have hA' : Filter.Tendsto (fun n => (A (x n) : H)) Filter.atTop (nhds (y + z • x₀)) := by
    have : (fun n => (A (x n) : H)) = fun n => y₀ n + z • (x n : H) := by
      funext n
      have := hx n
      rw [shiftMap_apply] at this
      rw [← this]; abel
    rw [this]
    exact hlim.add (hx₀.const_smul z)
  have hg : ((x₀, y + z • x₀) : H × H) ∈ A.graph := by
    refine hA.closed.mem_of_tendsto (f := fun n => ((x n : H), (A (x n) : H))) (b := Filter.atTop) ?_ ?_
    · exact hx₀.prodMk_nhds hA'
    · exact Filter.Eventually.of_forall fun n => LinearPMap.mem_graph A (x n)
  obtain ⟨x', hx'1, hx'2⟩ := (LinearPMap.mem_graph_iff A).1 hg
  refine ⟨x', ?_⟩
  rw [shiftMap_apply]
  simp only at hx'1 hx'2
  rw [hx'2, hx'1]; abel


/-- **`A - z` is onto when the deficiency space at `z̄` vanishes**: the range is closed, and its orthogonal complement lies in `N_{z̄}`. -/
lemma cs_shiftMap_surjective (hA : ClosedSymm A) {z : ℂ} (hz : z.im ≠ 0)
    (hN : deficiencySpace A ((starRingEnd ℂ) z) = ⊥) : Function.Surjective (shiftMap A z) := by
  have hcl := cs_range_shiftMap_closed hA hz
  set R : Submodule ℂ H := LinearMap.range (shiftMap A z) with hR
  have hbot : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hdef : y ∈ deficiencySpace A ((starRingEnd ℂ) z) := by
      refine mem_deficiencySpace_of_forall hA.dense _ _ fun x => ?_
      have h0 := hy (shiftMap A z x) (LinearMap.mem_range_self _ x)
      rw [shiftMap_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at h0
      rw [inner_smul_left, ← inner_conj_symm (𝕜 := ℂ) y (A x : H), h0, map_mul, starRingEnd_self_apply,
        ← inner_conj_symm (𝕜 := ℂ) y (x : H)]
    rw [hN] at hdef
    simpa using hdef
  have hdense : R.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hbot
  intro y
  have hall : (R : Set H) = Set.univ := by
    have := congrArg (fun S : Submodule ℂ H => (S : Set H)) hdense
    simp only [Submodule.topologicalClosure_coe, Submodule.top_coe] at this
    rwa [hcl.closure_eq] at this
  have : y ∈ (R : Set H) := by rw [hall]; trivial
  exact LinearMap.mem_range.1 this

/-- A symmetric densely defined operator is contained in its adjoint. -/
lemma ClosedSymm.le_adjoint (hA : ClosedSymm A) : A ≤ A† := by
  refine ⟨fun x hx => ?_, ?_⟩
  · exact LinearPMap.mem_adjoint_domain_of_exists x ⟨A ⟨x, hx⟩, fun y => hA.symm ⟨x, hx⟩ y⟩
  · intro x y hxy
    refine (LinearPMap.adjoint_apply_eq hA.dense y (x₀ := (A x : H)) fun w => ?_).symm
    rw [← hxy]
    exact hA.symm x w

/-- **Von Neumann, case `n₊ = n₋ = 0`**: a closed symmetric densely defined operator whose deficiency spaces at `i` and `-i` are
trivial is self-adjoint (the converse is `deficiencySpace_of_isSelfAdjoint`). -/
theorem isSelfAdjoint_of_deficiency_bot (hA : ClosedSymm A) (h₁ : deficiencySpace A Complex.I = ⊥)
    (h₂ : deficiencySpace A (-Complex.I) = ⊥) : IsSelfAdjoint A := by
  have hsurj := cs_shiftMap_surjective hA (z := Complex.I) (by simp) (by rw [Complex.conj_I]; exact h₂)
  have hmem : ∀ y : (A†).domain, (y : H) ∈ A.domain := by
    intro y
    obtain ⟨x, hx⟩ := hsurj ((A† y : H) - Complex.I • (y : H))
    rw [shiftMap_apply] at hx
    have hxd : (x : H) ∈ (A†).domain := hA.le_adjoint.1 x.2
    have hAx : (A† ⟨(x : H), hxd⟩ : H) = A x := (hA.le_adjoint.2 (x := x) (y := ⟨(x : H), hxd⟩) rfl).symm
    have hdef : ((y : H) - (x : H)) ∈ deficiencySpace A Complex.I := by
      refine ⟨(A†).domain.sub_mem y.2 hxd, ?_⟩
      have e1 : (⟨(y : H) - (x : H), (A†).domain.sub_mem y.2 hxd⟩ : (A†).domain) = y - ⟨(x : H), hxd⟩ := rfl
      rw [e1]
      change (A†).toFun (y - ⟨(x : H), hxd⟩) = _
      rw [(A†).toFun.map_sub]
      change (A† y : H) - (A† ⟨(x : H), hxd⟩ : H) = Complex.I • ((y : H) - (x : H))
      rw [hAx, smul_sub]
      have := hx
      rw [sub_eq_iff_eq_add] at this
      rw [this]; abel
    rw [h₁] at hdef
    have : (y : H) - (x : H) = 0 := by simpa using hdef
    have hyx : (y : H) = (x : H) := sub_eq_zero.mp this
    rw [hyx]; exact x.2
  have hge : A† ≤ A := by
    refine ⟨fun y hy => hmem ⟨y, hy⟩, ?_⟩
    intro y x hyx
    have hxd : (x : H) ∈ A.domain := x.2
    have hle := hA.le_adjoint.2 (x := x) (y := ⟨(x : H), hA.le_adjoint.1 x.2⟩) rfl
    have : y = ⟨(x : H), hA.le_adjoint.1 x.2⟩ := Subtype.ext hyx
    rw [this]; exact hle.symm
  exact le_antisymm hge hA.le_adjoint

/-- A self-adjoint operator is closed symmetric and densely defined. -/
theorem ClosedSymm.of_isSelfAdjoint (hA : IsSelfAdjoint A) : ClosedSymm A :=
  ⟨hA.dense_domain, hA.isClosed, sa_symm_apply hA⟩

/-- **Von Neumann, case `n₊ = n₋ = 0`, as an equivalence**: a closed symmetric densely defined operator is self-adjoint iff its
deficiency spaces at `i` and `-i` are trivial (Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 4, Theorem 1, first case). -/
theorem isSelfAdjoint_iff_deficiency_bot (hA : ClosedSymm A) :
    IsSelfAdjoint A ↔ deficiencySpace A Complex.I = ⊥ ∧ deficiencySpace A (-Complex.I) = ⊥ :=
  ⟨fun h => ⟨deficiencySpace_of_isSelfAdjoint h (by simp), deficiencySpace_of_isSelfAdjoint h (by simp)⟩,
    fun h => isSelfAdjoint_of_deficiency_bot hA h.1 h.2⟩

end Lightlike.OperatorAlgebras
