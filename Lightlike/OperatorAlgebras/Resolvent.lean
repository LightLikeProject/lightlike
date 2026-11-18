import Lightlike.OperatorAlgebras.Deficiency
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The resolvent of a self-adjoint operator

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence).
For a self-adjoint `A` and `z` with `Im z ≠ 0`, the operator `A - z` is a bijection from the domain onto `H`
with `‖(A - z) x‖ ≥ |Im z| ‖x‖`, and its inverse `resolventCLM hA z` is a bounded operator of norm at most
`1 / |Im z|`.

Mathlib has a resolvent only in an open pull request (`LinearPMap: definition of resolvent and resolvent
identities`); this file writes the one needed here, and a later switch to the pull request's definition is
meant to be easy.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- A self-adjoint operator is symmetric. -/
lemma sa_symm_apply (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have hAA : A† = A := hA
  have := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [hAA] at this
  exact this x y

/-- `⟪A x, x⟫` is real for a self-adjoint `A`. -/
lemma sa_inner_self_im (hA : IsSelfAdjoint A) (x : A.domain) :
    (⟪A x, (x : H)⟫_ℂ).im = 0 := by
  have h := sa_symm_apply hA x x
  have h2 : (starRingEnd ℂ) ⟪A x, (x : H)⟫_ℂ = ⟪A x, (x : H)⟫_ℂ := by
    rw [inner_conj_symm (𝕜 := ℂ)]; exact h.symm
  exact (Complex.conj_eq_iff_im.1 h2)

/-- **The lower bound of `A - z`**: `‖(A - z) x‖ ≥ |Im z| ‖x‖` on the domain of a self-adjoint `A`. -/
lemma sa_norm_sub_smul_ge (hA : IsSelfAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖(A x : H) - z • (x : H)‖ := by
  set u : H := (A x : H) - (z.re : ℂ) • (x : H) with hu
  have hdecomp : (A x : H) - z • (x : H) = u - ((z.im : ℂ) * Complex.I) • (x : H) := by
    rw [hu, sub_sub, ← add_smul]
    congr 2
    apply Complex.ext <;> simp
  have hw : (⟪u, (x : H)⟫_ℂ).im = 0 := by
    rw [hu, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp only [Complex.sub_im, sa_inner_self_im hA x, Complex.conj_ofReal]
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

/-- For a densely defined `A`: if `⟪z y, x⟫ = ⟪y, A x⟫` for all `x` in the domain, `y` is in the deficiency space
at `z`. -/
lemma mem_deficiencySpace_of_forall {A : H →ₗ.[ℂ] H} (hA : Dense (A.domain : Set H)) (z : ℂ) (y : H)
    (h : ∀ x : A.domain, ⟪z • y, (x : H)⟫_ℂ = ⟪y, A x⟫_ℂ) : y ∈ deficiencySpace A z := by
  have hy : y ∈ (A†).domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨z • y, fun x => h x⟩
  exact ⟨hy, LinearPMap.adjoint_apply_eq hA ⟨y, hy⟩ fun x => h x⟩

/-- The map `x ↦ A x - z x` on the domain. -/
noncomputable def shiftMap (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

lemma shiftMap_apply (z : ℂ) (x : A.domain) : shiftMap A z x = (A x : H) - z • (x : H) := rfl

/-- **The range of `A - z` is closed** for a self-adjoint `A` and non-real `z`. -/
lemma sa_range_shiftMap_closed (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
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
    have h1 := sa_norm_sub_smul_ge hA z (x m - x n)
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
    refine hA.isClosed.mem_of_tendsto (f := fun n => ((x n : H), (A (x n) : H))) (b := Filter.atTop) ?_ ?_
    · exact hx₀.prodMk_nhds hA'
    · exact Filter.Eventually.of_forall fun n => LinearPMap.mem_graph A (x n)
  obtain ⟨x', hx'1, hx'2⟩ := (LinearPMap.mem_graph_iff A).1 hg
  refine ⟨x', ?_⟩
  rw [shiftMap_apply]
  simp only at hx'1 hx'2
  rw [hx'2, hx'1]; abel

/-- **`A - z` is surjective** for a self-adjoint `A` and non-real `z`. -/
lemma sa_shiftMap_surjective (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Surjective (shiftMap A z) := by
  have hcl := sa_range_shiftMap_closed hA hz
  set R : Submodule ℂ H := LinearMap.range (shiftMap A z) with hR
  have hbot : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hdef : y ∈ deficiencySpace A ((starRingEnd ℂ) z) := by
      refine mem_deficiencySpace_of_forall hA.dense_domain _ _ fun x => ?_
      have h0 := hy (shiftMap A z x) (LinearMap.mem_range_self _ x)
      rw [shiftMap_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at h0
      rw [inner_smul_left, ← inner_conj_symm (𝕜 := ℂ) y (A x : H), h0, map_mul, starRingEnd_self_apply,
        ← inner_conj_symm (𝕜 := ℂ) y (x : H)]
    have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    rw [deficiencySpace_of_isSelfAdjoint hA hz'] at hdef
    simpa using hdef
  have hdense : R.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hbot
  intro y
  have hall : (R : Set H) = Set.univ := by
    have := congrArg (fun S : Submodule ℂ H => (S : Set H)) hdense
    simp only [Submodule.topologicalClosure_coe, Submodule.top_coe] at this
    rwa [hcl.closure_eq] at this
  have : y ∈ (R : Set H) := by rw [hall]; trivial
  exact LinearMap.mem_range.1 this

lemma sa_shiftMap_injective (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := sa_norm_sub_smul_ge hA z x
  rw [← shiftMap_apply, hx, norm_zero] at h
  have : ‖(x : H)‖ = 0 := by
    have hb : 0 < |z.im| := abs_pos.2 hz
    nlinarith [norm_nonneg (x : H)]
  exact Subtype.ext (norm_eq_zero.1 this)

end Lightlike.OperatorAlgebras
