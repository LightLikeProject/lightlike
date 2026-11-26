import Lightlike.OperatorAlgebras.Spectral.Unbounded.Spectrum

/-!
# Solutions of `(1 + D²) x = y` for a self-adjoint `D`

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

For a self-adjoint (unbounded) `D` and `y ∈ 𝓗` a *solution* is `x ∈ Dom D` with
`⟪x, z⟫ + ⟪D x, D z⟫ = ⟪y, z⟫` for all `z ∈ Dom D`, i.e. `x = (1 + D²)⁻¹ y` in the weak sense.
The form only involves `‖D z‖`-data, so it does not change if `D` is replaced by `U D` with `U`
isometric; this is the lever of the uniqueness theorem for the modular objects (next file),
which avoids any spectral-theorem input.

## Main results

* `tot` — total version of a `LinearPMap` (`0` outside the domain).
* `IsSol D y x` — `x` solves the form equation for `y`.
* `exists_isSol` — for self-adjoint `D` every `y` has a solution (von Neumann: `D ± i` onto).
* `IsSol.unique`, `IsSol.add`, `IsSol.smul` — uniqueness and linearity of the solution map.
* `IsSol.apply_mem` — `D x ∈ Dom D` and `D (D x) = y - x`.
* `IsSol.norm_le`, `IsSol.norm_apply_le` — `‖x‖ ≤ ‖y‖` and `‖D x‖ ≤ ‖y‖`.
-/

open Filter Topology Complex
open scoped LinearPMap InnerProductSpace

set_option linter.unusedSectionVars false

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

open Lightlike.OperatorAlgebras.Spectral.Unbounded

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- The total version of a partially defined operator: `D x` on the domain, `0` outside. -/
noncomputable def tot (D : 𝓗 →ₗ.[ℂ] 𝓗) (x : 𝓗) : 𝓗 :=
  open scoped Classical in
  if h : x ∈ D.domain then D ⟨x, h⟩ else 0

section
variable (D : 𝓗 →ₗ.[ℂ] 𝓗)

lemma tot_of_mem {x : 𝓗} (hx : x ∈ D.domain) : tot D x = D ⟨x, hx⟩ := by
  simp [tot, hx]

lemma tot_add {x y : 𝓗} (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    tot D (x + y) = tot D x + tot D y := by
  rw [tot_of_mem D (D.domain.add_mem hx hy), tot_of_mem D hx, tot_of_mem D hy]
  exact D.map_add ⟨x, hx⟩ ⟨y, hy⟩

lemma tot_smul (c : ℂ) {x : 𝓗} (hx : x ∈ D.domain) : tot D (c • x) = c • tot D x := by
  rw [tot_of_mem D (D.domain.smul_mem c hx), tot_of_mem D hx]
  exact D.map_smul c ⟨x, hx⟩

lemma tot_sub {x y : 𝓗} (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    tot D (x - y) = tot D x - tot D y := by
  have h := tot_add D hx (D.domain.neg_mem hy)
  have h2 := tot_smul D (-1) hy
  simp only [neg_smul, one_smul] at h2
  rw [sub_eq_add_neg, h, h2, sub_eq_add_neg]

end

/-- A vector orthogonal to a dense set is zero. -/
lemma eq_zero_of_dense {S : Set 𝓗} (hS : Dense S) {v : 𝓗} (h : ∀ x ∈ S, ⟪x, v⟫_ℂ = 0) :
    v = 0 := by
  have hc : closure S ⊆ {x | ⟪x, v⟫_ℂ = 0} :=
    closure_minimal h (isClosed_eq (by fun_prop) continuous_const)
  rw [hS.closure_eq] at hc
  have := hc (Set.mem_univ v)
  simpa using this

variable {D : 𝓗 →ₗ.[ℂ] 𝓗}

/-- A self-adjoint operator is symmetric: `⟪D x, y⟫ = ⟪x, D y⟫` on the domain. -/
lemma sa_inner (hD : IsSelfAdjoint D) {x y : 𝓗} (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    ⟪tot D x, y⟫_ℂ = ⟪x, tot D y⟫_ℂ := by
  have hT : HasDenseDomain D := hD.dense_domain
  have hsym : IsSymmetric D :=
    (isSymmetric_iff_le_adjoint hT).mpr (LinearPMap.isSelfAdjoint_def.mp hD).ge
  rw [tot_of_mem D hx, tot_of_mem D hy]
  exact (hsym ⟨x, hx⟩ ⟨y, hy⟩).symm

/-- The self-adjointness criterion: if `⟪D x, z⟫ = ⟪x, w⟫` for all `x ∈ Dom D`, then
`z ∈ Dom D` and `D z = w`. -/
lemma mem_of_inner (hD : IsSelfAdjoint D) {z w : 𝓗}
    (h : ∀ x ∈ D.domain, ⟪tot D x, z⟫_ℂ = ⟪x, w⟫_ℂ) : z ∈ D.domain ∧ tot D z = w := by
  have hadj : D† = D := LinearPMap.isSelfAdjoint_def.mp hD
  have hz : z ∈ D†.domain := by
    refine LinearPMap.mem_adjoint_domain_of_exists z ⟨w, fun x => ?_⟩
    have := h x x.2
    rw [tot_of_mem D x.2] at this
    rw [← inner_conj_symm z, ← inner_conj_symm w]
    exact congrArg (starRingEnd ℂ) this.symm
  have hz' : z ∈ D.domain := by
    have := congrArg LinearPMap.domain hadj
    rw [← this]; exact hz
  refine ⟨hz', ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_dense hD.dense_domain fun x hx => ?_
  rw [inner_sub_right, ← sa_inner hD hx hz', h x hx, sub_self]

/-- `x` solves the weak form of `(1 + D²) x = y`. -/
def IsSol (D : 𝓗 →ₗ.[ℂ] 𝓗) (y x : 𝓗) : Prop :=
  x ∈ D.domain ∧ ∀ z ∈ D.domain, ⟪x, z⟫_ℂ + ⟪tot D x, tot D z⟫_ℂ = ⟪y, z⟫_ℂ

/-- A solution has `D x ∈ Dom D` and `D (D x) = y - x`. -/
lemma IsSol.apply_mem (hD : IsSelfAdjoint D) {y x : 𝓗} (h : IsSol D y x) :
    tot D x ∈ D.domain ∧ tot D (tot D x) = y - x := by
  refine mem_of_inner hD fun z hz => ?_
  have e : ⟪tot D x, tot D z⟫_ℂ = ⟪y, z⟫_ℂ - ⟪x, z⟫_ℂ := by
    rw [← h.2 z hz]; ring
  have e2 : ⟪tot D z, tot D x⟫_ℂ = starRingEnd ℂ ⟪tot D x, tot D z⟫_ℂ :=
    (inner_conj_symm (tot D z) (tot D x)).symm
  rw [e2, e, map_sub, inner_conj_symm, inner_conj_symm, inner_sub_right]

/-- The solution is unique. -/
lemma IsSol.unique {y x x' : 𝓗} (h : IsSol D y x) (h' : IsSol D y x') : x = x' := by
  have hd : x - x' ∈ D.domain := D.domain.sub_mem h.1 h'.1
  have e := h.2 _ hd
  have e' := h'.2 _ hd
  rw [tot_sub D h.1 h'.1] at e e'
  have e0 : ⟪x - x', x - x'⟫_ℂ + ⟪tot D x - tot D x', tot D x - tot D x'⟫_ℂ = 0 := by
    have := sub_eq_zero.mpr (e.trans e'.symm)
    rw [← this]
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e0
  have h1 : ‖x - x'‖ ^ 2 = 0 := by
    have e1 : ((‖x - x'‖ ^ 2 + ‖tot D x - tot D x'‖ ^ 2 : ℝ) : ℂ) = 0 := by
      push_cast; exact e0
    have := Complex.ofReal_eq_zero.mp e1
    nlinarith [sq_nonneg ‖tot D x - tot D x'‖, sq_nonneg ‖x - x'‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1))

lemma IsSol.add {y₁ y₂ x₁ x₂ : 𝓗} (h₁ : IsSol D y₁ x₁) (h₂ : IsSol D y₂ x₂) :
    IsSol D (y₁ + y₂) (x₁ + x₂) := by
  refine ⟨D.domain.add_mem h₁.1 h₂.1, fun z hz => ?_⟩
  rw [tot_add D h₁.1 h₂.1, inner_add_left, inner_add_left, inner_add_left]
  have a := h₁.2 z hz
  have b := h₂.2 z hz
  linear_combination a + b

lemma IsSol.smul (c : ℂ) {y x : 𝓗} (h : IsSol D y x) : IsSol D (c • y) (c • x) := by
  refine ⟨D.domain.smul_mem c h.1, fun z hz => ?_⟩
  rw [tot_smul D c h.1, inner_smul_left, inner_smul_left, inner_smul_left]
  have a := h.2 z hz
  linear_combination (starRingEnd ℂ) c * a

/-- Norm bounds: `‖x‖² + ‖D x‖² ≤ ‖y‖ ‖x‖`, hence `‖x‖ ≤ ‖y‖` and `‖D x‖ ≤ ‖y‖`. -/
lemma IsSol.norm_sq_le {y x : 𝓗} (h : IsSol D y x) :
    ‖x‖ ^ 2 + ‖tot D x‖ ^ 2 ≤ ‖y‖ * ‖x‖ := by
  have e := h.2 x h.1
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have e1 : ((‖x‖ ^ 2 + ‖tot D x‖ ^ 2 : ℝ) : ℂ) = ⟪y, x⟫_ℂ := by
    push_cast; exact e
  have h1 := congrArg Complex.re e1
  rw [Complex.ofReal_re] at h1
  rw [h1]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

lemma IsSol.norm_le {y x : 𝓗} (h : IsSol D y x) : ‖x‖ ≤ ‖y‖ := by
  have := h.norm_sq_le
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg ‖tot D x‖]

lemma IsSol.norm_apply_le {y x : 𝓗} (h : IsSol D y x) : ‖tot D x‖ ≤ ‖y‖ := by
  have h1 := h.norm_sq_le
  have h2 := h.norm_le
  have : ‖tot D x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg ‖x‖]
  exact le_of_sq_le_sq this (norm_nonneg _) |>.trans_eq rfl

/-- For self-adjoint `D` every `y` has a solution: `D ± i` are onto. -/
lemma exists_isSol (hD : IsSelfAdjoint D) (y : 𝓗) : ∃ x, IsSol D y x := by
  obtain ⟨B2, hB2⟩ := mem_pmapResolventSet_of_im_ne_zero hD (lam := -Complex.I) (by simp)
  obtain ⟨B1, hB1⟩ := mem_pmapResolventSet_of_im_ne_zero hD (lam := Complex.I) (by simp)
  have hw : B2 y ∈ D.domain := hB2.mem_domain y
  have ew : D ⟨B2 y, hw⟩ - (-Complex.I) • B2 y = y := hB2.rightInverse y
  have hx : B1 (B2 y) ∈ D.domain := hB1.mem_domain (B2 y)
  have ex : D ⟨B1 (B2 y), hx⟩ - Complex.I • B1 (B2 y) = B2 y := hB1.rightInverse (B2 y)
  generalize B2 y = w at hw ew hx ex
  generalize B1 w = x at hx ex
  have ew' : tot D w = y - Complex.I • w := by
    rw [tot_of_mem D hw]
    rw [neg_smul, sub_neg_eq_add] at ew
    exact eq_sub_of_add_eq ew
  have ex' : tot D x = w + Complex.I • x := by
    rw [tot_of_mem D hx]
    exact sub_eq_iff_eq_add.mp ex
  have hDx : tot D x ∈ D.domain := by
    rw [ex']; exact D.domain.add_mem hw (D.domain.smul_mem _ hx)
  have DDx : tot D (tot D x) = y - x := by
    rw [ex', tot_add D hw (D.domain.smul_mem _ hx), tot_smul D Complex.I hx, ew', ex',
      smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  refine ⟨x, hx, fun z hz => ?_⟩
  have := sa_inner hD hDx hz
  rw [← this, DDx, inner_sub_left]
  ring

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.add := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.apply_mem := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.apply_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.norm_apply_le := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.norm_apply_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.norm_le := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.norm_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.norm_sq_le := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.norm_sq_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.smul := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.IsSol.unique := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.IsSol.unique
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.eq_zero_of_dense := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.eq_zero_of_dense
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.exists_isSol := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.exists_isSol
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.mem_of_inner := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.mem_of_inner
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.sa_inner := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.sa_inner
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.tot := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.tot
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.tot_add := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.tot_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.tot_of_mem := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.tot_of_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.tot_smul := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.tot_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.tot_sub := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.tot_sub
