import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Conformal Killing fields of a flat metric (G1-013)

Gourgoulhon (gr-qc/0703035, Appendix B.1): the conformal Killing operator `(Lv)ᵢⱼ = Dᵢvⱼ + Dⱼvᵢ - (2/3) Dₖvᵏ γᵢⱼ` (B.1),
and "a vector field which obeys `(L̃v)ᵢⱼ = 0` is called a conformal Killing vector. It is the generator of some conformal
isometry ... every Killing vector is a conformal Killing vector" (B.8); for the Euclidean space the conformal isometries are
"the isometries (translations, rotations) augmented by the homotheties".

On a real vector space `V` with a constant symmetric bilinear form `B` (a flat metric of any signature; namespace `Flat`,
the manifold definition being `Lightlike.IsConformalKillingAt` in `ConformalKillingField.lean`), a field `X` is
**conformal Killing** at `y` with factor `σ` when `B(DX(y) u, w) + B(u, DX(y) w) = 2σ B(u, w)` (`IsConformalKillingAt`):

* `isConformalKillingAt_of_killing`: a Killing field (`σ = 0`) is conformal Killing;
* `isConformalKillingAt_dilation`: the homothety `y ↦ y` is conformal Killing with `σ = 1`;
* `isConformalKillingAt_special`: the special conformal field `y ↦ B(y, y) b - 2 B(b, y) y` is conformal Killing with
  `σ = -2 B(b, y)`, for every `b`;
* `isConformalKillingAt_add`, `isConformalKillingAt_smul`: they form a vector space (factors add).

* `conformalKilling_classification`: **in dimension at least three, every `C³` field that is conformal Killing at every point
  is `X(y) = c + A y + specialConformal B b y` with `A` conformal** (`B(Au, w) + B(u, Aw) = 2σ(0) B(u, w)`, so `A` is a
  multiple of the identity plus a `B`-skew map): translations, rotations, the homothety and the special conformal fields, the
  `(n + 1)(n + 2)/2` conformal Killing fields (Gourgoulhon's "maximum dimension of ker L̃ is 10" for `n = 3`). The proof
  differentiates the equation twice: the second derivative of `X` is fixed by `Dσ` (`ck_second_formula`), and the symmetry of
  the third derivative forces `D²σ = 0` when `n ≥ 3` (`hessian_eq_zero`, in an orthogonal basis of `B`).

**Limits.** Coordinates on a vector space with a constant (flat) metric.
-/

open Set

namespace Lightlike
namespace Flat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `X` is a **conformal Killing field** of the flat metric `B` at `y`, with conformal factor `σ`. -/
def IsConformalKillingAt (B : V →L[ℝ] V →L[ℝ] ℝ) (X : V → V) (σ : ℝ) (y : V) : Prop :=
  ∀ u w : V, B (fderiv ℝ X y u) w + B u (fderiv ℝ X y w) = 2 * σ * B u w

/-- A Killing field of the flat metric is conformal Killing with conformal factor `0`. -/
theorem isConformalKillingAt_of_killing {B : V →L[ℝ] V →L[ℝ] ℝ} {X : V → V} {y : V}
    (h : ∀ u w : V, B (fderiv ℝ X y u) w + B u (fderiv ℝ X y w) = 0) : IsConformalKillingAt B X 0 y := by
  intro u w; rw [h]; ring

/-- The sum of two conformal Killing fields is conformal Killing, with the sum of the conformal factors. -/
theorem isConformalKillingAt_add {B : V →L[ℝ] V →L[ℝ] ℝ} {X Y : V → V} {σ τ : ℝ} {y : V}
    (hX : DifferentiableAt ℝ X y) (hY : DifferentiableAt ℝ Y y)
    (h1 : IsConformalKillingAt B X σ y) (h2 : IsConformalKillingAt B Y τ y) :
    IsConformalKillingAt B (X + Y) (σ + τ) y := by
  intro u w
  rw [fderiv_add hX hY]
  simp only [add_apply, map_add]
  linarith [h1 u w, h2 u w]

/-- A constant multiple of a conformal Killing field is conformal Killing, with the multiplied conformal factor. -/
theorem isConformalKillingAt_smul {B : V →L[ℝ] V →L[ℝ] ℝ} {X : V → V} {σ : ℝ} {y : V} (c : ℝ)
    (hX : DifferentiableAt ℝ X y) (h : IsConformalKillingAt B X σ y) :
    IsConformalKillingAt B (c • X) (c * σ) y := by
  intro u w
  rw [fderiv_const_smul hX]
  simp only [smul_apply, map_smul, smul_eq_mul]
  have := h u w
  linear_combination c * this

/-- **The homothety is conformal Killing** with `σ = 1`. -/
theorem isConformalKillingAt_dilation (B : V →L[ℝ] V →L[ℝ] ℝ) (y : V) : IsConformalKillingAt B id 1 y := by
  intro u w
  rw [fderiv_id]
  simp only [ContinuousLinearMap.id_apply]
  ring

/-- The special conformal field `y ↦ B(y, y) b - 2 B(b, y) y`. -/
noncomputable def specialConformal (B : V →L[ℝ] V →L[ℝ] ℝ) (b : V) (y : V) : V := B y y • b - (2 * B b y) • y

/-- Its derivative: `u ↦ (B(y, u) + B(u, y)) b - 2 B(b, u) y - 2 B(b, y) u`. -/
theorem hasFDerivAt_specialConformal (B : V →L[ℝ] V →L[ℝ] ℝ) (b y : V) :
    HasFDerivAt (specialConformal B b) ((B y + B.flip y).smulRight b -
      ((2 : ℝ) • B b).smulRight y - (2 * B b y) • ContinuousLinearMap.id ℝ V) y := by
  have hq : HasFDerivAt (fun z => B z z) (B y + B.flip y) y := by
    have := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
    convert this using 1
    all_goals rfl
  have h1 := hq.smul_const b
  have hl : HasFDerivAt (fun z => 2 * B b z) ((2 : ℝ) • B b) y := by
    simpa using ((B b).hasFDerivAt (x := y)).const_mul 2
  have h2 := hl.smul (hasFDerivAt_id y)
  have := h1.sub h2
  convert this using 1
  all_goals first
    | (funext z; simp [specialConformal])
    | (ext u; simp; abel)

/-- **The special conformal fields are conformal Killing**, `σ = -2 B(b, y)`, for a symmetric `B`. -/
theorem isConformalKillingAt_special (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u w, B u w = B w u) (b y : V) :
    IsConformalKillingAt B (specialConformal B b) (-2 * B b y) y := by
  intro u w
  rw [(hasFDerivAt_specialConformal B b y).fderiv]
  simp only [sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
  rw [hB u y, hB w y, hB u b]
  ring

/-! ## The classification in dimension at least three: the algebra -/

/-- The second derivative of a conformal Killing field is fixed by the derivative of the factor: if `T(v, u, w)` is
symmetric in `v, u` and `T(v, u, w) + T(v, w, u) = 2 s(v) B(u, w)`, then
`T(v, u, w) = s(v) B(u, w) + s(u) B(v, w) - s(w) B(u, v)`. -/
theorem ck_second_formula {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : ∀ u w, B u w = B w u) {T : V → V → V → ℝ} {s : V → ℝ}
    (hT : ∀ v u w, T v u w = T u v w) (h : ∀ v u w, T v u w + T v w u = 2 * s v * B u w) (v u w : V) :
    T v u w = s v * B u w + s u * B v w - s w * B u v := by
  have h1 := h v u w
  have h2 := h u v w
  have h3 := h w v u
  have e1 := hT v w u
  have e2 := hT u w v
  have e3 := hT u v w
  rw [hB v u] at h3
  linarith

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem exists_ne_two {m : ℕ} (hm : 3 ≤ m) (k l : Fin m) : ∃ j, j ≠ k ∧ j ≠ l := by
  by_contra hcon
  push Not at hcon
  have : (Finset.univ : Finset (Fin m)) ⊆ {k, l} := fun j _ => by
    by_cases hj : j = k
    · simp [hj]
    · simp [hcon j hj]
  have := Finset.card_le_card this
  simp only [Finset.card_univ, Fintype.card_fin] at this
  have := this.trans (Finset.card_insert_le k {l})
  simp at this; omega

/-- **The Hessian identity forces zero in dimension at least three.** If `B` is symmetric and nondegenerate, `H` is
symmetric and `H(z, u) B(v, w) - H(z, w) B(u, v) = H(v, u) B(z, w) - H(v, w) B(u, z)`, then `H = 0`. -/
theorem hessian_eq_zero [FiniteDimensional ℝ V] (hdim : 3 ≤ Module.finrank ℝ V) {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : ∀ u w, B u w = B w u) (hnd : B.toBilinForm.Nondegenerate) {H : V →L[ℝ] V →L[ℝ] ℝ}
    (hid : ∀ z u v w, H z u * B v w - H z w * B u v = H v u * B z w - H v w * B u z) : H = 0 := by
  have hsymm : LinearMap.IsSymm B.toBilinForm := ⟨fun u w => by simpa using hB u w⟩
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hd : ∀ i, B (e i) (e i) ≠ 0 := fun i =>
    LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hnd i
  have ho : ∀ i j, i ≠ j → B (e i) (e j) = 0 := fun i j hij => he hij
  -- `H(e_k, e_l) d_j = -H(e_j, e_j) B(e_l, e_k)` for `j ∉ {k, l}`
  have key : ∀ k l j, j ≠ k → j ≠ l → H (e k) (e l) * B (e j) (e j) = -(H (e j) (e j) * B (e l) (e k)) := by
    intro k l j hjk hjl
    have := hid (e k) (e l) (e j) (e j)
    rw [ho l j (Ne.symm hjl), ho k j (Ne.symm hjk)] at this
    linarith
  have hkl : ∀ k l, H (e k) (e l) = 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      obtain ⟨j, hjk, -⟩ := exists_ne_two hdim k k
      obtain ⟨j', hj'k, hj'j⟩ := exists_ne_two hdim k j
      have e1 := key k k j hjk hjk
      have e2 := key k k j' hj'k hj'k
      have e3 := key j j j' hj'j hj'j
      have : H (e k) (e k) * (2 * B (e j) (e j) * B (e j') (e j')) = 0 := by
        linear_combination B (e j') (e j') * e1 + B (e j) (e j) * e2 - B (e k) (e k) * e3
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exfalso
        have := mul_ne_zero (mul_ne_zero two_ne_zero (hd j)) (hd j')
        exact this h
    · obtain ⟨j, hjk, hjl⟩ := exists_ne_two hdim k l
      have := key k l j hjk hjl
      rw [ho l k (Ne.symm hkl), mul_zero, neg_zero] at this
      exact (mul_eq_zero.1 this).resolve_right (hd j)
  ext z u
  calc H z u = H (∑ i, e.repr z i • e i) (∑ j, e.repr u j • e j) := by rw [e.sum_repr, e.sum_repr]
    _ = 0 := by
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, hkl, mul_zero,
        Finset.sum_const_zero]
    _ = _ := rfl

/-! ## The classification in dimension at least three: the analysis -/

section Classification

variable [FiniteDimensional ℝ V]

/-- A nondegenerate symmetric form has a non-null vector. -/
theorem exists_nonnull {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : ∀ u w, B u w = B w u) (hnd : B.toBilinForm.Nondegenerate)
    (hdim : 0 < Module.finrank ℝ V) : ∃ u₀ : V, B u₀ u₀ ≠ 0 := by
  have hsymm : LinearMap.IsSymm B.toBilinForm := ⟨fun u w => by simpa using hB u w⟩
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  exact ⟨e ⟨0, hdim⟩, LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hnd _⟩

/-- The Riesz vector of a linear form for a nondegenerate form: `B(b, w) = s(w)`. -/
theorem exists_riesz {B : V →L[ℝ] V →L[ℝ] ℝ} (hnd : B.toBilinForm.Nondegenerate) (s : V →L[ℝ] ℝ) :
    ∃ b : V, ∀ w, B b w = s w := by
  obtain ⟨b, hb⟩ := (B.toBilinForm.toDual hnd).surjective s.toLinearMap
  refine ⟨b, fun w => ?_⟩
  have := congrArg (fun f : Module.Dual ℝ V => f w) hb
  simpa [LinearMap.BilinForm.toDual_def] using this

omit [FiniteDimensional ℝ V] in
/-- Two vectors with the same pairings are equal. -/
theorem eq_of_pairing {B : V →L[ℝ] V →L[ℝ] ℝ} (hnd : B.toBilinForm.Nondegenerate) {a a' : V}
    (h : ∀ w, B a w = B a' w) : a = a' := by
  have := hnd.1 (a - a') fun w => by simp [h w]
  exact sub_eq_zero.1 this

omit [FiniteDimensional ℝ V] in
/-- Differentiating a vanishing pairing: if `B(P y, w) + B(u, Q y) = 2 σ(y) c` for all `y`, then the derivatives satisfy
`B(P' v, w) + B(u, Q' v) = 2 σ'(v) c`. -/
theorem pairing_deriv {B : V →L[ℝ] V →L[ℝ] ℝ} {P Q : V → V} {σ : V → ℝ} {P' Q' : V →L[ℝ] V} {σ' : V →L[ℝ] ℝ}
    {y : V} (hP : HasFDerivAt P P' y) (hQ : HasFDerivAt Q Q' y) (hσ : HasFDerivAt σ σ' y) (u w : V) (c : ℝ)
    (h : ∀ y', B (P y') w + B u (Q y') = 2 * σ y' * c) (v : V) :
    B (P' v) w + B u (Q' v) = 2 * σ' v * c := by
  have h1 : HasFDerivAt (fun y' => B (P y') w + B u (Q y')) ((B.flip w).comp P' + (B u).comp Q') y :=
    ((B.flip w).hasFDerivAt.comp y hP).add ((B u).hasFDerivAt.comp y hQ)
  have h2 : HasFDerivAt (fun y' => 2 * σ y' * c) ((2 * c) • σ') y := by
    have := (hσ.const_mul 2).mul_const c
    convert this using 1
    ext v; simp; ring
  have heq : (fun y' => B (P y') w + B u (Q y')) = fun y' => 2 * σ y' * c := funext h
  rw [heq] at h1
  have := congrArg (fun L : V →L[ℝ] ℝ => L v) (h1.unique h2)
  simp at this
  linarith

/-- **The conformal Killing fields of a flat metric in dimension at least three**: a `C³` field that is conformal Killing at
every point is `X(y) = c + A y + specialConformal B b y` with `A` conformal, `B(Au, w) + B(u, Aw) = 2σ(0) B(u, w)`. -/
theorem conformalKilling_classification (hdim : 3 ≤ Module.finrank ℝ V) {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : ∀ u w, B u w = B w u) (hnd : B.toBilinForm.Nondegenerate) {X : V → V} (hX : ContDiff ℝ 3 X)
    {σ : V → ℝ} (hck : ∀ y, IsConformalKillingAt B X (σ y) y) :
    ∃ (c b : V) (A : V →L[ℝ] V), (∀ u w, B (A u) w + B u (A w) = 2 * σ 0 * B u w) ∧
      ∀ y, X y = c + A y + specialConformal B b y := by
  obtain ⟨u₀, hu₀⟩ := exists_nonnull hB hnd (by omega)
  have hDX : ContDiff ℝ 2 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  have hσeq : σ = fun y => (B (fderiv ℝ X y u₀) u₀ + B u₀ (fderiv ℝ X y u₀)) / (2 * B u₀ u₀) := by
    funext y; have := hck y u₀ u₀; field_simp; linarith
  have hσ : ContDiff ℝ 2 σ := by
    rw [hσeq]
    have h1 : ContDiff ℝ 2 (fun y => fderiv ℝ X y u₀) := hDX.clm_apply contDiff_const
    exact (((B.flip u₀).contDiff.comp h1).add ((B u₀).contDiff.comp h1)).div_const _
  set D2 : V → V →L[ℝ] V →L[ℝ] V := fun y => fderiv ℝ (fderiv ℝ X) y
  have hD2 : ∀ y, HasFDerivAt (fderiv ℝ X) (D2 y) y := fun y =>
    ((hDX.differentiable (by norm_num)) y).hasFDerivAt
  have hD2sym : ∀ y v u, D2 y v u = D2 y u v := fun y v u =>
    (hX.contDiffAt.isSymmSndFDerivAt (by simp; exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))) v u
  have hσd : ∀ y, HasFDerivAt σ (fderiv ℝ σ y) y := fun y => ((hσ.differentiable (by norm_num)) y).hasFDerivAt
  -- the first derivative of the conformal Killing equation
  have hT : ∀ y v u w, B (D2 y v u) w = fderiv ℝ σ y v * B u w + fderiv ℝ σ y u * B v w - fderiv ℝ σ y w * B u v := by
    intro y
    refine ck_second_formula hB (T := fun v u w => B (D2 y v u) w) (fun v u w => by simp only [hD2sym y v u]) ?_
    intro v u w
    have hPu : HasFDerivAt (fun y' => fderiv ℝ X y' u) ((D2 y).flip u) y := by
      have := (hD2 y).clm_apply (hasFDerivAt_const u y)
      simpa using this
    have hPw : HasFDerivAt (fun y' => fderiv ℝ X y' w) ((D2 y).flip w) y := by
      have := (hD2 y).clm_apply (hasFDerivAt_const w y)
      simpa using this
    have h' := pairing_deriv hPu hPw (hσd y) u w (B u w) (fun y' => hck y' u w) v
    simp only [ContinuousLinearMap.flip_apply] at h'
    rw [hB u (D2 y v w)] at h'
    exact h'
  -- the second derivative: the Hessian of `σ` vanishes
  have hDσ : ContDiff ℝ 1 (fderiv ℝ σ) := hσ.fderiv_right (by norm_num)
  have hD2c : ContDiff ℝ 1 D2 := hDX.fderiv_right (by norm_num)
  have hHd : ∀ y, HasFDerivAt (fderiv ℝ σ) (fderiv ℝ (fderiv ℝ σ) y) y := fun y =>
    ((hDσ.differentiable one_ne_zero) y).hasFDerivAt
  have hD3 : ∀ y, HasFDerivAt D2 (fderiv ℝ D2 y) y := fun y => ((hD2c.differentiable one_ne_zero) y).hasFDerivAt
  have hHsym : ∀ y z v, fderiv ℝ (fderiv ℝ σ) y z v = fderiv ℝ (fderiv ℝ σ) y v z := fun y z v =>
    (hσ.contDiffAt.isSymmSndFDerivAt (by simp)) z v
  have hD3sym : ∀ y z v, fderiv ℝ D2 y z v = fderiv ℝ D2 y v z := fun y z v =>
    (hDX.contDiffAt.isSymmSndFDerivAt (by simp)) z v
  have key3 : ∀ y z v u w, B (fderiv ℝ D2 y z v u) w =
      fderiv ℝ (fderiv ℝ σ) y z v * B u w + fderiv ℝ (fderiv ℝ σ) y z u * B v w -
        fderiv ℝ (fderiv ℝ σ) y z w * B u v := by
    intro y z v u w
    have hL : HasFDerivAt (fun y' => B (D2 y' v u) w) ((B.flip w).comp (((fderiv ℝ D2 y).flip v).flip u)) y := by
      have := ((B.flip w).hasFDerivAt).comp y (((hD3 y).clm_apply (hasFDerivAt_const v y)).clm_apply
        (hasFDerivAt_const u y))
      simpa [Function.comp_def] using this
    have hsv := (hHd y).clm_apply (hasFDerivAt_const v y)
    have hsu := (hHd y).clm_apply (hasFDerivAt_const u y)
    have hsw := (hHd y).clm_apply (hasFDerivAt_const w y)
    have hR := ((hsv.mul_const (B u w)).add (hsu.mul_const (B v w))).sub (hsw.mul_const (B u v))
    have heq : (fun y' => B (D2 y' v u) w) = fun y' => fderiv ℝ σ y' v * B u w + fderiv ℝ σ y' u * B v w -
        fderiv ℝ σ y' w * B u v := funext fun y' => hT y' v u w
    rw [heq] at hL
    have := congrArg (fun L : V →L[ℝ] ℝ => L z) (hL.unique hR)
    simp at this
    linarith
  have hH0 : ∀ y, fderiv ℝ (fderiv ℝ σ) y = 0 := by
    intro y
    refine hessian_eq_zero hdim hB hnd fun z u v w => ?_
    have h1 := key3 y z v u w
    have h2 := key3 y v z u w
    rw [hD3sym y z v, hHsym y z v] at h1
    linarith
  -- `σ'` is constant, with Riesz vector `b₀`
  have hs : ∀ y, fderiv ℝ σ y = fderiv ℝ σ 0 := fun y =>
    is_const_of_fderiv_eq_zero (hDσ.differentiable one_ne_zero) hH0 y 0
  set s₀ := fderiv ℝ σ 0
  obtain ⟨b₀, hb₀⟩ := exists_riesz hnd s₀
  have hD2f : ∀ y v u, D2 y v u = s₀ v • u + s₀ u • v - B u v • b₀ := by
    intro y v u
    refine eq_of_pairing hnd fun w => ?_
    rw [hT y v u w, hs y]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, add_apply, sub_apply, smul_apply, hb₀]
    ring
  -- first integration: `DX(y) v = DX(0) v + s₀(y) v + s₀(v) y - B(y, v) b₀`
  set A := fderiv ℝ X 0
  have hDXf : ∀ y v, fderiv ℝ X y v = A v + s₀ y • v + s₀ v • y - B y v • b₀ := by
    intro y v
    set F : V → V := fun y => fderiv ℝ X y v - (s₀ y • v + s₀ v • y - B y v • b₀)
    have hF : ∀ y, HasFDerivAt F ((D2 y).flip v - (s₀.smulRight v + s₀ v • ContinuousLinearMap.id ℝ V -
        (B.flip v).smulRight b₀)) y := by
      intro y
      have h1 : HasFDerivAt (fun y => fderiv ℝ X y v) ((D2 y).flip v) y := by
        have := (hD2 y).clm_apply (hasFDerivAt_const v y)
        simpa using this
      have h2 : HasFDerivAt (fun y => s₀ y • v + s₀ v • y - B y v • b₀)
          (s₀.smulRight v + s₀ v • ContinuousLinearMap.id ℝ V - (B.flip v).smulRight b₀) y := by
        have := ((s₀.smulRight v).hasFDerivAt (x := y) |>.add
          ((s₀ v • ContinuousLinearMap.id ℝ V).hasFDerivAt (x := y))).sub
          (((B.flip v).smulRight b₀).hasFDerivAt (x := y))
        convert this using 1
        all_goals rfl
      exact h1.sub h2
    have hF0 : ∀ y, fderiv ℝ F y = 0 := by
      intro y
      rw [(hF y).fderiv]
      ext z
      simp only [sub_apply, add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
        smul_apply, ContinuousLinearMap.id_apply, zero_apply, hD2f, hB v z]
      abel
    have := is_const_of_fderiv_eq_zero (fun y => (hF y).differentiableAt) hF0 y 0
    simp only [F, map_zero, zero_smul, smul_zero, zero_apply, add_zero, sub_zero, sub_self] at this
    set E := s₀ y • v + s₀ v • y - B y v • b₀
    calc fderiv ℝ X y v = (fderiv ℝ X y v - E) + E := by abel
      _ = A v + E := by rw [this]
      _ = _ := by simp only [E]; abel
  -- second integration
  set G : V → V := fun y => X y - (X 0 + A y + s₀ y • y - (1 / 2 : ℝ) • (B y y • b₀))
  have hG : ∀ y, HasFDerivAt G (fderiv ℝ X y - (A + (s₀ y • ContinuousLinearMap.id ℝ V + s₀.smulRight y) -
      (1 / 2 : ℝ) • (B y + B.flip y).smulRight b₀)) y := by
    intro y
    have h1 := ((hX.differentiable (by norm_num)) y).hasFDerivAt
    have hq : HasFDerivAt (fun z => B z z) (B y + B.flip y) y := by
      have := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
      convert this using 1
      all_goals rfl
    have h2 := ((hasFDerivAt_const (X 0) y).add A.hasFDerivAt).add
      ((s₀.hasFDerivAt).smul (hasFDerivAt_id y))
    have h3 := (hq.smul_const b₀).const_smul (1 / 2 : ℝ)
    have := h1.sub (h2.sub h3)
    convert this using 1
    all_goals first | rfl | (ext z; simp)
  have hG0 : ∀ y, fderiv ℝ G y = 0 := by
    intro y
    rw [(hG y).fderiv]
    ext v
    simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, zero_apply, hDXf y v, hB v y]
    module
  refine ⟨X 0, -(1 / 2 : ℝ) • b₀, A, fun u w => hck 0 u w, fun y => ?_⟩
  have := is_const_of_fderiv_eq_zero (fun y => (hG y).differentiableAt) hG0 y 0
  simp only [G, map_zero, smul_zero, zero_smul, add_zero, sub_zero, sub_self] at this
  rw [sub_eq_zero] at this
  rw [this]
  simp only [specialConformal, map_smul, smul_apply, smul_eq_mul, hb₀]
  module


end Classification

end Flat
end Lightlike
