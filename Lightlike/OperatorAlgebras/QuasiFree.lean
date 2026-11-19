import Lightlike.OperatorAlgebras.FockUnique
import Lightlike.OperatorAlgebras.StoneGenerator
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quasi-free vectors of a representation of the Weyl relations

J. Dereziński, arXiv:math-ph/0511030 (read), Section 9.1, pp. 38-39: a vector `Ψ` is *quasi-free* for a representation of
the CCR if `(Ψ|W(y)Ψ) = exp(-¼ yηy)` for a quadratic form `η` (eq. (70), p. 38); the field operators `φ(y)` are the
generators of `t ↦ W(ty) = e^{itφ(y)}`; Theorem 39, p. 39, gives the two-point function. Here:

* `WeylSystem h K`: the Weyl relations (eq. (8)-(9), Section 3.1, p. 9) without continuity; it is *regular* if
  `t ↦ W(ty)` is strongly continuous for each `y` (p. 10), and `WeylSystem.continuous_line_of_quasiFree` is Theorem 37,
  p. 38: a representation with a cyclic quasi-free vector is regular;
* `CCRRep.lineGroup R y`: the unitary group `t ↦ W(t y)`, and `CCRRep.field R y` its generator `φ(y)`;
* `CCRRep.IsQuasiFree R Ψ η`: eq. (70) for a symmetric real bilinear form `η`;
* `CCRRep.IsQuasiFree.mem_domain`: a quasi-free vector is in the domain of every field operator.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma symp_smul_smul_self (s t : ℝ) (y : h) : symp h ((s : ℂ) • y) ((t : ℂ) • y) = 0 := by
  unfold symp; rw [inner_smul_left, inner_smul_right]; simp [← Complex.ofReal_pow, Complex.mul_im]

lemma symp_real_smul_left (s : ℝ) (f g : h) : symp h ((s : ℂ) • f) g = s * symp h f g := by
  unfold symp; rw [inner_smul_left]; simp [Complex.mul_im]

lemma symp_real_smul_right (t : ℝ) (f g : h) : symp h f ((t : ℂ) • g) = t * symp h f g := by
  unfold symp; rw [inner_smul_right]; simp [Complex.mul_im]

lemma symp_self_eq_zero (f : h) : symp h f f = 0 := by
  simp [symp, ← Complex.ofReal_pow]

variable (h K) in
/-- **A representation of the CCR** (Dereziński, eq. (8)-(9), p. 9), with no continuity condition. -/
structure WeylSystem where
  /-- The Weyl unitary of a vector. -/
  W : h → (K ≃ₗᵢ[ℂ] K)
  /-- The Weyl relation (9). -/
  weyl : ∀ f g ψ, W f (W g ψ) = Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • W (f + g) ψ

namespace WeylSystem

variable (S : WeylSystem h K)

/-- `W 0 = 1` (Dereziński, Theorem 2, eq. (11)). -/
lemma W_zero_apply (ψ : K) : S.W 0 ψ = ψ := by
  have h1 := S.weyl 0 0 ψ
  rw [symp_self_eq_zero, add_zero] at h1
  simp only [zero_div, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul] at h1
  exact (S.W 0).injective h1

lemma W_zero : S.W 0 = LinearIsometryEquiv.refl ℂ K := by
  ext ψ; exact S.W_zero_apply ψ

/-- `W(s y) W(t y) = W((s + t) y)` (Dereziński, eq. (12)). -/
lemma W_line_add (y : h) (s t : ℝ) (ψ : K) :
    S.W ((s : ℂ) • y) (S.W ((t : ℂ) • y) ψ) = S.W (((s + t : ℝ) : ℂ) • y) ψ := by
  rw [S.weyl, symp_smul_smul_self]
  push_cast
  rw [add_smul]
  simp

lemma inner_W_neg_left (a : h) (x z : K) : ⟪S.W a x, z⟫_ℂ = ⟪x, S.W (-a) z⟫_ℂ := by
  have : S.W a (S.W (-a) z) = z := by
    rw [S.weyl, show symp h a (-a) = 0 by simp [symp, inner_neg_right, ← Complex.ofReal_pow], add_neg_cancel,
      S.W_zero_apply]
    simp
  rw [← LinearIsometryEquiv.inner_map_map (S.W a) x (S.W (-a) z), this]

/-- The vectors `u` along which `t ↦ W(t y) u` is continuous at `0`. -/
def contAt (y : h) : Submodule ℂ K where
  carrier := {u | Filter.Tendsto (fun t : ℝ => S.W ((t : ℂ) • y) u) (nhds 0) (nhds u)}
  zero_mem' := by simp [tendsto_const_nhds]
  add_mem' {u v} hu hv := by
    simp only [Set.mem_setOf_eq, map_add] at hu hv ⊢
    exact hu.add hv
  smul_mem' c u hu := by
    simp only [Set.mem_setOf_eq, map_smul] at hu ⊢
    exact hu.const_smul c

lemma isClosed_contAt (y : h) : IsClosed (S.contAt y : Set K) := by
  refine isClosed_of_closure_subset fun u hu => ?_
  show Filter.Tendsto (fun t : ℝ => S.W ((t : ℂ) • y) u) (nhds 0) (nhds u)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (ε / 3) (by positivity)
  have hv' : Filter.Tendsto (fun t : ℝ => S.W ((t : ℂ) • y) v) (nhds 0) (nhds v) := hv
  filter_upwards [Metric.tendsto_nhds.mp hv' (ε / 3) (by positivity)] with t ht
  have e1 : dist (S.W ((t : ℂ) • y) u) (S.W ((t : ℂ) • y) v) = dist u v := LinearIsometryEquiv.dist_map _ u v
  calc dist (S.W ((t : ℂ) • y) u) u
      ≤ dist (S.W ((t : ℂ) • y) u) (S.W ((t : ℂ) • y) v) + dist (S.W ((t : ℂ) • y) v) v + dist v u :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [e1, dist_comm v u]; gcongr
    _ = ε := by ring

/-- `⟪W x Ψ, W(t y) W x Ψ⟫ = e^{i t σ(x, y)} ⟪Ψ, W(t y) Ψ⟫`. -/
lemma inner_W_line_W (x y : h) (t : ℝ) (Ψ : K) :
    ⟪S.W x Ψ, S.W ((t : ℂ) • y) (S.W x Ψ)⟫_ℂ =
      Complex.exp (Complex.I * ((t * symp h x y : ℝ) : ℂ)) * ⟪Ψ, S.W ((t : ℂ) • y) Ψ⟫_ℂ := by
  rw [S.inner_W_neg_left, S.weyl ((t : ℂ) • y) x Ψ, map_smul, S.weyl (-x) ((t : ℂ) • y + x) Ψ, inner_smul_right,
    inner_smul_right, ← mul_assoc, ← Complex.exp_add, show -x + ((t : ℂ) • y + x) = (t : ℂ) • y by abel]
  congr 2
  have h1 : symp h ((t : ℂ) • y) x = -(t * symp h x y) := by
    rw [symp_real_smul_left]; unfold symp; rw [← inner_conj_symm y x, Complex.conj_im]; ring
  have h2 : symp h (-x) ((t : ℂ) • y + x) = -(t * symp h x y) := by
    unfold symp; rw [inner_neg_left, inner_add_right, inner_smul_right]; simp [Complex.mul_im, ← Complex.ofReal_pow]
  rw [h1, h2]
  push_cast
  ring

variable {S}

/-- **A quasi-free representation is regular** (Dereziński, Theorem 37, p. 38): if `Ψ` is cyclic and
`⟪Ψ, W y Ψ⟫ = exp(-¼ η(y, y))`, then `t ↦ W(t y) φ` is continuous for every `y` and `φ`. -/
theorem continuous_line_of_quasiFree {Ψ : K} {η : LinearMap.BilinForm ℝ h}
    (hΨ : ∀ y, ⟪Ψ, S.W y Ψ⟫_ℂ = Complex.exp (-(η y y / 4 : ℝ)))
    (hcyc : (Submodule.span ℂ (Set.range fun x => S.W x Ψ)).topologicalClosure = ⊤) (y : h) (φ : K) :
    Continuous fun t : ℝ => S.W ((t : ℂ) • y) φ := by
  have hq : ∀ t : ℝ, η ((t : ℂ) • y) ((t : ℂ) • y) = t ^ 2 * η y y := fun t => by
    simp only [Complex.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have hn : ⟪Ψ, Ψ⟫_ℂ = 1 := by
    have := hΨ 0
    simp only [S.W_zero_apply, map_zero, LinearMap.zero_apply, zero_div, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero] at this
    exact this
  -- each `W x Ψ` is in `contAt y`
  have hgen : ∀ x, S.W x Ψ ∈ S.contAt y := by
    intro x
    show Filter.Tendsto (fun t : ℝ => S.W ((t : ℂ) • y) (S.W x Ψ)) (nhds 0) (nhds (S.W x Ψ))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ t : ℝ, ‖S.W ((t : ℂ) • y) (S.W x Ψ) - S.W x Ψ‖ ^ 2 =
        2 - 2 * (Complex.exp (Complex.I * ((t * symp h x y : ℝ) : ℂ)) *
          Complex.exp (-((t ^ 2 * η y y) / 4 : ℝ))).re := by
      intro t
      have hu : ‖S.W x Ψ‖ = 1 := by
        rw [LinearIsometryEquiv.norm_map]
        have : ‖Ψ‖ ^ 2 = 1 := by
          rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hn]; simp
        nlinarith [norm_nonneg Ψ]
      rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, hu, ← inner_conj_symm, S.inner_W_line_W, hΨ, hq,
        RCLike.re_to_complex, Complex.conj_re]
      ring
    have hc : Continuous fun t : ℝ => 2 - 2 * (Complex.exp (Complex.I * ((t * symp h x y : ℝ) : ℂ)) *
        Complex.exp (-((t ^ 2 * η y y) / 4 : ℝ))).re := by fun_prop
    have h0 : Filter.Tendsto (fun t : ℝ => ‖S.W ((t : ℂ) • y) (S.W x Ψ) - S.W x Ψ‖ ^ 2) (nhds 0) (nhds 0) := by
      simp only [hsq]
      have := hc.tendsto 0
      convert this using 2
      simp
    have h1 := h0.sqrt
    simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h1
    exact h1
  have hspan : Submodule.span ℂ (Set.range fun x => S.W x Ψ) ≤ S.contAt y :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)
  have hall : φ ∈ S.contAt y := by
    have : (Submodule.span ℂ (Set.range fun x => S.W x Ψ)).topologicalClosure ≤ S.contAt y :=
      Submodule.topologicalClosure_minimal _ hspan (S.isClosed_contAt y)
    rw [hcyc] at this
    exact this Submodule.mem_top
  have h0 : Filter.Tendsto (fun t : ℝ => S.W ((t : ℂ) • y) φ) (nhds 0) (nhds φ) := hall
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h0' := Metric.tendsto_nhds.mp h0 ε hε
  have hshift : Filter.Tendsto (fun t : ℝ => t - t₀) (nhds t₀) (nhds 0) := by
    simpa using (continuous_sub_right t₀).tendsto t₀
  filter_upwards [hshift.eventually h0'] with t ht
  have e : S.W ((t : ℂ) • y) φ = S.W ((t₀ : ℂ) • y) (S.W (((t - t₀ : ℝ) : ℂ) • y) φ) := by
    rw [S.W_line_add]; congr 2; push_cast; ring
  rw [e, LinearIsometryEquiv.dist_map]
  exact ht

/-- The regular representation given by a cyclic quasi-free vector. -/
noncomputable def toCCRRep {Ψ : K} {η : LinearMap.BilinForm ℝ h}
    (hΨ : ∀ y, ⟪Ψ, S.W y Ψ⟫_ℂ = Complex.exp (-(η y y / 4 : ℝ)))
    (hcyc : (Submodule.span ℂ (Set.range fun x => S.W x Ψ)).topologicalClosure = ⊤) : CCRRep h K where
  W := S.W
  W_zero := S.W_zero
  weyl := S.weyl
  continuous_line y φ := continuous_line_of_quasiFree hΨ hcyc y φ

end WeylSystem

/-- **The one-parameter group** `t ↦ W(t y)`. -/
noncomputable def CCRRep.lineGroup (R : CCRRep h K) (y : h) : UnitaryGroup K where
  toFun t := R.W ((t : ℂ) • y)
  map_zero' := by simp [R.W_zero]
  map_add' s t := by
    ext ψ
    simp only [LinearIsometryEquiv.trans_apply]
    rw [R.weyl, symp_smul_smul_self, show ((s : ℂ) • y + (t : ℂ) • y) = ((s + t : ℝ) : ℂ) • y by
      push_cast; rw [add_smul]]
    simp
  continuous' ψ := R.continuous_line y ψ

lemma CCRRep.lineGroup_apply (R : CCRRep h K) (y : h) (t : ℝ) (ψ : K) :
    R.lineGroup y t ψ = R.W ((t : ℂ) • y) ψ := rfl

/-- The adjoint of `W a` is `W (-a)`. -/
lemma CCRRep.inner_W_left (R : CCRRep h K) (a : h) (x z : K) : ⟪R.W a x, z⟫_ℂ = ⟪x, R.W (-a) z⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map (R.W (-a)), R.W_neg_W]

/-- **A quasi-free vector** (Dereziński, eq. (70), p. 38): `(Ψ|W(y)Ψ) = exp(-¼ η(y, y))` for a symmetric real
bilinear form `η` (the source's quadratic form `y ↦ yηy`). -/
structure CCRRep.IsQuasiFree (R : CCRRep h K) (Ψ : K) (η : LinearMap.BilinForm ℝ h) : Prop where
  /-- `η` is symmetric. -/
  symm : ∀ a b, η a b = η b a
  /-- Eq. (70). -/
  expectation : ∀ y, ⟪Ψ, R.W y Ψ⟫_ℂ = Complex.exp (-(η y y / 4 : ℝ))

variable {R : CCRRep h K} {Ψ : K} {η : LinearMap.BilinForm ℝ h}

lemma bilin_real_smul (η : LinearMap.BilinForm ℝ h) (s t : ℝ) (a b : h) :
    η ((s : ℂ) • a) ((t : ℂ) • b) = s * t * η a b := by
  simp only [Complex.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma CCRRep.IsQuasiFree.norm_eq_one (hΨ : R.IsQuasiFree Ψ η) : ‖Ψ‖ = 1 := by
  have h0 := hΨ.expectation 0
  simp only [R.W_zero_apply, map_zero, LinearMap.zero_apply, zero_div, neg_zero, Complex.ofReal_zero,
    Complex.exp_zero] at h0
  have : ‖Ψ‖ ^ 2 = 1 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h0]; simp
  nlinarith [norm_nonneg Ψ, sq_nonneg (‖Ψ‖ - 1)]

/-- `η` is positive (Dereziński, p. 38: "`η` is necessarily positive"). -/
lemma CCRRep.IsQuasiFree.nonneg (hΨ : R.IsQuasiFree Ψ η) (y : h) : 0 ≤ η y y := by
  have h1 : ‖⟪Ψ, R.W y Ψ⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪Ψ, R.W y Ψ⟫_ℂ‖ ≤ ‖Ψ‖ * ‖R.W y Ψ‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [LinearIsometryEquiv.norm_map, hΨ.norm_eq_one, one_mul]
  rw [hΨ.expectation, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h1
  have := Real.exp_le_one_iff.mp h1
  linarith

/-- `‖W(s y)Ψ - Ψ‖² = 2 - 2 e^{-s² η(y,y)/4}` for a quasi-free `Ψ`. -/
lemma CCRRep.IsQuasiFree.norm_sq_W_sub (hΨ : R.IsQuasiFree Ψ η) (y : h) (s : ℝ) :
    ‖R.W ((s : ℂ) • y) Ψ - Ψ‖ ^ 2 = 2 - 2 * Real.exp (-(s ^ 2 * η y y / 4)) := by
  have hn := hΨ.norm_eq_one
  have hi : ⟪Ψ, R.W ((s : ℂ) • y) Ψ⟫_ℂ = (Real.exp (-(s ^ 2 * η y y / 4)) : ℂ) := by
    rw [hΨ.expectation, bilin_real_smul, Complex.ofReal_exp, Complex.ofReal_neg, ← sq]
  rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, hn, ← inner_conj_symm, hi]
  simp only [RCLike.re_to_complex, Complex.conj_ofReal, Complex.ofReal_re, one_pow]
  ring

lemma CCRRep.IsQuasiFree.norm_W_sub_le (hΨ : R.IsQuasiFree Ψ η) (y : h) (s : ℝ) :
    ‖R.W ((s : ℂ) • y) Ψ - Ψ‖ ≤ Real.sqrt (η y y / 2) * |s| := by
  have h1 := hΨ.norm_sq_W_sub y s
  have hη := hΨ.nonneg y
  have h2 : 2 - 2 * Real.exp (-(s ^ 2 * η y y / 4)) ≤ (Real.sqrt (η y y / 2) * |s|) ^ 2 := by
    have := Real.add_one_le_exp (-(s ^ 2 * η y y / 4))
    rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    nlinarith
  rw [← h1] at h2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2

variable [CompleteSpace K]

/-- **The field operator** `φ(y)`, the self-adjoint generator of `t ↦ W(t y) = e^{itφ(y)}`. -/
noncomputable def CCRRep.field (R : CCRRep h K) (y : h) : K →ₗ.[ℂ] K := (R.lineGroup y).generator

/-- **A quasi-free vector lies in the domain of every field operator** (Dereziński, p. 38, before Theorem 38:
"in a quasi-free representation we can define the corresponding field operators"). -/
theorem CCRRep.IsQuasiFree.mem_domain (hΨ : R.IsQuasiFree Ψ η) (y : h) : Ψ ∈ (R.field y).domain := by
  have hadj : Ψ ∈ ((R.lineGroup y).generator).adjoint.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    refine AddMonoidHomClass.continuous_of_bound _ (Real.sqrt (η y y / 2)) fun φ => ?_
    show ‖⟪Ψ, (R.lineGroup y).generator φ⟫_ℂ‖ ≤ Real.sqrt (η y y / 2) * ‖φ‖
    rw [UnitaryGroup.generator_apply, inner_smul_right, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hφ : HasDerivAt (fun t => R.lineGroup y t (φ : K)) ((R.lineGroup y).dvec φ) 0 := by
      have := (R.lineGroup y).hasDerivAt_of_mem φ.2 0
      simpa [UnitaryGroup.apply_zero] using this
    have hlim : Filter.Tendsto (fun t : ℝ => t⁻¹ • (R.lineGroup y t (φ : K) - φ)) (nhdsWithin 0 {0}ᶜ)
        (nhds ((R.lineGroup y).dvec φ)) := by
      have := hφ.tendsto_slope_zero
      simpa [UnitaryGroup.apply_zero] using this
    have hle : ∀ t : ℝ, t ≠ 0 →
        ‖innerSL ℂ Ψ (t⁻¹ • (R.lineGroup y t (φ : K) - φ))‖ ≤ Real.sqrt (η y y / 2) * ‖(φ : K)‖ := by
      intro t ht
      have e : ⟪Ψ, R.lineGroup y t (φ : K)⟫_ℂ = ⟪R.lineGroup y (-t) Ψ, φ⟫_ℂ := by
        rw [UnitaryGroup.inner_apply, neg_neg]
      have hat : |t| ≠ 0 := abs_ne_zero.mpr ht
      rw [innerSL_apply_apply, ← Complex.coe_smul, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        inner_sub_right, e, ← inner_sub_left]
      calc |t⁻¹| * ‖⟪R.lineGroup y (-t) Ψ - Ψ, (φ : K)⟫_ℂ‖
          ≤ |t⁻¹| * (‖R.lineGroup y (-t) Ψ - Ψ‖ * ‖(φ : K)‖) := by
            gcongr; exact norm_inner_le_norm _ _
        _ ≤ |t⁻¹| * ((Real.sqrt (η y y / 2) * |-t|) * ‖(φ : K)‖) := by
            gcongr; exact hΨ.norm_W_sub_le y (-t)
        _ = Real.sqrt (η y y / 2) * ‖(φ : K)‖ := by rw [abs_neg, abs_inv]; field_simp
    have hlim' := ((innerSL ℂ Ψ).continuous.tendsto _).comp hlim
    have := le_of_tendsto hlim'.norm (eventually_nhdsWithin_of_forall fun t ht => hle t ht)
    rw [innerSL_apply_apply] at this
    exact this
  exact (R.lineGroup y).adjoint_le_generator.1 hadj

omit [CompleteSpace K] in
/-- The coefficients `⟪W(s y₁)Ψ, W(t y₂)Ψ⟫` of a quasi-free vector. -/
lemma CCRRep.IsQuasiFree.inner_W_W (hΨ : R.IsQuasiFree Ψ η) (y₁ y₂ : h) (s t : ℝ) :
    ⟪R.W ((s : ℂ) • y₁) Ψ, R.W ((t : ℂ) • y₂) Ψ⟫_ℂ =
      Complex.exp (Complex.I * ((s * t * symp h y₁ y₂ / 2 : ℝ) : ℂ) -
        ((s ^ 2 * η y₁ y₁ - 2 * s * t * η y₁ y₂ + t ^ 2 * η y₂ y₂) / 4 : ℝ)) := by
  have hs : -((s : ℂ) • y₁) = ((-s : ℝ) : ℂ) • y₁ := by push_cast; rw [neg_smul]
  rw [R.inner_W_left, R.weyl, inner_smul_right, hΨ.expectation, ← Complex.exp_add, hs, symp_real_smul_left,
    symp_real_smul_right]
  simp only [map_add, LinearMap.add_apply, bilin_real_smul, hΨ.symm y₂ y₁]
  congr 1
  push_cast
  ring

omit [CompleteSpace K] in
lemma CCRRep.IsQuasiFree.inner_W_left_self (hΨ : R.IsQuasiFree Ψ η) (y : h) (s : ℝ) :
    ⟪R.W ((s : ℂ) • y) Ψ, Ψ⟫_ℂ = Complex.exp (-((s ^ 2 * η y y) / 4 : ℝ)) := by
  have hs : -((s : ℂ) • y) = ((-s : ℝ) : ℂ) • y := by push_cast; rw [neg_smul]
  rw [R.inner_W_left, hs, hΨ.expectation, bilin_real_smul]
  congr 2
  ring

omit [CompleteSpace K] in
lemma CCRRep.IsQuasiFree.inner_self_W (hΨ : R.IsQuasiFree Ψ η) (y : h) (s : ℝ) :
    ⟪Ψ, R.W ((s : ℂ) • y) Ψ⟫_ℂ = Complex.exp (-((s ^ 2 * η y y) / 4 : ℝ)) := by
  rw [hΨ.expectation, bilin_real_smul]
  congr 2
  ring

/-- The difference quotient `t⁻¹ (W(t y)Ψ - Ψ)` tends to `i φ(y) Ψ`. -/
lemma CCRRep.tendsto_slope_field (R : CCRRep h K) (y : h) {Ψ : K} (hΨ : Ψ ∈ (R.field y).domain) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ • (R.W ((t : ℂ) • y) Ψ - Ψ)) (nhdsWithin 0 {0}ᶜ)
      (nhds (Complex.I • R.field y ⟨Ψ, hΨ⟩)) := by
  have hφ : HasDerivAt (fun t => R.lineGroup y t Ψ) ((R.lineGroup y).dvec Ψ) 0 := by
    have := (R.lineGroup y).hasDerivAt_of_mem hΨ 0
    simpa [UnitaryGroup.apply_zero] using this
  have h1 := hφ.tendsto_slope_zero
  rw [show (R.lineGroup y).dvec Ψ = Complex.I • R.field y ⟨Ψ, hΨ⟩ from (R.lineGroup y).dvec_eq ⟨Ψ, hΨ⟩] at h1
  simpa [UnitaryGroup.apply_zero, CCRRep.lineGroup_apply, R.W_zero_apply] using h1

/-- `(u²)⁻¹ (e^{u²α} - e^{u²a} - e^{u²c} + 1) → α - a - c` as `u → 0`. -/
lemma tendsto_quad_slope (α a c : ℂ) :
    Filter.Tendsto (fun u : ℝ => ((u ^ 2 : ℝ) : ℂ)⁻¹ * (Complex.exp (((u ^ 2 : ℝ) : ℂ) * α) -
      Complex.exp (((u ^ 2 : ℝ) : ℂ) * a) - Complex.exp (((u ^ 2 : ℝ) : ℂ) * c) + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds (α - a - c)) := by
  have e : ∀ β : ℂ, HasDerivAt (fun v : ℝ => Complex.exp ((v : ℂ) * β)) β 0 := by
    intro β
    have := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const β).cexp).comp_ofReal
    simpa using this
  have hk := (((e α).sub (e a)).sub (e c)).add_const 1
  have h1 := hk.tendsto_slope_zero
  have hsq : Filter.Tendsto (fun u : ℝ => u ^ 2) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (continuous_pow 2).tendsto (0 : ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun u hu => pow_ne_zero 2 hu
  refine (h1.comp hsq).congr fun u => ?_
  simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, zero_add, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv]
  ring

/-- **The two-point function of a quasi-free vector** (Dereziński, Theorem 39 (1), p. 39):
`(φ(y₁)Ψ | φ(y₂)Ψ) = ½ (η(y₁, y₂) + i σ(y₁, y₂))`. -/
theorem CCRRep.IsQuasiFree.inner_field_field (hΨ : R.IsQuasiFree Ψ η) (y₁ y₂ : h) :
    ⟪R.field y₁ ⟨Ψ, hΨ.mem_domain y₁⟩, R.field y₂ ⟨Ψ, hΨ.mem_domain y₂⟩⟫_ℂ =
      ((η y₁ y₂ / 2 : ℝ) : ℂ) + Complex.I * ((symp h y₁ y₂ / 2 : ℝ) : ℂ) := by
  have hlim := Filter.Tendsto.inner (𝕜 := ℂ) (R.tendsto_slope_field y₁ (hΨ.mem_domain y₁))
    (R.tendsto_slope_field y₂ (hΨ.mem_domain y₂))
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg,
    one_mul] at hlim
  set α : ℂ := Complex.I * ((symp h y₁ y₂ / 2 : ℝ) : ℂ) - ((η y₁ y₁ - 2 * η y₁ y₂ + η y₂ y₂) / 4 : ℝ)
  set a : ℂ := ((-(η y₁ y₁ / 4) : ℝ) : ℂ)
  set c : ℂ := ((-(η y₂ y₂ / 4) : ℝ) : ℂ)
  have hval : ∀ u : ℝ, ⟪u⁻¹ • (R.W ((u : ℂ) • y₁) Ψ - Ψ), u⁻¹ • (R.W ((u : ℂ) • y₂) Ψ - Ψ)⟫_ℂ =
      ((u ^ 2 : ℝ) : ℂ)⁻¹ * (Complex.exp (((u ^ 2 : ℝ) : ℂ) * α) - Complex.exp (((u ^ 2 : ℝ) : ℂ) * a) -
        Complex.exp (((u ^ 2 : ℝ) : ℂ) * c) + 1) := by
    intro u
    rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, inner_sub_right, hΨ.inner_W_W, hΨ.inner_W_left_self, hΨ.inner_self_W,
      inner_self_eq_norm_sq_to_K, hΨ.norm_eq_one, Complex.conj_ofReal]
    have e1 : Complex.I * ((u * u * symp h y₁ y₂ / 2 : ℝ) : ℂ) -
        ((u ^ 2 * η y₁ y₁ - 2 * u * u * η y₁ y₂ + u ^ 2 * η y₂ y₂) / 4 : ℝ) = ((u ^ 2 : ℝ) : ℂ) * α := by
      simp only [α]; push_cast; ring
    have e2 : (-((u ^ 2 * η y₁ y₁) / 4 : ℝ) : ℂ) = ((u ^ 2 : ℝ) : ℂ) * a := by simp only [a]; push_cast; ring
    have e3 : (-((u ^ 2 * η y₂ y₂) / 4 : ℝ) : ℂ) = ((u ^ 2 : ℝ) : ℂ) * c := by simp only [c]; push_cast; ring
    rw [e1, e2, e3]
    push_cast
    ring
  have h2 := tendsto_quad_slope α a c
  have := tendsto_nhds_unique (hlim.congr hval) h2
  rw [this]
  simp only [α, a, c]
  push_cast
  ring

/-- `‖φ(y)Ψ‖² = η(y, y)/2` (Dereziński, proof of Theorem 39, p. 39). -/
theorem CCRRep.IsQuasiFree.norm_field_sq (hΨ : R.IsQuasiFree Ψ η) (y : h) :
    ‖R.field y ⟨Ψ, hΨ.mem_domain y⟩‖ ^ 2 = η y y / 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hΨ.inner_field_field, symp_self_eq_zero]
  simp

/-- **The symplectic form is bounded by the quadratic form** (Dereziński, Theorem 39 (2), p. 39, with the sharper
constant `1` for the source's `2`): `|σ(y₁, y₂)| ≤ η(y₁, y₁)^{1/2} η(y₂, y₂)^{1/2}`. -/
theorem CCRRep.IsQuasiFree.abs_symp_le (hΨ : R.IsQuasiFree Ψ η) (y₁ y₂ : h) :
    |symp h y₁ y₂| ≤ Real.sqrt (η y₁ y₁) * Real.sqrt (η y₂ y₂) := by
  set A := R.field y₁ ⟨Ψ, hΨ.mem_domain y₁⟩
  set B := R.field y₂ ⟨Ψ, hΨ.mem_domain y₂⟩
  have him : (⟪A, B⟫_ℂ).im = symp h y₁ y₂ / 2 := by
    rw [hΨ.inner_field_field]; simp
  have hcs : ‖⟪A, B⟫_ℂ‖ ≤ ‖A‖ * ‖B‖ := norm_inner_le_norm _ _
  have key : Real.sqrt (η y₁ y₁) * Real.sqrt (η y₂ y₂) = 2 * (‖A‖ * ‖B‖) := by
    rw [← Real.sqrt_mul (hΨ.nonneg y₁), show η y₁ y₁ * η y₂ y₂ = (2 * (‖A‖ * ‖B‖)) ^ 2 by
      rw [mul_pow, mul_pow, hΨ.norm_field_sq y₁, hΨ.norm_field_sq y₂]; ring, Real.sqrt_sq (by positivity)]
  rw [key]
  have := Complex.abs_im_le_norm ⟪A, B⟫_ℂ
  rw [him, abs_div, abs_two] at this
  linarith

/-- Dereziński, Theorem 39 (2), p. 39, as printed: `|y₁ωy₂| ≤ 2 |y₁ηy₁|^{1/2} |y₂ηy₂|^{1/2}`. -/
theorem CCRRep.IsQuasiFree.abs_symp_le_two_mul (hΨ : R.IsQuasiFree Ψ η) (y₁ y₂ : h) :
    |symp h y₁ y₂| ≤ 2 * Real.sqrt |η y₁ y₁| * Real.sqrt |η y₂ y₂| := by
  rw [abs_of_nonneg (hΨ.nonneg y₁), abs_of_nonneg (hΨ.nonneg y₂), mul_assoc]
  have := hΨ.abs_symp_le y₁ y₂
  have h0 : 0 ≤ Real.sqrt (η y₁ y₁) * Real.sqrt (η y₂ y₂) := by positivity
  linarith

section Fock

attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace K] in
/-- **The Fock vacuum is quasi-free**, with `η = Re⟪·,·⟫`, the real scalar product of `h`. -/
theorem FockRep.isQuasiFree_vacuum (R : FockRep h K) : R.toCCRRep.IsQuasiFree R.Ω (innerₗ h) where
  symm a b := real_inner_comm b a
  expectation y := by
    rw [R.vacuum_expectation, show innerₗ h y y = ‖y‖ ^ 2 from real_inner_self_eq_norm_sq y]

end Fock

end Lightlike.OperatorAlgebras
