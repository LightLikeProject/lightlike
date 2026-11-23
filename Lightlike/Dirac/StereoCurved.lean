import Mathlib
import Lightlike.Dirac.StereoSphere
import Lightlike.Dirac.SelfAdjoint

/-!
# The Dirac operator of the round sphere in the stereographic chart: explicit form

In the stereographic orthonormal frame `Fₐ = h eₐ` of the unit `n`-sphere (`stereoF`, `stereoOmega`)
the spinor connection form is `spinForm (ωᵢ) = ¼ (γᵢ Y − Y γᵢ)` with `Y(y) = ∑ₗ yₗ γₗ`
(Clifford multiplication by the position vector).  Using `γᵢ² = -1` and `γᵢγₖγᵢ = γₖ` (`i ≠ k`) one gets
`∑ᵢ γᵢ spinForm(ωᵢ) = -((n-1)/2) Y`, hence
`D f = h ∑ᵢ γᵢ ∂ᵢ f - ((n-1)/2) Y f`  (`diracF_stereo`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Clifford multiplication by the position vector `y = ∑ yₗ eₗ`. -/
noncomputable def Yop (ρ : CliffordRep n V) (y : E n) : V →L[ℝ] V := ∑ l, y l • gam ρ l

/-- `γᵢ γₖ γᵢ = γₖ` for `i ≠ k` and `= -γₖ` for `i = k`. -/
lemma gam_conj (ρ : CliffordRep n V) (i k : Fin n) :
    gam ρ i * gam ρ k * gam ρ i = if i = k then -gam ρ k else gam ρ k := by
  by_cases h : i = k
  · subst h
    simp [gam_mul_self]
  · rw [if_neg h, gam_mul_swap ρ h, neg_mul, mul_assoc, gam_mul_self]
    simp

lemma sum_gam_conj (ρ : CliffordRep n V) (x : E n) :
    ∑ i, gam ρ i * Yop ρ x * gam ρ i = ((n : ℝ) - 2) • Yop ρ x := by
  have h1 : ∀ i, gam ρ i * Yop ρ x * gam ρ i = ∑ k, x k • (if i = k then -gam ρ k else gam ρ k) := by
    intro i
    simp only [Yop, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, gam_conj]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ k, ∑ i : Fin n, x k • (if i = k then -gam ρ k else gam ρ k) =
      ((n : ℝ) - 2) • (x k • gam ρ k) := by
    intro k
    have h3 : ∀ i : Fin n, (if i = k then -gam ρ k else gam ρ k) =
        gam ρ k - if i = k then (2 : ℝ) • gam ρ k else 0 := by
      intro i
      split_ifs
      · rw [two_smul]; abel
      · simp
    simp only [h3, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin, smul_sub, smul_smul]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← sub_smul]
    congr 1
    ring
  simp only [h2, ← Finset.smul_sum]
  rfl

lemma spinForm_stereo (ρ : CliffordRep n V) (x : E n) (i : Fin n) :
    spinForm ρ (stereoOmega x i) = (1 / 4 : ℝ) • (gam ρ i * Yop ρ x - Yop ρ x * gam ρ i) := by
  unfold spinForm Yop stereoOmega
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, sub_smul, ite_smul,
    zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma sum_gam_spinForm_stereo (ρ : CliffordRep n V) (x : E n) :
    ∑ i, gam ρ i * spinForm ρ (stereoOmega x i) = (-((n : ℝ) - 1) / 2) • Yop ρ x := by
  have h1 : ∀ i, gam ρ i * spinForm ρ (stereoOmega x i) =
      (1 / 4 : ℝ) • (-Yop ρ x - gam ρ i * Yop ρ x * gam ρ i) := by
    intro i
    rw [spinForm_stereo, mul_smul_comm, mul_sub, ← mul_assoc, gam_mul_self, ← mul_assoc]
    simp
  simp only [h1, ← Finset.smul_sum, Finset.sum_sub_distrib, sum_gam_conj, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  module

/-- **The Dirac operator of the round sphere in the stereographic chart.**
`D f = h · (∑ᵢ γᵢ ∂ᵢ f) − ((n−1)/2) · y·f`, with `h = (1+‖y‖²)/2` and `y·` Clifford multiplication
by the position vector. -/
theorem diracF_stereo (ρ : CliffordRep n V) (f : E n → V) (x : E n) :
    diracF ρ stereoF stereoOmega f x =
      stereoH x • dirac ρ f x + (-((n : ℝ) - 1) / 2) • Yop ρ x (f x) := by
  have h1 : ∀ i, gam ρ i (nablaF ρ stereoF stereoOmega i f x) =
      stereoH x • gam ρ i (fderiv ℝ f x (e i)) + (gam ρ i * spinForm ρ (stereoOmega x i)) (f x) := by
    intro i
    simp only [nablaF, stereoF, map_add, map_smul, mul_apply_eq_comp, Function.comp_apply]
    rfl
  have h2 := congrArg (fun L => L (f x)) (sum_gam_spinForm_stereo ρ x)
  simp only [ContinuousLinearMap.sum_apply, smul_apply] at h2
  simp only [diracF, h1, Finset.sum_add_distrib, ← Finset.smul_sum, h2, dirac]

/-! ### The weight `h^{-n}` (Riemannian volume density) and the weighted flat integration by parts -/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

/-- The Riemannian volume density `h^{-n} = (2/(1+‖y‖²))ⁿ` of the round `n`-sphere in the
stereographic chart. -/
noncomputable def stereoW (n : ℕ) (y : E n) : ℝ := stereoH y ^ (-(n : ℤ))

/-- The weight `h · h^{-n} = h^{1-n}` appearing in the integration by parts for `D`. -/
noncomputable def stereoPhi (n : ℕ) (y : E n) : ℝ := stereoH y ^ (1 - (n : ℤ))

lemma stereoPhi_eq (x : E n) : stereoPhi n x = stereoH x * stereoW n x := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  rw [stereoPhi, stereoW, ← zpow_one_add₀ hne]
  congr 1

lemma hasFDerivAt_stereoPhi (x : E n) :
    HasFDerivAt (stereoPhi n)
      ((((1 - (n : ℤ) : ℤ) : ℝ) * stereoH x ^ ((1 - (n : ℤ)) - 1)) •
        ((1 / 2 : ℝ) • (2 • innerSL ℝ x))) x := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  exact (hasDerivAt_zpow (1 - (n : ℤ)) (stereoH x) (Or.inl hne)).comp_hasFDerivAt x
    (hasFDerivAt_stereoH x)

lemma fderiv_stereoPhi_apply (x v : E n) :
    fderiv ℝ (stereoPhi n) x v = (1 - (n : ℝ)) * stereoW n x * ⟪x, v⟫ := by
  rw [(hasFDerivAt_stereoPhi x).fderiv]
  have e1 : stereoH x ^ ((1 - (n : ℤ)) - 1) = stereoW n x := by
    rw [stereoW]; congr 1; ring
  simp only [ContinuousLinearMap.smul_apply, e1, innerSL_apply_apply, smul_eq_mul]
  push_cast
  simp

lemma contDiff_stereoPhi : ContDiff ℝ 1 (stereoPhi n : E n → ℝ) := by
  rw [contDiff_one_iff_fderiv]
  have hd : Differentiable ℝ (stereoPhi n : E n → ℝ) := fun x => (hasFDerivAt_stereoPhi x).differentiableAt
  refine ⟨hd, ?_⟩
  have : fderiv ℝ (stereoPhi n : E n → ℝ) = fun x : E n =>
      ((((1 - (n : ℤ) : ℤ) : ℝ) * stereoH x ^ ((1 - (n : ℤ)) - 1)) •
        ((1 / 2 : ℝ) • (2 • innerSL ℝ x)) : E n →L[ℝ] ℝ) := by
    funext x
    rw [(hasFDerivAt_stereoPhi x).fderiv]
  rw [this]
  have hc1 : Continuous (fun x : E n => (((1 - (n : ℤ) : ℤ) : ℝ) * stereoH x ^ ((1 - (n : ℤ)) - 1))) :=
    continuous_const.mul (Continuous.zpow₀ ((contDiff_stereoH (n := n)).continuous) _
      (fun x => Or.inl (stereoH_pos x).ne'))
  have hc2 : Continuous (fun x : E n => ((1 / 2 : ℝ) • (2 • innerSL ℝ x) : E n →L[ℝ] ℝ)) :=
    ((innerSL ℝ : E n →L[ℝ] E n →L[ℝ] ℝ).continuous.const_smul (2 : ℕ)).const_smul (1 / 2 : ℝ)
  exact hc1.smul hc2

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Dirac operator of a weighted spinor: `D (φ g) = φ D g + ∑ᵢ (∂ᵢφ) γᵢ g`. -/
lemma dirac_smul_apply (ρ : CliffordRep n V) {φ : E n → ℝ} {g : E n → V} (hφ : ContDiff ℝ 1 φ)
    (hg : ContDiff ℝ 1 g) (x : E n) :
    dirac ρ (fun y => φ y • g y) x =
      φ x • dirac ρ g x + ∑ i, fderiv ℝ φ x (e i) • gam ρ i (g x) := by
  have hφ' := (hφ.differentiable (by norm_num)) x
  have hg' := (hg.differentiable (by norm_num)) x
  have h : HasFDerivAt (fun y => φ y • g y) _ x := hφ'.hasFDerivAt.smul hg'.hasFDerivAt
  simp only [dirac, h.fderiv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum]

/-- **Weighted flat integration by parts for `D`.** For `C¹` compactly supported `f, g` and a `C¹`
weight `φ`, `∫ φ ⟪D f, g⟫ = ∫ (φ ⟪f, D g⟫ + ⟪f, ∑ᵢ (∂ᵢφ) γᵢ g⟫)`. -/
theorem integral_dirac_inner_weight {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {φ : E n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {f g : E n → V} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ x, φ x * inner ℝ (dirac ρ f x) (g x) =
      ∫ x, (φ x * inner ℝ (f x) (dirac ρ g x) +
        inner ℝ (f x) (∑ i, fderiv ℝ φ x (e i) • gam ρ i (g x))) := by
  have h : ∫ x, inner ℝ (dirac ρ f x) (φ x • g x) =
      ∫ x, inner ℝ (f x) (dirac ρ (fun y => φ y • g y) x) :=
    integral_dirac_inner hρ hf (hφ.smul hg) hfc (hgc.smul_left)
  simp only [real_inner_smul_right] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [dirac_smul_apply ρ hφ hg x, inner_add_right, real_inner_smul_right]

lemma inner_e (x : E n) (i : Fin n) : ⟪x, e i⟫ = x i := by
  simp [e, EuclideanSpace.inner_single_right]

lemma continuous_stereoW : Continuous (stereoW n : E n → ℝ) :=
  Continuous.zpow₀ ((contDiff_stereoH (n := n)).continuous) _
    (fun x => Or.inl (stereoH_pos x).ne')

lemma continuous_dirac {ρ : CliffordRep n V} {f : E n → V} (hf : ContDiff ℝ 1 f) :
    Continuous (dirac ρ f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  exact continuous_finset_sum _ fun i _ => (gam ρ i).continuous.comp (hfd.clm_apply continuous_const)

lemma continuous_Yop_apply {ρ : CliffordRep n V} {f : E n → V} (hf : Continuous f) :
    Continuous (fun x => Yop ρ x (f x)) := by
  simp only [Yop, sum_apply, smul_apply]
  exact continuous_finset_sum _ fun l _ =>
    ((EuclideanSpace.proj l : E n →L[ℝ] ℝ).continuous).smul ((gam ρ l).continuous.comp hf)

/-- Clifford multiplication by the position vector is skew-adjoint. -/
lemma inner_Yop {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (x : E n) (u v : V) :
    inner ℝ (Yop ρ x u) v = -inner ℝ u (Yop ρ x v) := by
  have hρ' : ∀ (i : Fin n) (w u : V), inner ℝ (gam ρ i w) u = -inner ℝ w (gam ρ i u) := hρ
  simp only [Yop, sum_apply, smul_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, hρ', Finset.sum_neg_distrib, mul_neg]

omit [InnerProductSpace ℝ V] in
/-- Integrability of a continuous function supported where a compactly supported `k` is nonzero. -/
lemma integrable_of_cont_supp {u : E n → ℝ} {k : E n → V} (hu : Continuous u)
    (hkc : HasCompactSupport k) (hs : ∀ x, k x = 0 → u x = 0) : Integrable u :=
  hu.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hkc.isCompact fun x hx => hs x (image_eq_zero_of_notMem_tsupport hx))

lemma sum_fderiv_stereoPhi_gam (ρ : CliffordRep n V) (g : E n → V) (x : E n) :
    ∑ i, fderiv ℝ (stereoPhi n) x (e i) • gam ρ i (g x) =
      ((1 - (n : ℝ)) * stereoW n x) • Yop ρ x (g x) := by
  simp only [fderiv_stereoPhi_apply, inner_e, Yop, sum_apply, smul_apply, Finset.smul_sum,
    smul_smul, mul_assoc]

/-- **Formal self-adjointness of the Dirac operator of the round sphere, in the stereographic
chart.** For `C¹` compactly supported spinor fields `f, g` on `ℝⁿ` (the chart), with `D = diracF`
the Dirac operator in the stereographic frame and the Riemannian volume density `h^{-n}`
(`stereoW`): `∫ ⟪D f, g⟫ h^{-n} dy = ∫ ⟪f, D g⟫ h^{-n} dy`.  The proof uses the weighted flat
integration by parts and the skew-adjointness of `Y`; the term `(n-1)/2 · Y` of the spin
connection exactly compensates the derivative of the density. -/
theorem integral_diracF_stereo_inner {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {f g : E n → V}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ x, inner ℝ (diracF ρ stereoF stereoOmega f x) (g x) * stereoW n x =
      ∫ x, inner ℝ (f x) (diracF ρ stereoF stereoOmega g x) * stereoW n x := by
  have hweight := integral_dirac_inner_weight hρ (contDiff_stereoPhi (n := n)) hf hg hfc hgc
  simp only [sum_fderiv_stereoPhi_gam] at hweight
  have hL : ∀ x, inner ℝ (diracF ρ stereoF stereoOmega f x) (g x) * stereoW n x =
      stereoPhi n x * inner ℝ (dirac ρ f x) (g x) +
        (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x)) := by
    intro x
    rw [diracF_stereo, inner_add_left, real_inner_smul_left, real_inner_smul_left, stereoPhi_eq]
    ring
  have hR : ∀ x, inner ℝ (f x) (diracF ρ stereoF stereoOmega g x) * stereoW n x =
      (stereoPhi n x * inner ℝ (f x) (dirac ρ g x) +
        inner ℝ (f x) (((1 - (n : ℝ)) * stereoW n x) • Yop ρ x (g x))) +
        (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x)) := by
    intro x
    rw [diracF_stereo, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, inner_Yop hρ, stereoPhi_eq]
    ring
  have hcw : Continuous (fun x : E n => -((n : ℝ) - 1) / 2 * stereoW n x) :=
    continuous_const.mul continuous_stereoW
  have ha1 : Integrable (fun x => stereoPhi n x * inner ℝ (dirac ρ f x) (g x)) :=
    integrable_of_cont_supp (k := g)
      (contDiff_stereoPhi.continuous.mul ((continuous_dirac hf).inner hg.continuous)) hgc
      (fun x hx => by simp [hx])
  have ha2 : Integrable
      (fun x => -((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x)) :=
    integrable_of_cont_supp (k := g)
      (hcw.mul ((continuous_Yop_apply hf.continuous).inner hg.continuous)) hgc
      (fun x hx => by simp [hx])
  have hb : Integrable (fun x => stereoPhi n x * inner ℝ (f x) (dirac ρ g x) +
        inner ℝ (f x) (((1 - (n : ℝ)) * stereoW n x) • Yop ρ x (g x))) :=
    integrable_of_cont_supp (k := f)
      ((contDiff_stereoPhi.continuous.mul (hf.continuous.inner (continuous_dirac hg))).add
        (hf.continuous.inner
          ((continuous_const.mul continuous_stereoW).smul
            (continuous_Yop_apply hg.continuous)))) hfc
      (fun x hx => by simp [hx])
  calc ∫ x, inner ℝ (diracF ρ stereoF stereoOmega f x) (g x) * stereoW n x
      = ∫ x, (stereoPhi n x * inner ℝ (dirac ρ f x) (g x) +
          (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x))) :=
        integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = (∫ x, stereoPhi n x * inner ℝ (dirac ρ f x) (g x)) +
          ∫ x, (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x)) :=
        integral_add ha1 ha2
    _ = (∫ x, (stereoPhi n x * inner ℝ (f x) (dirac ρ g x) +
          inner ℝ (f x) (((1 - (n : ℝ)) * stereoW n x) • Yop ρ x (g x)))) +
          ∫ x, (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x)) := by
        rw [hweight]
    _ = ∫ x, ((stereoPhi n x * inner ℝ (f x) (dirac ρ g x) +
          inner ℝ (f x) (((1 - (n : ℝ)) * stereoW n x) • Yop ρ x (g x))) +
          (-((n : ℝ) - 1) / 2 * stereoW n x * inner ℝ (Yop ρ x (f x)) (g x))) :=
        (integral_add hb ha2).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => (hR x).symm)

end Inner

end Lightlike.Dirac
