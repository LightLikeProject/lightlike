import Lightlike.OperatorAlgebras.PureStates
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-!
# The pure states of `C₀(X)` are the points of `X`

N. P. Landsman, *Lecture Notes on C*-Algebras, Hilbert C*-modules, and Quantum Mechanics*, arXiv:math-ph/9807030,
Theorem 2.12.9, p. 46: the pure states of `C₀(X)` correspond to the points of `X`; "the case that `X` is not compact may
be reduced to the compact case by passing from `A = C₀(X)` to `C(X̃)`", the one-point compactification, since a pure
state of `C₀(X)` extends to a pure state of `C(X̃)`.

For a locally compact Hausdorff space `X`:

* `states₀ X`: the positive linear functionals on `C₀(X, ℂ)` of norm one (`sup {ω f | 0 ≤ f ≤ 1} = 1`; Definition 2.8.6,
  p. 36);
* `ext ω`: the extension `ω̃(F) = ω(F - F(∞)) + F(∞)` to `C(OnePoint X, ℂ)`, a state (`ext_mem_states`; Proposition 2.8.7,
  p. 37);
* `isPure₀_iff_exists_eval`: the pure states of `C₀(X)` are the evaluations at the points of `X`.
-/

open scoped ComplexOrder ZeroAtInfty CompactlySupported
open OnePoint

namespace Lightlike.OperatorAlgebras.PureStates

variable (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- `g` takes real values in `[0, 1]`. -/
def IsUnitValued₀ (g : C₀(X, ℂ)) : Prop := ∀ x, (g x).im = 0 ∧ 0 ≤ (g x).re ∧ (g x).re ≤ 1

/-- **The states of `C₀(X)`**: positive linear functionals with `sup {ω f | 0 ≤ f ≤ 1} = 1` (Landsman, Definition 2.8.6,
p. 36: a state on a C*-algebra is "positive and has norm 1"; for a positive functional on `C₀(X)` the norm is this
supremum). -/
def states₀ : Set (C₀(X, ℂ) →ₗ[ℂ] ℂ) :=
  {ω | (∀ f : C₀(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ ω f) ∧ (∀ f, IsUnitValued₀ X f → (ω f).re ≤ 1) ∧
    ∀ ε > 0, ∃ f, IsUnitValued₀ X f ∧ 1 - ε < (ω f).re}

/-- **A pure state of `C₀(X)`**: an extreme point of `states₀ X`. -/
def IsPure₀ (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) : Prop := ω ∈ Set.extremePoints ℝ (states₀ X)

variable {X}

/-- The restriction `F ↦ F - F(∞)` of `C(OnePoint X)` to `C₀(X)`, as a linear map. -/
noncomputable def restr : C(OnePoint X, ℂ) →ₗ[ℂ] C₀(X, ℂ) := ContinuousMap.toZeroAtInftyLinearMap X ℂ ℂ

lemma restr_apply (F : C(OnePoint X, ℂ)) (x : X) : restr F x = F x - F ∞ := rfl

/-- **The extension** `ω̃(F) = ω(F - F(∞)) + F(∞)` of a functional on `C₀(X)` to `C(OnePoint X)` (Landsman,
Proposition 2.8.7, p. 37: `ω_I(A + λI) = ω(A) + λ` on the unitization, here `C(X̃)`). -/
noncomputable def ext (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ :=
  ω ∘ₗ restr + ((ContinuousMap.evalCLM ℂ (∞ : OnePoint X) : C(OnePoint X, ℂ) →L[ℂ] ℂ) : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ)

lemma ext_apply (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) (F : C(OnePoint X, ℂ)) : ext ω F = ω (restr F) + F ∞ := rfl

/-- `restr (f extended by 0) = f`. -/
lemma restr_toOnePoint (f : C₀(X, ℂ)) : restr f.toOnePoint = f := by
  ext x; simp [restr_apply]

/-- `ω̃ (f extended by 0) = ω f`. -/
lemma ext_toOnePoint (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) (f : C₀(X, ℂ)) : ext ω f.toOnePoint = ω f := by
  rw [ext_apply, restr_toOnePoint]; simp

/-- `F = (F - F(∞)) + F(∞)`: `F` is the extension by zero of its restriction plus the constant `F(∞)`. -/
lemma toOnePoint_restr_add (F : C(OnePoint X, ℂ)) :
    F = (restr F).toOnePoint + ContinuousMap.const (OnePoint X) (F ∞) := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp
  | coe x => simp [restr_apply]

/-- The restriction of a functional on `C(OnePoint X)` to `C₀(X)` (extension by zero). -/
noncomputable def res (ρ : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ) : C₀(X, ℂ) →ₗ[ℂ] ℂ :=
  ρ ∘ₗ ZeroAtInftyContinuousMap.toOnePointLinearMap X ℂ ℂ

lemma res_apply (ρ : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ) (f : C₀(X, ℂ)) : res ρ f = ρ f.toOnePoint := rfl

lemma res_ext (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) : res (ext ω) = ω := by
  ext f; rw [res_apply, ext_toOnePoint]

lemma ext_res {ρ : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ} (hρ : ρ ∈ states (OnePoint X)) : ext (res ρ) = ρ := by
  ext F
  rw [ext_apply, res_apply]
  conv_rhs => rw [toOnePoint_restr_add F]
  rw [map_add, show ContinuousMap.const (OnePoint X) (F ∞) = F ∞ • (1 : C(OnePoint X, ℂ)) by ext; simp,
    map_smul, hρ.2, smul_eq_mul, mul_one]

/-- A real-valued nonnegative part as an element of `C₀(X, ℂ)`. -/
noncomputable def posPart₀ (g : C₀(X, ℂ)) (s : ℝ) : C₀(X, ℂ) where
  toFun x := ((max (s * (g x).re) 0 : ℝ) : ℂ)
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    have hc : Continuous fun z : ℂ => ((max (s * z.re) 0 : ℝ) : ℂ) := by fun_prop
    have := (hc.tendsto 0).comp (ZeroAtInftyContinuousMapClass.zero_at_infty g)
    simp only [Complex.zero_re, mul_zero, max_self, Complex.ofReal_zero] at this
    exact this

lemma posPart₀_apply (g : C₀(X, ℂ)) (s : ℝ) (x : X) : posPart₀ g s x = ((max (s * (g x).re) 0 : ℝ) : ℂ) := rfl

lemma posPart₀_nonneg (g : C₀(X, ℂ)) (s : ℝ) (x : X) : 0 ≤ posPart₀ g s x := by
  rw [posPart₀_apply]; exact_mod_cast le_max_right _ _

/-- **The extension of a state of `C₀(X)` is a state of `C(OnePoint X)`**: for `F ≥ 0` with `F(∞) = c`, the restriction
`g = F - c` is real with `g ≥ -c`, so `ω g ≥ -c` since `ω g⁻ ≤ c` (the norm of `ω` is one). -/
theorem ext_mem_states {ω : C₀(X, ℂ) →ₗ[ℂ] ℂ} (hω : ω ∈ states₀ X) : ext ω ∈ states (OnePoint X) := by
  refine ⟨fun F hF => ?_, ?_⟩
  · set c := (F ∞).re
    have hc0 : 0 ≤ c := (Complex.nonneg_iff.mp (hF ∞)).1
    have hFreal : ∀ p, (F p).im = 0 := fun p => (Complex.nonneg_iff.mp (hF p)).2.symm
    have hcinf : F ∞ = (c : ℂ) := Complex.ext rfl (by simp [hFreal])
    set g := restr F
    have hgre : ∀ x, -c ≤ (g x).re := fun x => by
      rw [restr_apply, Complex.sub_re]; linarith [(Complex.nonneg_iff.mp (hF x)).1]
    have hgim : ∀ x, (g x).im = 0 := fun x => by rw [restr_apply, Complex.sub_im, hFreal, hFreal, sub_zero]
    -- `g = g⁺ - g⁻`
    have hdecomp : g = posPart₀ g 1 - posPart₀ g (-1) := by
      ext x
      apply Complex.ext
      · simp only [ZeroAtInftyContinuousMap.sub_apply, posPart₀_apply, Complex.sub_re, Complex.ofReal_re]
        rcases le_total 0 (g x).re with h | h
        · simp [max_eq_left, max_eq_right, h]
        · simp [max_eq_left, max_eq_right, h]
      · simp [ZeroAtInftyContinuousMap.sub_apply, posPart₀_apply, hgim]
    have hp := hω.1 _ (posPart₀_nonneg g 1)
    have hn := hω.1 _ (posPart₀_nonneg g (-1))
    -- `ω g⁻ ≤ c`
    have hnle : (ω (posPart₀ g (-1))).re ≤ c := by
      rcases eq_or_lt_of_le hc0 with h0 | h0
      · have hz : posPart₀ g (-1) = 0 := by
          ext x; rw [posPart₀_apply]
          have := hgre x
          simp only [ZeroAtInftyContinuousMap.zero_apply]
          rw [max_eq_right (by linarith)]; simp
        rw [hz, map_zero, Complex.zero_re]; exact h0.le
      · have hu : IsUnitValued₀ X ((c⁻¹ : ℂ) • posPart₀ g (-1)) := by
          intro x
          simp only [ZeroAtInftyContinuousMap.smul_apply, posPart₀_apply, smul_eq_mul, ← Complex.ofReal_inv,
            ← Complex.ofReal_mul, Complex.ofReal_im, Complex.ofReal_re, true_and]
          refine ⟨by positivity, ?_⟩
          rw [inv_mul_le_iff₀ h0, mul_one]
          exact max_le (by linarith [hgre x]) hc0
        have := hω.2.1 _ hu
        rw [map_smul, smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul] at this
        rwa [inv_mul_le_iff₀ h0, mul_one] at this
    rw [ext_apply, hcinf, show restr F = g from rfl, hdecomp, map_sub]
    rw [Complex.nonneg_iff] at hp hn ⊢
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      add_zero]
    exact ⟨by linarith [hp.1], by rw [← hp.2, ← hn.2, sub_self]⟩
  · rw [ext_apply, show restr (1 : C(OnePoint X, ℂ)) = 0 from by ext x; simp [restr_apply], map_zero, zero_add]
    rfl

/-- The restriction of a state of `C(OnePoint X)` is positive and bounded by one on `[0, 1]`-valued functions. -/
lemma res_pos_le {ρ : C(OnePoint X, ℂ) →ₗ[ℂ] ℂ} (hρ : ρ ∈ states (OnePoint X)) :
    (∀ f : C₀(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ res ρ f) ∧ (∀ f, IsUnitValued₀ X f → (res ρ f).re ≤ 1) := by
  constructor
  · intro f hf
    rw [res_apply]
    refine hρ.1 _ fun p => ?_
    induction p using OnePoint.rec with
    | infty => simp
    | coe x => simpa using hf x
  · intro f hf
    have h := hρ.1 (1 - f.toOnePoint) fun p => by
      induction p using OnePoint.rec with
      | infty => simp
      | coe x =>
        rw [Complex.nonneg_iff]
        simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, ZeroAtInftyContinuousMap.toOnePoint_coe,
          Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, (hf x).1, sub_zero]
        exact ⟨by linarith [(hf x).2.2], by simp⟩
    rw [map_sub, hρ.2, Complex.nonneg_iff, Complex.sub_re, Complex.one_re] at h
    rw [res_apply]; linarith [h.1]

/-- The evaluation at `x` on `C₀(X)`. -/
noncomputable def evalAt₀ (x : X) : C₀(X, ℂ) →ₗ[ℂ] ℂ :=
  res (evalAt (x : OnePoint X))

lemma evalAt₀_apply (x : X) (f : C₀(X, ℂ)) : evalAt₀ x f = f x := by
  show evalAt (x : OnePoint X) f.toOnePoint = f x
  rw [evalAt_apply, ZeroAtInftyContinuousMap.toOnePoint_coe]

lemma ext_evalAt₀ (x : X) : ext (evalAt₀ x) = evalAt (x : OnePoint X) :=
  ext_res (evalAt_mem_states _)

/-- A bump `f ∈ C₀(X)` with values in `[0, 1]` and `f x = 1` (Urysohn). -/
lemma exists_bump (x : X) : ∃ f : C₀(X, ℂ), IsUnitValued₀ X f ∧ f x = 1 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x)) isClosed_empty
      (Set.disjoint_empty _)
  let fc : C_c(X, ℂ) := ⟨⟨fun y => (f y : ℂ), by fun_prop⟩, hfc.comp_left Complex.ofReal_zero⟩
  refine ⟨⟨fc.toContinuousMap, ZeroAtInftyContinuousMapClass.zero_at_infty fc⟩, fun y => ?_, ?_⟩
  · show ((f y : ℂ)).im = 0 ∧ 0 ≤ ((f y : ℂ)).re ∧ ((f y : ℂ)).re ≤ 1
    simpa using hf01 y
  · show ((f x : ℂ)) = 1
    rw [hf1 (Set.mem_singleton x)]; simp

lemma evalAt₀_mem_states₀ (x : X) : evalAt₀ x ∈ states₀ X := by
  refine ⟨(res_pos_le (evalAt_mem_states _)).1, (res_pos_le (evalAt_mem_states _)).2, fun ε hε => ?_⟩
  obtain ⟨f, hf, hfx⟩ := exists_bump x
  exact ⟨f, hf, by rw [evalAt₀_apply, hfx, Complex.one_re]; linarith⟩

/-- `ext` is affine on convex combinations. -/
lemma ext_combo (ρ₁ ρ₂ : C₀(X, ℂ) →ₗ[ℂ] ℂ) {a b : ℝ} (hab : a + b = 1) :
    ext (a • ρ₁ + b • ρ₂) = a • ext ρ₁ + b • ext ρ₂ := by
  ext F
  simp only [ext_apply, LinearMap.add_apply, LinearMap.smul_apply, Complex.real_smul]
  have : (F ∞) = ((a + b : ℝ) : ℂ) * F ∞ := by rw [hab]; simp
  conv_lhs => rw [this]
  push_cast; ring

/-- **Evaluations are pure states of `C₀(X)`.** -/
theorem isPure₀_evalAt₀ (x : X) : IsPure₀ X (evalAt₀ x) := by
  refine ⟨evalAt₀_mem_states₀ x, ?_⟩
  intro ρ₁ hρ₁ ρ₂ hρ₂ hseg
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  have hseg' : evalAt (x : OnePoint X) ∈ openSegment ℝ (ext ρ₁) (ext ρ₂) :=
    ⟨a, b, ha, hb, hab, by rw [← ext_combo ρ₁ ρ₂ hab, hsum, ext_evalAt₀]⟩
  have h1 := (isPure_evalAt (x : OnePoint X)).2 (ext_mem_states hρ₁) (ext_mem_states hρ₂) hseg'
  rw [← res_ext ρ₁, h1]
  rfl

/-- **A pure state of `C₀(X)` extends to a pure state of `C(OnePoint X)`** (Landsman, proof of Theorem 2.12.9). -/
theorem isPure_ext {ω : C₀(X, ℂ) →ₗ[ℂ] ℂ} (hω : IsPure₀ X ω) : IsPure (OnePoint X) (ext ω) := by
  refine ⟨ext_mem_states hω.1, ?_⟩
  intro ρ₁ hρ₁ ρ₂ hρ₂ hseg
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  have hres : a • res ρ₁ + b • res ρ₂ = ω := by
    rw [← res_ext ω, ← hsum]; ext f; simp [res_apply]
  have hb1 := (res_pos_le hρ₁).2
  have hb2 := (res_pos_le hρ₂).2
  have hs₁ : res ρ₁ ∈ states₀ X := by
    refine ⟨(res_pos_le hρ₁).1, hb1, fun ε hε => ?_⟩
    obtain ⟨f, hf, hfε⟩ := hω.1.2.2 (a * ε) (by positivity)
    refine ⟨f, hf, ?_⟩
    have h := congrArg (fun φ : C₀(X, ℂ) →ₗ[ℂ] ℂ => (φ f).re) hres
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.real_smul, Complex.add_re, Complex.re_ofReal_mul]
      at h
    have := hb2 f hf
    nlinarith
  have hs₂ : res ρ₂ ∈ states₀ X := by
    refine ⟨(res_pos_le hρ₂).1, hb2, fun ε hε => ?_⟩
    obtain ⟨f, hf, hfε⟩ := hω.1.2.2 (b * ε) (by positivity)
    refine ⟨f, hf, ?_⟩
    have h := congrArg (fun φ : C₀(X, ℂ) →ₗ[ℂ] ℂ => (φ f).re) hres
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.real_smul, Complex.add_re, Complex.re_ofReal_mul]
      at h
    have := hb1 f hf
    nlinarith
  have h1 := hω.2 hs₁ hs₂ ⟨a, b, ha, hb, hab, hres⟩
  rw [← ext_res hρ₁, h1]

/-- **The pure states of `C₀(X)` are the evaluations at the points of `X`** (Landsman, Theorem 2.12.9, p. 46). -/
theorem isPure₀_iff_exists_eval (ω : C₀(X, ℂ) →ₗ[ℂ] ℂ) : IsPure₀ X ω ↔ ∃ x : X, ω = evalAt₀ x := by
  constructor
  · intro hω
    obtain ⟨y, hy⟩ := (isPure_iff_exists_eval (ext ω)).mp (isPure_ext hω)
    induction y using OnePoint.rec with
    | infty =>
      -- the point at infinity: `ω = 0`, impossible for a state
      exfalso
      obtain ⟨f, -, hf⟩ := hω.1.2.2 (1 / 2) (by norm_num)
      have : ω f = 0 := by
        rw [← ext_toOnePoint ω f, hy, evalAt_apply, ZeroAtInftyContinuousMap.toOnePoint_infty]
      rw [this, Complex.zero_re] at hf
      norm_num at hf
    | coe x =>
      refine ⟨x, ?_⟩
      rw [← res_ext ω, hy]
      rfl
  · rintro ⟨x, rfl⟩
    exact isPure₀_evalAt₀ x

end Lightlike.OperatorAlgebras.PureStates
