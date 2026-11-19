import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Topology.ContinuousMap.StarOrdered
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# The pure states of `C(X)` are the points of `X`

N. P. Landsman, *Lecture Notes on C*-Algebras, Hilbert C*-modules, and Quantum Mechanics*, arXiv:math-ph/9807030
(read): Definition 2.12.1, p. 44 (a pure state is an extreme point of the state space), Proposition 2.12.8, p. 46, and
Theorem 2.12.9, p. 46 ("The pure state space of the commutative C*-algebra `C₀(X)` ... is homeomorphic to `X`"; the
proof establishes "a bijective correspondence between the pure states and the multiplicative functionals on `C₀(X)`",
for `X` compact first).

For a compact Hausdorff space `X`:

* `states X`: the positive linear functionals `ω` on `C(X, ℂ)` with `ω 1 = 1`; `IsPure`: extreme points of `states X`;
* `mul_of_isPure`: a pure state is multiplicative (Landsman's argument: `ω_g = ω(· g)` for `0 ≤ g ≤ 1` is a multiple of
  `ω`);
* `exists_eq_eval_of_mul`: a multiplicative state is the evaluation at a point (its kernel is a maximal ideal of
  `C(X, ℂ)`, Mathlib's `ContinuousMap.ideal_isMaximal_iff`);
* `isPure_eval`: every evaluation is pure;
* `isPure_iff_exists_eval`, `isPure_iff_mul`: the pure states are exactly the evaluations at points, and exactly the
  multiplicative states. With Mathlib's `WeakDual.CharacterSpace.homeoEval` (`X ≃ₜ` the characters of `C(X, ℂ)`) this
  is Theorem 2.12.9 for compact `X`.
-/

open scoped ComplexOrder

namespace Lightlike.OperatorAlgebras.PureStates

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **The states of `C(X)`**: linear functionals that are positive (`ω f ≥ 0` when `f ≥ 0` pointwise) with
`ω 1 = 1` (Landsman, Definition 2.8.1, p. 35; the positive elements of `C(X)` are the pointwise nonnegative functions). -/
def states : Set (C(X, ℂ) →ₗ[ℂ] ℂ) := {ω | (∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ ω f) ∧ ω 1 = 1}

/-- **A pure state**: an extreme point of the state space (Landsman, Definition 2.12.1, p. 44). -/
def IsPure (ω : C(X, ℂ) →ₗ[ℂ] ℂ) : Prop := ω ∈ Set.extremePoints ℝ (states X)

variable {X}

/-! ### Decomposition into functions with values in `[0, 1]` -/

/-- `f` takes real values in `[0, 1]`. -/
def IsUnitValued (g : C(X, ℂ)) : Prop := ∀ x, (g x).im = 0 ∧ 0 ≤ (g x).re ∧ (g x).re ≤ 1

lemma nonneg_of_isUnitValued {g : C(X, ℂ)} (hg : IsUnitValued g) (x : X) : 0 ≤ g x := by
  rw [Complex.nonneg_iff]; exact ⟨(hg x).2.1, (hg x).1.symm⟩

lemma one_sub_nonneg_of_isUnitValued {g : C(X, ℂ)} (hg : IsUnitValued g) (x : X) : 0 ≤ (1 - g) x := by
  rw [Complex.nonneg_iff]
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, (hg x).1, sub_zero]
  exact ⟨by linarith [(hg x).2.2], by simp⟩

/-- The continuous function `x ↦ max (u x) 0 / M`, real-valued in `ℂ`. -/
noncomputable def posPart (u : C(X, ℝ)) (M : ℝ) : C(X, ℂ) :=
  ⟨fun x => ((max (u x) 0 / M : ℝ) : ℂ), by fun_prop⟩

lemma posPart_apply (u : C(X, ℝ)) (M : ℝ) (x : X) : posPart u M x = ((max (u x) 0 / M : ℝ) : ℂ) := rfl

lemma isUnitValued_posPart {u : C(X, ℝ)} {M : ℝ} (hM : 0 < M) (hu : ∀ x, |u x| ≤ M) :
    IsUnitValued (posPart u M) := by
  intro x
  simp only [posPart_apply, Complex.ofReal_im, Complex.ofReal_re, true_and]
  refine ⟨by positivity, (div_le_one hM).mpr (max_le ?_ hM.le)⟩
  exact (le_abs_self _).trans (hu x)

/-- **Every function is a combination of four `[0, 1]`-valued functions**: the positive and negative parts of the real
and the imaginary part, divided by `M > ‖f‖`; if `f x = 0`, all four vanish at `x`. -/
lemma exists_decomp (f : C(X, ℂ)) :
    ∃ (c : Fin 4 → ℂ) (g : Fin 4 → C(X, ℂ)), (∀ k, IsUnitValued (g k)) ∧ f = ∑ k, c k • g k ∧
      ∀ x, f x = 0 → ∀ k, g k x = 0 := by
  set M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by positivity
  have hb : ∀ x, ‖f x‖ ≤ M := fun x => (f.norm_coe_le_norm x).trans (by linarith)
  let re : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let im : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have hre : ∀ x, |re x| ≤ M := fun x => (Complex.abs_re_le_norm _).trans (hb x)
  have him : ∀ x, |im x| ≤ M := fun x => (Complex.abs_im_le_norm _).trans (hb x)
  have hre' : ∀ x, |(-re) x| ≤ M := fun x => by simpa using hre x
  have him' : ∀ x, |(-im) x| ≤ M := fun x => by simpa using him x
  refine ⟨![(M : ℂ), -(M : ℂ), Complex.I * M, -(Complex.I * M)], ![posPart re M, posPart (-re) M, posPart im M,
    posPart (-im) M], ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    exacts [isUnitValued_posPart hM hre, isUnitValued_posPart hM hre', isUnitValued_posPart hM him,
      isUnitValued_posPart hM him']
  · ext x
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul, posPart_apply, ContinuousMap.neg_apply]
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    apply Complex.ext <;> simp [re, im, Complex.mul_re, Complex.mul_im] <;> field_simp <;>
      rcases le_total 0 (f x).re with h | h <;> rcases le_total 0 (f x).im with h' | h' <;>
      simp [max_eq_left, max_eq_right, h, h'] <;> linarith
  · intro x hx k
    fin_cases k <;> simp [posPart_apply, re, im, hx]

/-! ### Pure states are multiplicative -/

variable {ω : C(X, ℂ) →ₗ[ℂ] ℂ}

lemma map_nonneg_of_isUnitValued (hω : ω ∈ states X) {g : C(X, ℂ)} (hg : IsUnitValued g) : 0 ≤ ω g :=
  hω.1 g (nonneg_of_isUnitValued hg)

/-- `0 ≤ ω (f g) ≤ ω g` for `[0, 1]`-valued `f`, `g`. -/
lemma map_mul_le (hω : ω ∈ states X) {f g : C(X, ℂ)} (hf : IsUnitValued f) (hg : IsUnitValued g) :
    0 ≤ ω (f * g) ∧ ω (f * g) ≤ ω g := by
  constructor
  · refine hω.1 _ fun x => ?_
    rw [ContinuousMap.mul_apply]
    exact mul_nonneg (nonneg_of_isUnitValued hf x) (nonneg_of_isUnitValued hg x)
  · have h := hω.1 ((1 - f) * g) fun x => by
      rw [ContinuousMap.mul_apply]
      exact mul_nonneg (one_sub_nonneg_of_isUnitValued hf x) (nonneg_of_isUnitValued hg x)
    rw [sub_mul, one_mul, map_sub] at h
    exact sub_nonneg.mp h

/-- If `ω g = 0` for a `[0, 1]`-valued `g`, then `ω (f g) = 0` for every `f`. -/
lemma map_mul_eq_zero (hω : ω ∈ states X) {g : C(X, ℂ)} (hg : IsUnitValued g) (h0 : ω g = 0) (f : C(X, ℂ)) :
    ω (f * g) = 0 := by
  obtain ⟨c, p, hp, rfl, -⟩ := exists_decomp f
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [smul_mul_assoc, map_smul]
  have h := map_mul_le hω (hp k) hg
  rw [h0] at h
  rw [le_antisymm h.2 h.1, smul_zero]

/-- **Landsman, Theorem 2.12.9 (the converse direction)**: for a pure state `ω` and a `[0, 1]`-valued `g`,
`ω (f g) = ω f ω g`. -/
lemma map_mul_of_isUnitValued (hω : IsPure X ω) {g : C(X, ℂ)} (hg : IsUnitValued g) (f : C(X, ℂ)) :
    ω (f * g) = ω f * ω g := by
  have hs := hω.1
  -- `t = ω g` is real in `[0, 1]`
  have ht0 := map_nonneg_of_isUnitValued hs hg
  have h1g : IsUnitValued (1 - g) := fun x => by
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, (hg x).1, sub_zero]
    exact ⟨by simp, by linarith [(hg x).2.2], by linarith [(hg x).2.1]⟩
  have ht1 := map_nonneg_of_isUnitValued hs h1g
  rw [map_sub, hs.2] at ht1
  rw [Complex.nonneg_iff] at ht0 ht1
  set t := ω g
  have him : t.im = 0 := ht0.2.symm
  have htc : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rcases eq_or_lt_of_le ht0.1 with h0 | h0
  · -- `ω g = 0`
    have : t = 0 := Complex.ext h0.symm him
    rw [map_mul_eq_zero hs hg this f, this, mul_zero]
  rcases eq_or_lt_of_le (show t.re ≤ 1 by simpa using ht1.1) with h1 | h1
  · -- `ω (1 - g) = 0`
    have ht1' : t = 1 := Complex.ext (by simpa using h1) (by simpa using him)
    have hz : ω (1 - g) = 0 := by
      rw [map_sub, hs.2]
      show 1 - t = 0
      rw [ht1', sub_self]
    have := map_mul_eq_zero hs h1g hz f
    rw [mul_sub, mul_one, map_sub, sub_eq_zero] at this
    rw [← this]
    show ω f = ω f * t
    rw [ht1', mul_one]
  · -- `0 < t < 1`: `ω = t ω₁ + (1 - t) ω₂` with `ω₁ = ω(· g)/t`, `ω₂ = ω(· (1 - g))/(1 - t)`
    set ω₁ : C(X, ℂ) →ₗ[ℂ] ℂ := ((t⁻¹ : ℂ)) • (ω ∘ₗ LinearMap.mulRight ℂ g)
    set ω₂ : C(X, ℂ) →ₗ[ℂ] ℂ := (((1 - t)⁻¹ : ℂ)) • (ω ∘ₗ LinearMap.mulRight ℂ (1 - g))
    have htne : t ≠ 0 := fun h => by rw [h] at h0; simp at h0
    have ht1ne : 1 - t ≠ 0 := fun h => by
      have : t.re = 1 := by have := congrArg Complex.re h; simp at this; linarith
      linarith
    have hω₁ : ω₁ ∈ states X := by
      refine ⟨fun f hf => ?_, ?_⟩
      · simp only [ω₁, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, smul_eq_mul]
        refine mul_nonneg ?_ (hs.1 _ fun x => ?_)
        · rw [htc, ← Complex.ofReal_inv]; exact_mod_cast (inv_pos.mpr h0).le
        · rw [ContinuousMap.mul_apply]; exact mul_nonneg (hf x) (nonneg_of_isUnitValued hg x)
      · simp only [ω₁, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul, smul_eq_mul]
        exact inv_mul_cancel₀ htne
    have hω₂ : ω₂ ∈ states X := by
      refine ⟨fun f hf => ?_, ?_⟩
      · simp only [ω₂, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, smul_eq_mul]
        refine mul_nonneg ?_ (hs.1 _ fun x => ?_)
        · rw [htc, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv]
          exact_mod_cast (inv_pos.mpr (by linarith)).le
        · rw [ContinuousMap.mul_apply]; exact mul_nonneg (hf x) (one_sub_nonneg_of_isUnitValued hg x)
      · simp only [ω₂, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul, smul_eq_mul,
          map_sub, hs.2]
        exact inv_mul_cancel₀ ht1ne
    have hseg : ω ∈ openSegment ℝ ω₁ ω₂ := by
      refine ⟨t.re, 1 - t.re, h0, by linarith, by ring, ?_⟩
      ext f
      have hfg : ω (f * (1 - g)) = ω f - ω (f * g) := by rw [mul_sub, mul_one, map_sub]
      simp only [ω₁, ω₂, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
        smul_eq_mul, Complex.real_smul, hfg]
      rw [show ((1 - t.re : ℝ) : ℂ) = 1 - t by push_cast; rw [← htc], ← htc]
      field_simp
      ring
    have h₁ := hω.2 hω₁ hω₂ hseg
    have := congrArg (fun φ : C(X, ℂ) →ₗ[ℂ] ℂ => φ f) h₁
    simp only [ω₁, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, smul_eq_mul] at this
    calc ω (f * g) = t * (t⁻¹ * ω (f * g)) := by rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul]
      _ = t * ω f := by rw [this]
      _ = ω f * t := mul_comm _ _

/-- **A pure state is multiplicative.** -/
theorem mul_of_isPure (hω : IsPure X ω) (f g : C(X, ℂ)) : ω (f * g) = ω f * ω g := by
  obtain ⟨c, p, hp, rfl, -⟩ := exists_decomp g
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, map_mul_of_isUnitValued hω (hp _)]
  try simp [Finset.mul_sum, mul_left_comm]

/-! ### Multiplicative states are evaluations, evaluations are pure -/

/-- A state as a positive linear map, which is continuous on the C*-algebra `C(X, ℂ)`. -/
lemma continuous_of_mem_states (hω : ω ∈ states X) : Continuous ω := by
  let ω' : C(X, ℂ) →ₚ[ℂ] ℂ :=
    { ω with
      monotone' := fun f g hfg => by
        have := hω.1 (g - f) fun x => sub_nonneg.mpr (hfg x)
        rw [map_sub] at this
        exact sub_nonneg.mp this }
  exact map_continuous ω'

/-- **A multiplicative state is the evaluation at a point** (its kernel is a closed maximal ideal of `C(X, ℂ)`). -/
theorem exists_eq_eval_of_mul (hω : ω ∈ states X) (hmul : ∀ f g, ω (f * g) = ω f * ω g) :
    ∃ x : X, ∀ f, ω f = f x := by
  let φ : C(X, ℂ) →+* ℂ :=
    { toFun := ω, map_one' := hω.2, map_mul' := hmul, map_zero' := map_zero ω, map_add' := map_add ω }
  have hsurj : Function.Surjective φ := fun z => ⟨z • 1, by simp [φ, hω.2]⟩
  have hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hclosed : IsClosed (RingHom.ker φ : Set C(X, ℂ)) :=
    isClosed_singleton.preimage (continuous_of_mem_states hω)
  obtain ⟨x, hx⟩ := (ContinuousMap.ideal_isMaximal_iff (RingHom.ker φ)).mp hmax
  refine ⟨x, fun f => ?_⟩
  have hmem : f - f x • 1 ∈ RingHom.ker φ := by
    rw [← hx, ContinuousMap.mem_idealOfSet_compl_singleton]
    simp
  rw [RingHom.mem_ker] at hmem
  have : ω (f - f x • 1) = 0 := hmem
  rw [map_sub, map_smul, hω.2, smul_eq_mul, mul_one, sub_eq_zero] at this
  exact this

/-- The evaluation at `x` as a linear functional. -/
noncomputable def evalAt (x : X) : C(X, ℂ) →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ x : C(X, ℂ) →L[ℂ] ℂ)

@[simp] lemma evalAt_apply (x : X) (f : C(X, ℂ)) : evalAt x f = f x := rfl

lemma evalAt_mem_states (x : X) : evalAt x ∈ states X := ⟨fun f hf => hf x, by simp⟩

/-- **Every evaluation is pure** (Landsman, proof of Theorem 2.12.9): a state `ω₁` with `t ω₁ ≤ ω_x` vanishes on the
functions vanishing at `x`, so `ω₁ = ω_x`. -/
theorem isPure_evalAt (x : X) : IsPure X (evalAt x) := by
  refine ⟨evalAt_mem_states x, ?_⟩
  intro ω₁ hω₁ ω₂ hω₂ hseg
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  -- a state below a multiple of `ω_x` is `ω_x`
  have key : ∀ {ρ σ : C(X, ℂ) →ₗ[ℂ] ℂ} {a b : ℝ}, ρ ∈ states X → σ ∈ states X → 0 < a → 0 < b →
      a • ρ + b • σ = evalAt x → ρ = evalAt x := by
    intro ρ σ a b hρ hσ ha hb hs
    have hvan : ∀ g : C(X, ℂ), IsUnitValued g → g x = 0 → ρ g = 0 := by
      intro g hg hgx
      have h := congrArg (fun φ : C(X, ℂ) →ₗ[ℂ] ℂ => φ g) hs
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.real_smul, evalAt_apply, hgx] at h
      have hρ0 := map_nonneg_of_isUnitValued hρ hg
      have hσ0 := map_nonneg_of_isUnitValued hσ hg
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.zero_re] at hre
      rw [Complex.nonneg_iff] at hρ0 hσ0
      have : (ρ g).re = 0 := by nlinarith [hρ0.1, hσ0.1]
      exact Complex.ext this hρ0.2.symm
    ext f
    obtain ⟨c, p, hp, hfeq, hpx⟩ := exists_decomp (f - f x • 1)
    have h0 : ρ (f - f x • 1) = 0 := by
      rw [hfeq, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_smul, hvan _ (hp k) (hpx x (by simp) k), smul_zero]
    rw [map_sub, map_smul, hρ.2, smul_eq_mul, mul_one, sub_eq_zero] at h0
    rw [h0, evalAt_apply]
  exact key hω₁ hω₂ ha hb hsum

/-- **The pure states of `C(X)` are the evaluations at points** (Landsman, Theorem 2.12.9, p. 46). -/
theorem isPure_iff_exists_eval (ω : C(X, ℂ) →ₗ[ℂ] ℂ) : IsPure X ω ↔ ∃ x : X, ω = evalAt x := by
  constructor
  · intro hω
    obtain ⟨x, hx⟩ := exists_eq_eval_of_mul hω.1 (mul_of_isPure hω)
    exact ⟨x, LinearMap.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact isPure_evalAt x

/-- **The pure states of `C(X)` are the multiplicative states** (Landsman, proof of Theorem 2.12.9, p. 46). -/
theorem isPure_iff_mul (ω : C(X, ℂ) →ₗ[ℂ] ℂ) :
    IsPure X ω ↔ ω ∈ states X ∧ ∀ f g, ω (f * g) = ω f * ω g := by
  constructor
  · intro hω; exact ⟨hω.1, mul_of_isPure hω⟩
  · rintro ⟨hs, hmul⟩
    obtain ⟨x, hx⟩ := exists_eq_eval_of_mul hs hmul
    rw [show ω = evalAt x from LinearMap.ext hx]
    exact isPure_evalAt x

end Lightlike.OperatorAlgebras.PureStates
