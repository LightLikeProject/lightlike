module

public import Mathlib
public import Lightlike.Spacetime.WaveEquationGreenOperators.Abstract
public import Lightlike.Spacetime.WaveEquationGreenOperators.Minkowski2c

/-!
# Cauchy uniqueness and uniqueness of the Green operators in 1+1 Minkowski (row G1-059)

A solution `h` of the wave equation `box h = 0` on `ℝ²` (light-cone coordinates) which is
*partially differentiable* (`PartDiff`: `v ↦ h (u, v)` differentiable, and `u ↦ ∂ᵥ h (u, v)`
differentiable; true for `C²` functions and for `Gret f`) and whose support lies in a quadrant
`{u > -R, v > -R}` vanishes (`eq_zero_of_box_eq_zero`).  Hence such an `h` supported in the future
cone `Jp (supp f)` of a test function `f` vanishes (`cauchyUnique_box`).  The abstract uniqueness
statement of `Abstract.lean` has to be restricted to regular solutions (for a non-differentiable `h`
the junk value `deriv h = 0` makes `box h = 0` meaningless), so we state the restricted version
`CauchyUniqueOn` and `IsGreen.eq_of_cauchyUniqueOn`, and conclude with `Gret_isGreen` and
`Gret_unique`: `Gret` is a retarded Green operator of `box` (BGP key `bgp-2007`, Section 3.4), and any
retarded Green operator of `box` with `PartDiff` (e.g. `C²`) values equals `Gret` on test functions.

* `CauchyUniqueOn`, `IsGreen.eq_of_cauchyUniqueOn`: regularity-restricted abstract uniqueness;
* `PartDiff`, `PartDiff.sub`, `ContDiff.partDiff`, `Gret_partDiff`: the regularity class;
* `eq_zero_of_box_eq_zero`, `cauchyUnique_box`: the concrete Cauchy uniqueness;
* `Test`, `Gret_isGreen`, `Gret_unique`: existence and uniqueness of the retarded operator.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.GreenOps

/-- Cauchy uniqueness restricted to the solutions satisfying the regularity predicate `Cls`. -/
def CauchyUniqueOn {M : Type*} (Cls : (M → ℝ) → Prop) (P : (M → ℝ) → (M → ℝ))
    (Test : (M → ℝ) → Prop) (J : Set M → Set M) : Prop :=
  ∀ h f : M → ℝ, Cls h → Test f → P h = 0 → Function.support h ⊆ J (Function.support f) → h = 0

/-- Uniqueness of Green operators whose values on a test function `f` satisfy `Cls`, from
`CauchyUniqueOn`; `Cls` is assumed stable under subtraction. -/
theorem IsGreen.eq_of_cauchyUniqueOn {M : Type*} {Cls : (M → ℝ) → Prop} {P : (M → ℝ) → (M → ℝ)}
    {Test : (M → ℝ) → Prop} {J : Set M → Set M}
    (hP : ∀ g h, Cls g → Cls h → P (g - h) = P g - P h)
    (hCls : ∀ g h, Cls g → Cls h → Cls (g - h)) (hU : CauchyUniqueOn Cls P Test J)
    {G G' : (M → ℝ) → (M → ℝ)} (hG : IsGreen P Test J G) (hG' : IsGreen P Test J G')
    {f : M → ℝ} (hf : Test f) (h1 : Cls (G f)) (h2 : Cls (G' f)) : G f = G' f := by
  have h0 : P (G f - G' f) = 0 := by
    rw [hP _ _ h1 h2, hG.left_inv f hf, hG'.left_inv f hf, sub_self]
  have hs : Function.support (G f - G' f) ⊆ J (Function.support f) := by
    intro x hx
    by_cases e1 : G f x = 0
    · have : G' f x ≠ 0 := by
        intro e2
        exact hx (by simp [e1, e2])
      exact hG'.supp_subset f hf this
    · exact hG.supp_subset f hf e1
  exact sub_eq_zero.mp (hU _ f (hCls _ _ h1 h2) hf h0 hs)

end Lightlike.GreenOps

namespace Lightlike.GreenOps.Mink2

/-- Partial differentiability: `v ↦ h (u, v)` is differentiable for every `u`, and
`u ↦ ∂ᵥ h (u, v)` is differentiable for every `v`.  This is what `box h` needs to be meaningful. -/
def PartDiff (h : ℝ × ℝ → ℝ) : Prop :=
  (∀ u, Differentiable ℝ fun v => h (u, v)) ∧
    ∀ v, Differentiable ℝ fun u => deriv (fun v' => h (u, v')) v

/-- `PartDiff` is stable under subtraction. -/
lemma PartDiff.sub {g h : ℝ × ℝ → ℝ} (hg : PartDiff g) (hh : PartDiff h) : PartDiff (g - h) := by
  refine ⟨fun u => (hg.1 u).sub (hh.1 u), fun v => ?_⟩
  have : (fun u => deriv (fun v' => (g - h) (u, v')) v) =
      fun u => deriv (fun v' => g (u, v')) v - deriv (fun v' => h (u, v')) v := by
    funext u
    exact deriv_sub (hg.1 u v) (hh.1 u v)
  rw [this]
  exact (hg.2 v).sub (hh.2 v)

/-- `C²` functions are `PartDiff`. -/
lemma _root_.ContDiff.partDiff {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h) : PartDiff h := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hgd : ContDiff ℝ 1 (fun p => fderiv ℝ h p (0, 1)) :=
    (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  refine ⟨fun u => (hh1.differentiable one_ne_zero).comp
    ((differentiable_const u).prodMk differentiable_id), fun v => ?_⟩
  have : (fun u => deriv (fun v' => h (u, v')) v) = fun u => fderiv ℝ h (u, v) (0, 1) :=
    funext fun u => deriv_slice2 hh1 u v
  rw [this]
  exact (hgd.differentiable one_ne_zero).comp (differentiable_id.prodMk (differentiable_const v))

/-- `Gret f` is `PartDiff` for continuous compactly supported `f`. -/
lemma Gret_partDiff {f : ℝ × ℝ → ℝ} (hc : Continuous f) (hcs : HasCompactSupport f) :
    PartDiff (Gret f) := by
  obtain ⟨R, hR⟩ := exists_bound hcs
  have step : ∀ u v : ℝ, deriv (fun v' => Gret f (u, v')) v = 1 / 4 * ∫ a in Iic u, f (a, v) := by
    intro u v
    have h := (hasDerivAt_integral_Iic (continuous_phi hc hR u) (integrable_phi hc hR u) v)
    exact (h.const_mul (1 / 4)).deriv
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · have h := (hasDerivAt_integral_Iic (continuous_phi hc hR u) (integrable_phi hc hR u) v)
    exact (h.const_mul (1 / 4)).differentiableAt
  · have h2 : (fun u => deriv (fun v' => Gret f (u, v')) v) =
        fun u => 1 / 4 * ∫ a in Iic u, f (a, v) := funext fun u => step u v
    rw [h2]
    intro u
    exact ((hasDerivAt_integral_Iic (g := fun a => f (a, v)) (by fun_prop)
      (integrable_slice1 hc hR v) u).const_mul (1 / 4)).differentiableAt

/-- A `PartDiff` solution of `box h = 0` supported in the quadrant `{u > -R, v > -R}` vanishes. -/
theorem eq_zero_of_box_eq_zero {h : ℝ × ℝ → ℝ} (hh : PartDiff h) {R : ℝ}
    (hz : ∀ p, h p ≠ 0 → -R < p.1 ∧ -R < p.2) (hb : box h = 0) : h = 0 := by
  have hu0 : ∀ v, h (-R - 1, v) = 0 := by
    intro v
    by_contra hne
    have := (hz _ hne).1
    simp only at this
    linarith
  have hv0 : ∀ u, h (u, -R - 1) = 0 := by
    intro u
    by_contra hne
    have := (hz _ hne).2
    simp only at this
    linarith
  -- step 1: the partial derivative `∂ᵥ h` vanishes
  have step1 : ∀ u v, deriv (fun v' => h (u, v')) v = 0 := by
    intro u v
    have hder : ∀ u', deriv (fun u'' => deriv (fun v' => h (u'', v')) v) u' = 0 := by
      intro u'
      have := congrFun hb (u', v)
      unfold box at this
      dsimp only at this
      simpa using this
    have hc := is_const_of_deriv_eq_zero (hh.2 v) hder u (-R - 1)
    rw [hc]
    have : (fun v' => h (-R - 1, v')) = fun _ => 0 := funext hu0
    rw [this]
    simp
  funext ⟨u, v⟩
  have hc := is_const_of_deriv_eq_zero (hh.1 u) (fun v' => step1 u v') v (-R - 1)
  simpa [hv0 u] using hc

/-- The set of test functions: `C²` with compact support. -/
def Test (f : ℝ × ℝ → ℝ) : Prop := ContDiff ℝ 2 f ∧ HasCompactSupport f

/-- Cauchy uniqueness for `box` among `PartDiff` solutions with support in the future cone
`Jp (supp f)` of a test function. -/
theorem cauchyUnique_box : CauchyUniqueOn PartDiff box Test Jp := by
  intro h f hh hf hb hs
  obtain ⟨R, hR⟩ := exists_bound hf.2
  refine eq_zero_of_box_eq_zero hh (R := R) (fun p hp => ?_) hb
  obtain ⟨q, hq, h1, h2⟩ := hs hp
  have := hR q hq
  constructor
  · linarith [(abs_lt.mp this.1).1]
  · linarith [(abs_lt.mp this.2).1]

/-- `box` is additive (on `PartDiff` functions it is the difference rule; here for the
arguments we need). -/
lemma box_sub {g h : ℝ × ℝ → ℝ} (hg : PartDiff g) (hh : PartDiff h) :
    box (g - h) = box g - box h := by
  funext p
  unfold box
  have e : (fun u => deriv (fun v => (g - h) (u, v)) p.2) =
      fun u => deriv (fun v => g (u, v)) p.2 - deriv (fun v => h (u, v)) p.2 :=
    funext fun u => deriv_sub (hg.1 u p.2) (hh.1 u p.2)
  rw [e]
  have := deriv_sub (hg.2 p.2 p.1) (hh.2 p.2 p.1)
  simp only [Pi.sub_apply]
  have h' : deriv (fun u => deriv (fun v => g (u, v)) p.2 - deriv (fun v => h (u, v)) p.2) p.1 =
      deriv (fun u => deriv (fun v => g (u, v)) p.2) p.1 -
        deriv (fun u => deriv (fun v => h (u, v)) p.2) p.1 := this
  rw [h']
  ring

/-- **Existence** (retarded half): `Gret` is a retarded Green operator of `box` on the test
functions, with support rule `Jp` (BGP key `bgp-2007`, Section 3.4). -/
theorem Gret_isGreen : IsGreen box Test Jp Gret where
  left_inv _ hf := box_Gret hf.1.continuous hf.2
  right_inv _ hf := Gret_box hf.1 hf.2
  supp_subset f _ := support_Gret_subset f

/-- **Uniqueness** (retarded half): a retarded Green operator `G` of `box` whose value on the test
function `f` is `PartDiff` (e.g. `C²`) agrees with `Gret` on `f`. -/
theorem Gret_unique {G : (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)} (hG : IsGreen box Test Jp G) {f : ℝ × ℝ → ℝ}
    (hf : Test f) (hGf : PartDiff (G f)) : Gret f = G f :=
  IsGreen.eq_of_cauchyUniqueOn (fun _ _ hg hh => box_sub hg hh) (fun _ _ hg hh => PartDiff.sub hg hh) cauchyUnique_box
    Gret_isGreen hG hf (Gret_partDiff hf.1.continuous hf.2) hGf

end Lightlike.GreenOps.Mink2
