import Lightlike.Asymptotics.EPRL.FiniteMax
import Lightlike.Asymptotics.EPRL.MaxSet
import Lightlike.Asymptotics.EPRL.Critical
import Lightlike.Asymptotics.EPRL.Formula

/-!
# The maximum set as sign lifts, and the Hessian at each of its points

For the Regge state, spins proportional to the areas and even node sums, the gauge-fixed amplitude
`F(Y) = F_n(Y, 1)` on `SU(2)^4` has `|F| = 1` exactly at the `2 · 16` points `signPt c s`, `c` one
of the two critical classes and `s ∈ {±}^4` a sign pattern.

At every such point the amplitude in the gnomonic chart is the amplitude in the gnomonic chart
around the class representative (`chart_signPt`), so the first and second derivatives, and the
value, do not depend on the sign pattern. The Hessian is `4 P H P` with `H` the Hessian of the
class (`hessMat_qchart`), which gives the factor `(4^{-1/2})^{12} = 2^{-12}` in the constant of the
asymptotic formula.
-/

open Matrix Finset Filter MeasureTheory Complex
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4 Lightlike.Oscillatory Lightlike.Regge4

/-- The point of `SU(2)^4` with the sign pattern `s` applied to the class representative `c`. -/
noncomputable def signPt (c : Fin 5 → SU2) (s : Fin 4 → Bool) : Fin 4 → SU2 :=
  fun a => if s a then SU2.negOne * c a.castSucc else c a.castSucc

/-- The coercion of the sign point with a final `1` is the sign lift of the class. -/
lemma snoc_signPt_coe (c : Fin 5 → SU2) (hc4 : (c 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (s : Fin 4 → Bool) :
    (fun a => ((Fin.snoc (signPt c s) (1 : SU2) : Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ)) =
      signLift (fun a => (c a : Matrix (Fin 2) (Fin 2) ℂ)) (Fin.snoc s false) := by
  funext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last, signLift]
    simp [hc4]
  · simp only [Fin.snoc_castSucc, signLift, signPt]
    by_cases h : s i = true
    · simp [h, SU2.negOne_coe]
    · simp [h]

/-- `signLift` commutes with the gnomonic chart. -/
lemma qchart_signLift (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 5 → Bool) (q : Fin 12 → ℝ) :
    qchart (signLift X s) q = signLift (qchart X q) s := by
  funext a
  by_cases h : (a : ℕ) < 4
  · by_cases hs : s a = true <;> simp [qchart, signLift, h, hs]
  · by_cases hs : s a = true <;> simp [qchart, signLift, h, hs]

/-- `signLift` commutes with the exponential chart. -/
lemma chart_signLift (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 5 → Bool) (θ : Fin 12 → ℝ) :
    chart (signLift X s) θ = signLift (chart X θ) s := by
  funext a
  by_cases h : (a : ℕ) < 4
  · by_cases hs : s a = true <;> simp [chart, signLift, h, hs]
  · by_cases hs : s a = true <;> simp [chart, signLift, h, hs]

/-- The gauge-fixed amplitude with a final `1`. -/
noncomputable def gaugeF (n : Fin 10 → ℕ) (g : BdryData) (Y : Fin 4 → SU2) : ℂ :=
  cohF n g (Fin.snoc Y 1)

/-- **The amplitude around a sign point is the amplitude around the class**, in the gnomonic
chart: for even node sums, `F(chartMap (signPt c s) q) = F_n(qchart c q)`. -/
lemma gaugeF_chartMap_signPt (n : Fin 10 → ℕ) (g : BdryData)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (c : Fin 5 → SU2)
    (hc4 : (c 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1) (s : Fin 4 → Bool) (q : Fin 12 → ℝ) :
    gaugeF n g (chartMap (signPt c s) q) =
      cohAmp n g (qchart (fun a => (c a : Matrix (Fin 2) (Fin 2) ℂ)) q) := by
  have h1 := snoc_gamma_eq_qchart (signPt c s) q
  have h2 := snoc_signPt_coe c hc4 s
  unfold gaugeF cohF chartMap
  rw [h1, h2, qchart_signLift, cohAmp_signLift n g _ hev]

/-- The value at a sign point is the value at the class. -/
lemma gaugeF_signPt (n : Fin 10 → ℕ) (g : BdryData)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (c : Fin 5 → SU2)
    (hc4 : (c 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1) (s : Fin 4 → Bool) :
    gaugeF n g (signPt c s) = cohAmp n g (fun a => (c a : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold gaugeF cohF
  rw [snoc_signPt_coe c hc4 s, cohAmp_signLift n g _ hev]

/-- **The Hessian at a sign point**: `-(F p)⁻¹ H_q = 4 P (-H) P`, `H` the Hessian of the class in
the exponential chart. -/
lemma neg_hess_signPt (n : Fin 10 → ℕ) (g : BdryData)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (c : Fin 5 → SU2)
    (hc4 : (c 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1) (s : Fin 4 → Bool) :
    -((gaugeF n g (signPt c s))⁻¹ •
        hessMat (fun q => gaugeF n g (chartMap (signPt c s) q)) 0) =
      (4 : ℂ) • (-hessAmp n g (fun a => (c a : Matrix (Fin 2) (Fin 2) ℂ))).submatrix perm12 perm12 := by
  have hfun : (fun q => gaugeF n g (chartMap (signPt c s) q)) =
      fun q => cohAmp n g (qchart (fun a => (c a : Matrix (Fin 2) (Fin 2) ℂ)) q) :=
    funext (gaugeF_chartMap_signPt n g hev c hc4 s)
  rw [hfun, gaugeF_signPt n g hev c hc4 s, hessMat_qchart]
  ext i j
  simp [hessAmp, Matrix.smul_apply, Matrix.neg_apply, Matrix.submatrix_apply]
  ring

/-! ## The two classes and the finite maximum set -/

/-- The class representatives in `SU(2)^5`: `U⁺ = critPlusSU2 σ` for `true`, `U⁻ = 1` for
`false`. -/
noncomputable def cls (σ : Simplex4) (b : Bool) : Fin 5 → SU2 :=
  if b then critPlusSU2 σ else fun _ => 1

lemma coe_cls_true (σ : Simplex4) (a : Fin 5) :
    (cls σ true a : Matrix (Fin 2) (Fin 2) ℂ) = critPlus σ a := by simp [cls]

lemma coe_cls_false (σ : Simplex4) (a : Fin 5) :
    (cls σ false a : Matrix (Fin 2) (Fin 2) ℂ) = critMinus a := by simp [cls, critMinus]

lemma coe_cls_four (σ : Simplex4) (b : Bool) : (cls σ b 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  cases b
  · rw [coe_cls_false]; rfl
  · rw [coe_cls_true, critPlus_four]

lemma coe_signPt (c : Fin 5 → SU2) (s : Fin 4 → Bool) (i : Fin 4) :
    (signPt c s i : Matrix (Fin 2) (Fin 2) ℂ) =
      if s i then -(c i.castSucc : Matrix (Fin 2) (Fin 2) ℂ) else c i.castSucc := by
  by_cases h : s i = true <;> simp [signPt, h, SU2.negOne_coe]

open Classical in
/-- The finite maximum set: all sign patterns of the two class representatives. -/
noncomputable def maxSet (σ : Simplex4) : Finset (Fin 4 → SU2) :=
  (Finset.univ : Finset (Bool × (Fin 4 → Bool))).image fun x => signPt (cls σ x.1) x.2

lemma signPt_cls_injective (σ : Simplex4) :
    Function.Injective fun x : Bool × (Fin 4 → Bool) => signPt (cls σ x.1) x.2 := by
  rintro ⟨b, s⟩ ⟨b', s'⟩ h
  have hi : ∀ i : Fin 4, (if s i then -(cls σ b i.castSucc : Matrix (Fin 2) (Fin 2) ℂ)
      else cls σ b i.castSucc) = if s' i then -(cls σ b' i.castSucc : Matrix (Fin 2) (Fin 2) ℂ)
      else cls σ b' i.castSucc := fun i => by
    rw [← coe_signPt, ← coe_signPt]
    have h' : signPt (cls σ b) s = signPt (cls σ b') s' := h
    exact congr_arg (fun Y : Fin 4 → SU2 => (Y i : Matrix (Fin 2) (Fin 2) ℂ)) h'
  have h1 : ((1 : Matrix (Fin 2) (Fin 2) ℂ)) ≠ -1 := fun h1 => by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h1
    simp at this
    have h2 := congr_arg Complex.re this
    norm_num at h2
  have hdet : ∀ (c : Fin 5 → SU2) (i : Fin 5), (c i : Matrix (Fin 2) (Fin 2) ℂ) ≠
      -(c i : Matrix (Fin 2) (Fin 2) ℂ) := fun c i hh => by
    have h0 : (c i : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      have := congr_arg (fun M => M + (c i : Matrix (Fin 2) (Fin 2) ℂ)) hh
      simp only [neg_add_cancel] at this
      rw [← two_smul ℂ] at this
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    have hd : (c i : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := (c i).2.2
    rw [h0] at hd
    simp at hd
  by_cases hbb : b = b'
  · subst hbb
    refine Prod.ext rfl (funext fun i => ?_)
    have := hi i
    by_cases h1 : s i = true <;> by_cases h2 : s' i = true
    · simp [h1, h2]
    · exfalso; simp only [h1, h2, ite_true] at this
      exact hdet (cls σ b) i.castSucc (neg_eq_iff_eq_neg.mp this)
    · exfalso; simp only [h1, h2, ite_true] at this
      exact hdet (cls σ b) i.castSucc this
    · simp [h1, h2]
  · exfalso
    have := hi 0
    have hne := critPlus_ne σ (0 : Fin 4).castSucc (by decide)
    have hP : critPlus σ (0 : Fin 4).castSucc = 1 ∨ critPlus σ (0 : Fin 4).castSucc = -1 := by
      cases b <;> cases b' <;> first
        | exact absurd rfl hbb
        | (simp only [coe_cls_false, coe_cls_true, critMinus] at this
           by_cases h1 : s 0 = true <;> by_cases h2 : s' 0 = true <;> simp [h1, h2] at this <;>
           first
             | exact Or.inl this
             | exact Or.inl this.symm
             | exact Or.inr this
             | exact Or.inr this.symm
             | exact Or.inr (neg_eq_iff_eq_neg.mp this)
             | exact Or.inr (neg_eq_iff_eq_neg.mp this.symm))
    rcases hP with hP | hP
    · exact hne.1 hP
    · exact hne.2 hP

/-- **The maximum set is the set of sign points**: `|F(Y)| = 1` exactly on `maxSet σ`. -/
lemma mem_maxSet_iff (σ : Simplex4) (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) (Y : Fin 4 → SU2) :
    Y ∈ maxSet σ ↔ ‖gaugeF n (reggeState σ) Y‖ = 1 := by
  classical
  have h4 : ((Fin.snoc Y (1 : SU2) : Fin 5 → SU2) 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    show ((Fin.snoc Y (1 : SU2) : Fin 5 → SU2) (Fin.last 4) : Matrix (Fin 2) (Fin 2) ℂ) = 1
    rw [Fin.snoc_last]; rfl
  have key := norm_eq_one_iff_signLift σ n hn (Fin.snoc Y 1) h4
  unfold gaugeF cohF
  rw [key]
  simp only [maxSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨b, s⟩, rfl⟩
    refine ⟨Fin.snoc s false, Fin.snoc_last _ _, ?_⟩
    have h := snoc_signPt_coe (cls σ b) (coe_cls_four σ b) s
    cases b
    · left
      intro a
      have := congr_fun h a
      rw [this]
      congr 1
    · right
      intro a
      have := congr_fun h a
      rw [this]
      congr 1
  · rintro ⟨s5, h4', h | h⟩
    · refine ⟨(false, fun i => s5 i.castSucc), ?_⟩
      funext i
      refine Subtype.ext ?_
      have hi := h i.castSucc
      simp only [Fin.snoc_castSucc] at hi
      show (signPt (cls σ false) _ i : Matrix (Fin 2) (Fin 2) ℂ) = _
      rw [coe_signPt, hi]
      simp only [signLift, coe_cls_false]
    · refine ⟨(true, fun i => s5 i.castSucc), ?_⟩
      funext i
      refine Subtype.ext ?_
      have hi := h i.castSucc
      simp only [Fin.snoc_castSucc] at hi
      show (signPt (cls σ true) _ i : Matrix (Fin 2) (Fin 2) ℂ) = _
      rw [coe_signPt, hi]
      simp only [signLift, coe_cls_true]

/-- **Each class is a critical point**: the value has modulus one and the derivatives in the
exponential chart vanish. -/
lemma cls_critical (σ : Simplex4) (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) (b : Bool) :
    ‖cohAmp n (reggeState σ) (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ∀ l : Fin 12, coordDeriv (fun θ => cohAmp n (reggeState σ)
        (chart (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0 := by
  refine (reggeState_critical_iff σ n hn (cls σ b)).mpr ?_
  cases b
  · left
    intro a
    left
    simp [coe_cls_false, coe_cls_four, critMinus]
  · right
    intro a
    left
    simp only [coe_cls_true, critPlus_four, one_mul]

/-- The amplitude in the gnomonic chart around a sign point has no first derivative. -/
lemma fderiv_signPt (σ : Simplex4) (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (b : Bool) (s : Fin 4 → Bool) :
    fderiv ℝ (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) 0 = 0 := by
  have hfun : (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) =
      fun q => cohAmp n (reggeState σ) (qchart (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ)) q) :=
    funext (gaugeF_chartMap_signPt n _ hev _ (coe_cls_four σ b) s)
  rw [hfun]
  exact fderiv_eq_zero_of_coordDeriv
    (coordDeriv_qchart_eq_zero n _ _ (cls_critical σ n hn b).2)

lemma contDiff_signPt (σ : Simplex4) (n : Fin 10 → ℕ)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (b : Bool) (s : Fin 4 → Bool) :
    ContDiff ℝ ∞ (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) := by
  have hfun : (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) =
      fun q => cohAmp n (reggeState σ) (qchart (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ)) q) :=
    funext (gaugeF_chartMap_signPt n _ hev _ (coe_cls_four σ b) s)
  rw [hfun]
  exact (contDiff_cohAmp' n _).comp (contDiff_qchart _)

lemma det_signPt (σ : Simplex4) (n : Fin 10 → ℕ)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (b : Bool) (s : Fin 4 → Bool)
    (hnd : (-hessAmp n (reggeState σ) (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0) :
    (-((gaugeF n (reggeState σ) (signPt (cls σ b) s))⁻¹ •
        hessMat (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) 0)).det ≠ 0 := by
  rw [neg_hess_signPt n _ hev _ (coe_cls_four σ b) s, Matrix.det_smul,
    Matrix.det_submatrix_equiv_self]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hnd

lemma sq4 : (((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ 12 = ((1 / 4096 : ℝ) : ℂ) := by
  have h : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = (((4 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]
    push_cast; rfl
  rw [h, ← Complex.ofReal_pow]
  congr 1
  have h2 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [h2, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma haarDensity4_zero : haarDensity4 (reshape.symm 0) = (1 / (2 * Real.pi ^ 2)) ^ 4 := by
  have : (reshape.symm (0 : Fin 12 → ℝ) : Fin 4 → Fin 3 → ℝ) = 0 := by
    funext a k; rfl
  rw [this]
  unfold haarDensity4
  simp [haarDensity_zero]

/-- **The term of a sign point** in the stationary phase sum. -/
lemma term_signPt (σ : Simplex4) (n : Fin 10 → ℕ)
    (hev : ∀ a, Even (∑ k, k5Spins n a k)) (b : Bool) (s : Fin 4 → Bool) (lam : ℕ) :
    gaugeF n (reggeState σ) (signPt (cls σ b) s) ^ lam *
        ((((2 * Real.pi / lam) ^ (((12 : ℕ) : ℝ) / 2) : ℝ) *
          invSqrtDet (-((gaugeF n (reggeState σ) (signPt (cls σ b) s))⁻¹ •
            hessMat (fun q => gaugeF n (reggeState σ) (chartMap (signPt (cls σ b) s) q)) 0)) *
          (haarDensity4 (reshape.symm 0) : ℂ))) =
      cohAmp n (reggeState σ) (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ)) ^ lam *
        ((((2 * Real.pi / lam) ^ 6 * (1 / 4096) * (1 / (2 * Real.pi ^ 2)) ^ 4 : ℝ) : ℂ) *
          invSqrtDet (-hessAmp n (reggeState σ) (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ)))) := by
  rw [neg_hess_signPt n _ hev _ (coe_cls_four σ b) s, gaugeF_signPt n _ hev _ (coe_cls_four σ b) s,
    haarDensity4_zero]
  have h4 : ((4 : ℂ)) = ((4 : ℝ) : ℂ) := by norm_num
  rw [h4, invSqrtDet_smul_pos _ (by norm_num : (0 : ℝ) < 4), invSqrtDet_submatrix, sq4]
  have h6 : ((12 : ℕ) : ℝ) / 2 = ((6 : ℕ) : ℝ) := by norm_num
  rw [h6, Real.rpow_natCast]
  push_cast
  ring

lemma cohAmp_critPlus_cls (σ : Simplex4) (n : Fin 10 → ℕ) :
    cohAmp n (reggeState σ) (fun a => (cls σ true a : Matrix (Fin 2) (Fin 2) ℂ)) =
      cexp (I * (reggeAction σ n : ℂ)) := by
  have : (fun a => (cls σ true a : Matrix (Fin 2) (Fin 2) ℂ)) = critPlus σ :=
    funext (coe_cls_true σ)
  rw [this, cohAmp_critPlus]

lemma cohAmp_critMinus_cls (σ : Simplex4) (n : Fin 10 → ℕ) :
    cohAmp n (reggeState σ) (fun a => (cls σ false a : Matrix (Fin 2) (Fin 2) ℂ)) =
      cexp (-(I * (reggeAction σ n : ℂ))) := by
  have : (fun a => (cls σ false a : Matrix (Fin 2) (Fin 2) ℂ)) = critMinus :=
    funext (coe_cls_false σ)
  rw [this, cohAmp_critMinus]

lemma const_identity (u : ℝ) :
    16 * (u * (1 / 4096) * (1 / (2 * Real.pi ^ 2)) ^ 4) = u * 2 ^ 4 / (4 * Real.pi) ^ 8 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The asymptotic formula for the coherent 15j integral** (BFH, eq. (16), with the error term
`O(λ^{-7})`): the gauge-fixed integral localises at the `32` sign points of the two critical
classes (`localise_pieces`), each contributes by stationary phase (`asymptotics_finite_max`), the
sixteen sign lifts of a class contribute equally (`cohAmp_signLift`), and the Hessian in the
gnomonic chart gives the factor `2^{-12}`. -/
theorem coh15jAsymptoticFormula : Coh15jAsymptoticFormula := by
  intro σ n hn hev hp hm
  have hg := isSU2Data_reggeState σ
  have e1 : (fun a => (cls σ true a : Matrix (Fin 2) (Fin 2) ℂ)) = critPlus σ :=
    funext (coe_cls_true σ)
  have e2 : (fun a => (cls σ false a : Matrix (Fin 2) (Fin 2) ℂ)) = critMinus :=
    funext (coe_cls_false σ)
  have hndb : ∀ b : Bool, (-hessAmp n (reggeState σ)
      (fun a => (cls σ b a : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    intro b
    cases b
    · rw [e2]; exact hm
    · rw [e1]; exact hp
  have hmem : ∀ p ∈ maxSet σ, ∃ b s, p = signPt (cls σ b) s := by
    intro p hpm
    classical
    obtain ⟨⟨b, s⟩, -, rfl⟩ := Finset.mem_image.mp hpm
    exact ⟨b, s, rfl⟩
  have hmain := asymptotics_finite_max (gaugeF n (reggeState σ)) (continuous_cohF4 n _)
    (fun Y => norm_cohAmp_le n hg (Fin.snoc Y 1)) (maxSet σ)
    (fun Y hY => (mem_maxSet_iff σ n hn Y).mpr hY)
    (fun p hpm => (mem_maxSet_iff σ n hn p).mp hpm)
    (fun p hpm => by
      obtain ⟨b, s, rfl⟩ := hmem p hpm
      exact contDiff_signPt σ n hev b s)
    (fun p hpm => by
      obtain ⟨b, s, rfl⟩ := hmem p hpm
      exact fderiv_signPt σ n hn hev b s)
    (fun p hpm => by
      obtain ⟨b, s, rfl⟩ := hmem p hpm
      exact det_signPt σ n hev b s (hndb b))
  refine hmain.congr_left fun lam => ?_
  have hcoh : coh15j (lam • n) (reggeState σ) =
      ∫ Y : Fin 4 → SU2, gaugeF n (reggeState σ) Y ^ lam ∂(haarN (N := 4)) := by
    rw [coh15j_eq_gaugeFixed]
    congr 1
    funext Y
    exact cohF_smul n _ lam _
  have hsum : ∑ p ∈ maxSet σ, gaugeF n (reggeState σ) p ^ lam *
      ((((2 * Real.pi / lam) ^ (((12 : ℕ) : ℝ) / 2) : ℝ) *
        invSqrtDet (-((gaugeF n (reggeState σ) p)⁻¹ •
          hessMat (fun q => gaugeF n (reggeState σ) (chartMap p q)) 0)) *
        (haarDensity4 (reshape.symm 0) : ℂ))) =
      (((2 * Real.pi / lam) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 : ℝ) : ℂ) *
        (cexp (I * lam * reggeAction σ n) * ampPlus n σ +
          cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ) := by
    classical
    unfold maxSet
    rw [Finset.sum_image (fun x _ y _ h => signPt_cls_injective σ h), Fintype.sum_prod_type]
    simp_rw [term_signPt σ n hev _ _ lam]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Fintype.sum_bool, cohAmp_critPlus_cls σ n, cohAmp_critMinus_cls σ n]
    have hc := const_identity ((2 * Real.pi / lam) ^ 6)
    have hcC : (((16 : ℝ) * ((2 * Real.pi / lam) ^ 6 * (1 / 4096) * (1 / (2 * Real.pi ^ 2)) ^ 4) : ℝ) : ℂ) =
        (((2 * Real.pi / lam) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 : ℝ) : ℂ) := by rw [hc]
    rw [← hcC]
    have ep : cexp (I * (reggeAction σ n : ℂ)) ^ lam = cexp (I * lam * reggeAction σ n) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    have em : cexp (-(I * (reggeAction σ n : ℂ))) ^ lam = cexp (-(I * lam * reggeAction σ n)) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [ep, em]
    unfold ampPlus ampMinus
    rw [← e1, ← e2]
    push_cast
    ring
  show _ = _
  rw [hcoh, hsum]

end Lightlike.Asymptotics.EPRL
