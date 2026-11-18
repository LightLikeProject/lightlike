import Lightlike.FieldTheory.Gaussian.Mono

/-!
# Moments of the Gaussian measure

The monomials are integrable for the centred Gaussian measure (all moments of a Gaussian measure are
finite), and `E [x_{i₁} ⋯ x_{iₖ}]` is the integral `moment S l` of the monomial `mono l`.
-/

open MeasureTheory ProbabilityTheory Matrix Real
open scoped ENNReal

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The moment `E [x_{l₀} x_{l₁} ⋯]` for the centred Gaussian measure with covariance `S`. -/
def moment (S : Matrix ι ι ℝ) (l : List ι) : ℝ := ∫ x, mono l x ∂(multivariateGaussian 0 S)

lemma memLp_coord (S : Matrix ι ι ℝ) (k : ι) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x : EuclideanSpace ℝ ι => x k) p (multivariateGaussian 0 S) := by
  have h := (IsGaussian.memLp_id (multivariateGaussian 0 S) p hp)
  have := h.continuousLinearMap_comp (EuclideanSpace.proj k : EuclideanSpace ℝ ι →L[ℝ] ℝ)
  simpa [Function.comp_def] using this

lemma mono_eq_prod (l : List ι) (x : EuclideanSpace ℝ ι) :
    mono l x = ∏ m : Fin l.length, x (l.get m) := by
  unfold mono
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_get <;> simp

/-- Every monomial is integrable for the centred Gaussian measure. -/
lemma integrable_mono (S : Matrix ι ι ℝ) (l : List ι) :
    Integrable (mono l) (multivariateGaussian 0 S) := by
  by_cases hn : l.length = 0
  · rw [List.length_eq_zero_iff] at hn
    subst hn
    exact integrable_const (1 : ℝ)
  · have hn' : (l.length : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
    have h := MemLp.fun_prod (μ := multivariateGaussian 0 S) (s := Finset.univ)
      (f := fun (m : Fin l.length) (x : EuclideanSpace ℝ ι) => x (l.get m))
      (p := fun _ => (l.length : ℝ≥0∞))
      (fun m _ => memLp_coord S _ (ENNReal.natCast_ne_top _))
    have hsum : (∑ _i : Fin l.length, ((l.length : ℝ≥0∞))⁻¹)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.mul_inv_cancel hn' (ENNReal.natCast_ne_top _), inv_one]
    rw [hsum, memLp_one_iff_integrable] at h
    have : mono l = fun x : EuclideanSpace ℝ ι => ∏ m : Fin l.length, x (l.get m) := by
      ext x; exact mono_eq_prod l x
    rw [this]; exact h

lemma integrable_dmono (S : Matrix ι ι ℝ) (j : ι) (l : List ι) :
    Integrable (dmono j l) (multivariateGaussian 0 S) := by
  unfold dmono
  refine integrable_finsetSum _ fun m _ => ?_
  by_cases h : l[m]? = some j
  · simpa [h] using integrable_mono S (l.eraseIdx m)
  · simp [h]

lemma mulVec_mul_mono (A : Matrix ι ι ℝ) (j : ι) (l : List ι) (x : EuclideanSpace ℝ ι) :
    (A *ᵥ x.ofLp) j * mono l x = ∑ k, A j k * mono (k :: l) x := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mono_cons]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma integrable_mulVec_mul_mono (S A : Matrix ι ι ℝ) (j : ι) (l : List ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => (A *ᵥ x.ofLp) j * mono l x) (multivariateGaussian 0 S) := by
  simp_rw [mulVec_mul_mono]
  exact integrable_finsetSum _ fun k _ => (integrable_mono S (k :: l)).const_mul _

/-- **Gaussian integration by parts for the moments.** -/
theorem integral_dmono {S : Matrix ι ι ℝ} (hS : S.PosDef) (j : ι) (l : List ι) :
    ∫ x, dmono j l x ∂(multivariateGaussian 0 S) =
      ∫ x : EuclideanSpace ℝ ι, (S⁻¹ *ᵥ x.ofLp) j * mono l x ∂(multivariateGaussian 0 S) := by
  have hA : (S⁻¹).IsHermitian := hS.isHermitian.inv
  have h1 : Integrable (fun x : EuclideanSpace ℝ ι => weight S⁻¹ x * mono l x) :=
    integrable_weight_mul hS (integrable_mono S l)
  have h2 : Integrable (fun x : EuclideanSpace ℝ ι => weight S⁻¹ x * dmono j l x) :=
    integrable_weight_mul hS (integrable_dmono S j l)
  have h3 : Integrable (fun x : EuclideanSpace ℝ ι => (-((S⁻¹ *ᵥ x.ofLp) j) * weight S⁻¹ x) * mono l x) := by
    have := (integrable_weight_mul hS (integrable_mulVec_mul_mono S S⁻¹ j l)).neg
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]; ring
  have key := integral_weight_mul_lineDeriv hA j (hasLineDerivAt_mono j l) h1 h2 h3
  rw [integral_multivariateGaussian S hS, integral_multivariateGaussian S hS]
  have e1 : ∀ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * (x.ofLp ⬝ᵥ S⁻¹ *ᵥ x.ofLp)) * dmono j l x =
      weight S⁻¹ x * dmono j l x := fun x => rfl
  have e2 : ∀ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * (x.ofLp ⬝ᵥ S⁻¹ *ᵥ x.ofLp)) *
      ((S⁻¹ *ᵥ x.ofLp) j * mono l x) = (S⁻¹ *ᵥ x.ofLp) j * (weight S⁻¹ x * mono l x) := by
    intro x; unfold weight; ring
  simp_rw [e1, e2]
  rw [key]

lemma sum_mul_mulVec (S : Matrix ι ι ℝ) (hS : S.PosDef) (i : ι) (x : EuclideanSpace ℝ ι) :
    ∑ j, S i j * (S⁻¹ *ᵥ x.ofLp) j = x i := by
  have hu : IsUnit S.det := isUnit_iff_ne_zero.2 hS.det_pos.ne'
  have := congrFun (show S *ᵥ (S⁻¹ *ᵥ x.ofLp) = x.ofLp by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]) i
  simpa [Matrix.mulVec, dotProduct] using this

/-- **Isserlis' recursion**: `E [x_i x_{l₀} ⋯ x_{lₙ}] = ∑ₘ S_{i, lₘ} E [∏_{k ≠ m} x_{lₖ}]`. -/
theorem moment_cons {S : Matrix ι ι ℝ} (hS : S.PosDef) (i : ι) (l : List ι) :
    moment S (i :: l) = ∑ m : Fin l.length, S i (l.get m) * moment S (l.eraseIdx m) := by
  unfold moment
  have h1 : ∀ x : EuclideanSpace ℝ ι, mono (i :: l) x =
      ∑ j, S i j * ((S⁻¹ *ᵥ x.ofLp) j * mono l x) := by
    intro x
    calc mono (i :: l) x = x i * mono l x := mono_cons i l x
      _ = (∑ j, S i j * (S⁻¹ *ᵥ x.ofLp) j) * mono l x := by rw [sum_mul_mulVec S hS i x]
      _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun j _ => (integrable_mulVec_mul_mono S S⁻¹ j l).const_mul _)]
  have h2 : ∀ j, ∫ x : EuclideanSpace ℝ ι, S i j * ((S⁻¹ *ᵥ x.ofLp) j * mono l x)
      ∂(multivariateGaussian 0 S) = S i j * ∫ x, dmono j l x ∂(multivariateGaussian 0 S) := by
    intro j
    rw [integral_const_mul, integral_dmono hS]
  simp_rw [h2]
  unfold dmono
  have h3 : ∀ j, ∫ x, ∑ m ∈ Finset.range l.length, (if l[m]? = some j then mono (l.eraseIdx m) x else 0)
      ∂(multivariateGaussian 0 S) = ∑ m ∈ Finset.range l.length,
        (if l[m]? = some j then ∫ x, mono (l.eraseIdx m) x ∂(multivariateGaussian 0 S) else 0) := by
    intro j
    rw [integral_finsetSum _ (fun m _ => ?_)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : l[m]? = some j <;> simp [h]
    · by_cases h : l[m]? = some j
      · simpa [h] using integrable_mono S (l.eraseIdx m)
      · simp [h]
  simp_rw [h3, Finset.mul_sum]
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single (l.get m)]
  · simp
  · intro j _ hj
    have : l[(m : ℕ)]? ≠ some j := by
      rw [List.getElem?_eq_getElem m.2]; intro h; exact hj (Option.some.inj h).symm
    simp only [this, ↓reduceIte, mul_zero]
  · simp

lemma moment_nil (S : Matrix ι ι ℝ) : moment S [] = 1 := by
  unfold moment
  simp [mono]

/-- Odd moments vanish. -/
theorem moment_odd {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∀ (n : ℕ) (l : List ι), l.length = n → Odd n → moment S l = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl hodd
    rcases l with _ | ⟨i, l'⟩
    · simp at hl; subst hl; exact absurd hodd (by decide)
    · rw [moment_cons hS]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hlen : (l'.eraseIdx m).length = n - 2 := by
        rw [List.length_eraseIdx_of_lt m.2]; simp at hl; omega
      have hn : 2 ≤ n := by
        have := m.2; simp at hl; omega
      rw [ih (n - 2) (by omega) _ hlen (by obtain ⟨k, hk⟩ := hodd; exact ⟨k - 1, by omega⟩), mul_zero]

/-- The two-point function is the covariance. -/
theorem moment_two {S : Matrix ι ι ℝ} (hS : S.PosDef) (i j : ι) : moment S [i, j] = S i j := by
  rw [moment_cons hS]
  simp [moment_nil]

/-- The four-point function (Wick's theorem, three pairings). -/
theorem moment_four {S : Matrix ι ι ℝ} (hS : S.PosDef) (i j k l : ι) :
    moment S [i, j, k, l] = S i j * S k l + S i k * S j l + S i l * S j k := by
  rw [moment_cons hS]
  simp [Fin.sum_univ_three, moment_two hS]

end Lightlike.FieldTheory
