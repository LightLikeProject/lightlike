import Lightlike.FieldTheory.Gaussian.Wick

/-!
# Wick's theorem for a positive semidefinite covariance

`moment_eq_pairSum_of_posSemidef` is the Isserlis formula of Tubaro–Zanella, *An introduction to Malliavin
calculus*, arXiv:2502.07941v1, Theorem 2.19, p. 9 (read 19 November 2026), for the coordinates of `N(0, S)` with
`S` positive semidefinite (all centred jointly Gaussian families of the form `x_{l_k}`); it removes the positive
definiteness of `moment_eq_pairSum`.

Route: `multivariateGaussian 0 S` is the image of the standard Gaussian under `R = √S` (Mathlib's definition), so
`E[∏_k x_{l_k}] = ∫ ∏_k (R y)_{l_k} dγ(y) = ∑_{a : Fin n → ι} ∏_k R_{l_k a_k} · E_γ[∏_k y_{a_k}]`; the identity
covariance is positive definite, so `E_γ[∏ y_{a_k}] = ∑_c ∏_{(p,q) ∈ c} δ_{a_p a_q}` (`moment_eq_pairSum`), and for
each full contraction `c` the sum over `a` factors along the pairs:
`∑_a ∏_{(p,q)} δ_{a_p a_q} ∏_k R_{l_k a_k} = ∏_{(p,q)} ∑_b R_{l_p b} R_{l_q b} = ∏_{(p,q)} (R Rᵀ)_{l_p l_q}`.
-/

namespace Lightlike.FieldTheory

open WickContraction

/-- For a full contraction every position is contracted. -/
lemma isSome_getDual_of_isFull {n : ℕ} {c : WickContraction n} (hc : c.IsFull) (x : Fin n) :
    (c.getDual? x).isSome := by
  have : x ∉ c.uncontracted := by rw [hc]; exact Finset.notMem_empty x
  unfold uncontracted at this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact Option.ne_none_iff_isSome.1 this

/-- **A product over the positions is a product over the pairs** of a full contraction. -/
lemma prod_eq_prod_pairs {M : Type*} [CommMonoid M] {n : ℕ} {c : WickContraction n} (hc : c.IsFull)
    (f : Fin n → M) :
    ∏ k, f k = ∏ a : c.1, f (c.fstFieldOfContract a) * f (c.sndFieldOfContract a) := by
  have h1 : ∏ k, f k = ∏ x : {x : Fin n // (c.getDual? x).isSome}, f x :=
    (Fintype.prod_equiv (Equiv.subtypeUnivEquiv (isSome_getDual_of_isFull hc)).symm _ _ fun _ => rfl)
  rw [h1, ← c.sigmaContractedEquiv.prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact prod_finset_eq_mul_fst_snd c a (fun x => f x)

/-- For a full contraction the positions are the pairs times `Fin 2` (first and second position of a pair). -/
noncomputable def pairsEquiv {n : ℕ} {c : WickContraction n} (hc : c.IsFull) : Fin n ≃ c.1 × Fin 2 :=
  (Equiv.subtypeUnivEquiv (isSome_getDual_of_isFull hc)).symm.trans
    (c.sigmaContractedEquiv.symm.trans
      ((Equiv.sigmaCongrRight fun a => c.contractEquivFinTwo a).trans (Equiv.sigmaEquivProd _ _)))

lemma pairsEquiv_symm_zero {n : ℕ} {c : WickContraction n} (hc : c.IsFull) (α : c.1) :
    (pairsEquiv hc).symm (α, 0) = c.fstFieldOfContract α := rfl

lemma pairsEquiv_symm_one {n : ℕ} {c : WickContraction n} (hc : c.IsFull) (α : c.1) :
    (pairsEquiv hc).symm (α, 1) = c.sndFieldOfContract α := rfl

/-- Index maps on the positions are pairs of indices on the contracted pairs. -/
noncomputable def indexEquiv {ι : Type*} {n : ℕ} {c : WickContraction n} (hc : c.IsFull) :
    (Fin n → ι) ≃ (c.1 → ι × ι) :=
  ((pairsEquiv hc).arrowCongr (Equiv.refl ι)).trans
    ((Equiv.curry c.1 (Fin 2) ι).trans (Equiv.piCongrRight fun _ => piFinTwoEquiv fun _ => ι))

lemma indexEquiv_apply {ι : Type*} {n : ℕ} {c : WickContraction n} (hc : c.IsFull) (a : Fin n → ι) (α : c.1) :
    indexEquiv hc a α = (a (c.fstFieldOfContract α), a (c.sndFieldOfContract α)) := rfl

/-- **The sum over index maps factors along the pairs.** -/
lemma sum_prod_delta {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {c : WickContraction n} (hc : c.IsFull)
    (g : Fin n → ι → ℝ) :
    ∑ a : Fin n → ι, (∏ α : c.1, if a (c.fstFieldOfContract α) = a (c.sndFieldOfContract α) then (1 : ℝ) else 0) *
        ∏ k, g k (a k) =
      ∏ α : c.1, ∑ b : ι, g (c.fstFieldOfContract α) b * g (c.sndFieldOfContract α) b := by
  have hsummand : ∀ a : Fin n → ι,
      (∏ α : c.1, if a (c.fstFieldOfContract α) = a (c.sndFieldOfContract α) then (1 : ℝ) else 0) *
        ∏ k, g k (a k) =
      ∏ α : c.1, (fun (u : ι × ι) => if u.1 = u.2 then g (c.fstFieldOfContract α) u.1 *
        g (c.sndFieldOfContract α) u.2 else 0) (indexEquiv hc a α) := by
    intro a
    rw [prod_eq_prod_pairs hc (fun k => g k (a k)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [indexEquiv_apply]
    by_cases hα : a (c.fstFieldOfContract α) = a (c.sndFieldOfContract α)
    · simp [hα]
    · simp [hα]
  simp_rw [hsummand]
  rw [← (indexEquiv hc).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  refine (Fintype.prod_sum (fun (α : c.1) (u : ι × ι) => if u.1 = u.2 then g (c.fstFieldOfContract α) u.1 *
    g (c.sndFieldOfContract α) u.2 else 0)).symm.trans ?_
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [Finset.sum_ite_eq Finset.univ b (fun u => g (c.fstFieldOfContract α) b * g (c.sndFieldOfContract α) u)]
  simp

end Lightlike.FieldTheory

namespace Lightlike.FieldTheory

open MeasureTheory Matrix WithLp WickContraction ProbabilityTheory
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian measure with covariance `1` is the standard Gaussian measure. -/
lemma multivariateGaussian_zero_one :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  have h : (fun x : EuclideanSpace ℝ ι =>
      (0 : EuclideanSpace ℝ ι) + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (1 : Matrix ι ι ℝ)) x) = id := by
    funext x; simp [CFC.sqrt_one]
  rw [multivariateGaussian, h, Measure.map_id]

/-- **The moments through the square root**: with `R = √S`,
`E_S[∏_k x_{l_k}] = ∑_{a : Fin n → ι} ∏_k R_{l_k a_k} · E_1[∏_k y_{a_k}]`. -/
lemma moment_eq_sum_sqrt {S : Matrix ι ι ℝ} (l : List ι) :
    moment S l = ∑ a : Fin l.length → ι,
      (∏ k, CFC.sqrt S (l.get k) (a k)) * moment 1 (List.ofFn a) := by
  set R : Matrix ι ι ℝ := CFC.sqrt S with hR
  have hφ : Measurable fun x : EuclideanSpace ℝ ι => (0 : EuclideanSpace ℝ ι) + toEuclideanCLM (𝕜 := ℝ) R x := by
    fun_prop
  have h1 : ∀ x : EuclideanSpace ℝ ι, mono l ((0 : EuclideanSpace ℝ ι) + toEuclideanCLM (𝕜 := ℝ) R x) =
      ∑ a : Fin l.length → ι, (∏ k, R (l.get k) (a k)) * mono (List.ofFn a) x := by
    intro x
    rw [zero_add, mono_eq_prod]
    have e : ∀ m : Fin l.length, (toEuclideanCLM (𝕜 := ℝ) R x) (l.get m) = ∑ b, R (l.get m) b * x b := by
      intro m
      show (ofLp (toEuclideanCLM (𝕜 := ℝ) R x)) (l.get m) = _
      rw [ofLp_toEuclideanCLM]
      rfl
    simp_rw [e]
    rw [Finset.prod_univ_sum]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [mono_eq_prod, Finset.prod_mul_distrib]
    congr 1
    refine Fintype.prod_equiv (finCongr (List.length_ofFn).symm) _ _ fun m => ?_
    first
      | (rw [List.get_ofFn]; rfl)
      | (simp only [List.get_eq_getElem, List.getElem_ofFn]; done)
      | (simp only [List.get_eq_getElem, List.getElem_ofFn]; rfl)
  have hmono : Continuous (mono l) := by
    rw [show mono l = fun x => ∏ m : Fin l.length, x (l.get m) from funext (mono_eq_prod l)]
    fun_prop
  unfold moment
  rw [multivariateGaussian, integral_map hφ.aemeasurable hmono.aestronglyMeasurable]
  have hint : ∀ a : Fin l.length → ι, Integrable (fun x => (∏ k, R (l.get k) (a k)) * mono (List.ofFn a) x)
      (stdGaussian (EuclideanSpace ℝ ι)) := fun a => by
    rw [← multivariateGaussian_zero_one]; exact (integrable_mono 1 (List.ofFn a)).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_finsetSum _ fun a _ => hint a]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, multivariateGaussian_zero_one]

/-- **Wick's theorem for a positive semidefinite covariance** (Tubaro–Zanella, arXiv:2502.07941, Theorem 2.19,
p. 9): `E[∏_k x_{l_k}] = ∑_c ∏_{(p,q) ∈ c} S_{l_p l_q}` over the full Wick contractions `c`. -/
theorem moment_eq_pairSum_of_posSemidef {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (l : List ι) :
    moment S l = pairSum S l.get := by
  set R : Matrix ι ι ℝ := CFC.sqrt S with hR
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hRsymm : ∀ i j, R i j = R j i := by
    intro i j
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    have := congrFun (congrFun h.star_eq i) j
    simpa [Matrix.star_apply] using this.symm
  rw [moment_eq_sum_sqrt]
  simp_rw [moment_ofFn_eq_pairSum Matrix.PosDef.one, pairSum, pairWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have key := sum_prod_delta c.2 (fun k b => R (l.get k) b)
  simp only [Matrix.one_apply] at *
  calc ∑ a : Fin l.length → ι, (∏ k, R (l.get k) (a k)) *
        ∏ α : c.1.1, (if a (c.1.fstFieldOfContract α) = a (c.1.sndFieldOfContract α) then (1 : ℝ) else 0)
      = ∑ a : Fin l.length → ι, (∏ α : c.1.1,
          (if a (c.1.fstFieldOfContract α) = a (c.1.sndFieldOfContract α) then (1 : ℝ) else 0)) *
          ∏ k, R (l.get k) (a k) := Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = ∏ α : c.1.1, ∑ b : ι, R (l.get (c.1.fstFieldOfContract α)) b * R (l.get (c.1.sndFieldOfContract α)) b := key
    _ = ∏ α : c.1.1, S (l.get (c.1.fstFieldOfContract α)) (l.get (c.1.sndFieldOfContract α)) := by
        refine Finset.prod_congr rfl fun α _ => ?_
        rw [← hRR, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun b _ => by rw [hRsymm (l.get (c.1.sndFieldOfContract α)) b]

end Lightlike.FieldTheory
