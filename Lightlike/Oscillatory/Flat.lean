module

public import Lightlike.Oscillatory.Vanishing

/-!
# Flat functions and division by `|x|²`

A smooth function is *flat* at a point if all its derivatives vanish there. Stationary phase at a
critical point on the boundary of the support of the amplitude needs one fact about such
functions: a flat function `v` on `ℝⁿ` divided by `|x|²` is again smooth and flat. Writing
`v = ∑ⱼ xⱼ (v xⱼ / |x|²)` repeatedly then shows that `v` vanishes to every order in the sense of
`Vanish`, with the quotients still zero wherever `v` is (`vanish_of_flat`). The Hadamard
quotients `∫₀¹ ∂ⱼv(tx) dt` would not do here, as they need not vanish off the support of `v`.

* `exists_bound_of_flat`: a flat function and all its derivatives are `O(|x|^N)` near the origin,
  for every `N` (mean value inequality, by induction on `N`).
* `exists_bound_of_homogeneous`: a function smooth off the origin and homogeneous of degree `-1`
  has `m`-th derivative `O(|x|^{-1-m})` (scaling to the unit sphere).
* `contDiff_of_bound`: a function smooth off the origin, zero at the origin, whose derivatives of
  every order are `O(|x|²)` near the origin, is smooth and flat there.
* `flat_mul_divCoord`: for `v` smooth and flat at `0`, `v xⱼ / |x|²` is smooth and flat at `0`
  (Leibniz rule and the three bounds above).
* `vanish_of_flat`: a smooth function, flat at `0` and zero off `K`, is in `Vanish K p` for
  every `p`.
* `iteratedFDeriv_eq_zero_of_mem_closure_compl`: a smooth function is flat at every point of the
  closure of the complement of its support, so in particular at a boundary point of the support.
-/

@[expose] public section

namespace Lightlike.Oscillatory

open MeasureTheory Complex Finset Set Filter Asymptotics
open scoped Real ContDiff Topology

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A continuous function vanishes on the closure of the complement of its support. -/
theorem apply_eq_zero_of_mem_closure_compl {f : E → F} (hf : Continuous f) {x : E}
    (hx : x ∈ closure (tsupport f)ᶜ) : f x = 0 :=
  closure_minimal (fun _ hy => image_eq_zero_of_notMem_tsupport hy)
    (isClosed_eq hf continuous_const) hx

omit [FiniteDimensional ℝ E] in
/-- A smooth function is flat (all derivatives zero) at every point of the closure of the
complement of its support. -/
theorem iteratedFDeriv_eq_zero_of_mem_closure_compl {f : E → F} (hf : ContDiff ℝ ∞ f) {x : E}
    (hx : x ∈ closure (tsupport f)ᶜ) (k : ℕ) : iteratedFDeriv ℝ k f x = 0 := by
  have hc : IsClosed {y | iteratedFDeriv ℝ k f y = 0} :=
    isClosed_eq (hf.continuous_iteratedFDeriv (mod_cast le_top)) continuous_const
  refine closure_minimal (fun y hy => ?_) hc hx
  by_contra h
  exact hy (support_iteratedFDeriv_subset k (Function.mem_support.mpr h))

/-- **Flat functions are small to every order.** If `f` is smooth and all its derivatives vanish at
`0`, then for every `N` and `k`, `‖Dᵏf(x)‖ ≤ C ‖x‖^N` on the closed unit ball. -/
theorem exists_bound_of_flat {f : E → F} (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ k, iteratedFDeriv ℝ k f 0 = 0) (N : ℕ) :
    ∀ k, ∃ C, 0 ≤ C ∧ ∀ x : E, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖x‖ ^ N := by
  induction N with
  | zero =>
    intro k
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m := k) (mod_cast le_top)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    rw [pow_zero, mul_one]
    exact (hC x (by rwa [Metric.mem_closedBall, dist_zero_right])).trans (le_max_left _ _)
  | succ N ih =>
    intro k
    obtain ⟨C, hC0, hC⟩ := ih (k + 1)
    refine ⟨C, hC0, fun x hx => ?_⟩
    have hd : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y := fun y _ =>
      hf.differentiable_iteratedFDeriv (m := k) (mod_cast ENat.natCast_lt_top k) y
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        ‖fderiv ℝ (iteratedFDeriv ℝ k f) y‖ ≤ C * ‖x‖ ^ N := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [norm_fderiv_iteratedFDeriv]
      exact (hC y (hy.trans hx)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy N) hC0)
    have := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le hd hb
      (Metric.mem_closedBall_self (norm_nonneg x))
      (by rw [Metric.mem_closedBall, dist_zero_right])
    rw [h0 k, sub_zero, sub_zero] at this
    calc _ ≤ _ := this
      _ = C * ‖x‖ ^ (N + 1) := by ring

/-- **Derivatives of a homogeneous function of degree `-1`.** If `g` is smooth off the origin and
`g(t x) = t⁻¹ g(x)` for `t > 0`, then `‖x‖^{m+1} ‖Dᵐg(x)‖` is bounded on `x ≠ 0`. -/
theorem exists_bound_of_homogeneous {g : E → F} (hg : ContDiffOn ℝ ∞ g {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x : E, x ≠ 0 → g (t • x) = t⁻¹ • g x) (m : ℕ) :
    ∃ M, ∀ x : E, x ≠ 0 → ‖x‖ ^ (m + 1) * ‖iteratedFDeriv ℝ m g x‖ ≤ M := by
  have ho : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ m g) {0}ᶜ :=
    (hg.continuousOn_iteratedFDerivWithin (m := m) (mod_cast le_top) ho.uniqueDiffOn).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen m ho hy).symm
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
    (hcont.mono fun y hy h => by
      rw [mem_sphere_zero_iff_norm] at hy
      rw [Set.mem_singleton_iff.mp h, norm_zero] at hy
      exact zero_ne_one hy)
  refine ⟨M, fun x hx => ?_⟩
  set t := ‖x‖ with ht
  have htp : 0 < t := norm_pos_iff.mpr hx
  have ht0 : 0 ≤ t⁻¹ := inv_nonneg.mpr htp.le
  set L : E →L[ℝ] E := t⁻¹ • ContinuousLinearMap.id ℝ E with hL
  have hLx : ∀ z, L z = t⁻¹ • z := fun z => rfl
  have heq : g =ᶠ[𝓝 x] fun z => t⁻¹ • (g ∘ L) z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    simp only [Function.comp_apply, hLx]
    rw [hhom t⁻¹ (inv_pos.mpr htp) z hz, inv_inv, smul_smul, inv_mul_cancel₀ htp.ne', one_smul]
  have hy : L x ∈ ({0}ᶜ : Set E) := by
    rw [hLx]
    exact smul_ne_zero (inv_ne_zero htp.ne') hx
  have hpre : IsOpen (L ⁻¹' {0}ᶜ) := ho.preimage L.continuous
  have hcomp : iteratedFDeriv ℝ m (g ∘ L) x =
      (iteratedFDeriv ℝ m g (L x)).compContinuousLinearMap fun _ => L := by
    rw [← iteratedFDerivWithin_of_isOpen m hpre hy,
      L.iteratedFDerivWithin_comp_right hg ho.uniqueDiffOn hpre.uniqueDiffOn hy
        (mod_cast le_top),
      iteratedFDerivWithin_of_isOpen m ho hy]
  have hca : ContDiffAt ℝ m (g ∘ L) x :=
    ((hg.contDiffAt (ho.mem_nhds hy)).comp x L.contDiff.contDiffAt).of_le (mod_cast le_top)
  have hLn : ‖L‖ ≤ t⁻¹ := by
    calc ‖L‖ ≤ ‖t⁻¹‖ * ‖ContinuousLinearMap.id ℝ E‖ := by rw [hL]; exact norm_smul_le (t⁻¹) (ContinuousLinearMap.id ℝ E)
      _ ≤ t⁻¹ * 1 := by
        rw [Real.norm_of_nonneg ht0]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ht0
      _ = t⁻¹ := mul_one _
  have hyM : ‖iteratedFDeriv ℝ m g (L x)‖ ≤ M := hM _ (by
    rw [mem_sphere_zero_iff_norm, hLx, norm_smul, Real.norm_of_nonneg ht0, ← ht,
      inv_mul_cancel₀ htp.ne'])
  have hA := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ m g (L x)) fun _ => L
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hA
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hca, hcomp, norm_smul,
    Real.norm_of_nonneg ht0]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hyM
  calc t ^ (m + 1) * (t⁻¹ * ‖(iteratedFDeriv ℝ m g (L x)).compContinuousLinearMap fun _ => L‖)
      ≤ t ^ (m + 1) * (t⁻¹ * (M * t⁻¹ ^ m)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ht0) (by positivity)
        exact hA.trans (mul_le_mul hyM (pow_le_pow_left₀ (norm_nonneg _) hLn m)
          (by positivity) hM0)
    _ = M := by
        have h1 : t⁻¹ * (M * t⁻¹ ^ m) = M * (t ^ (m + 1))⁻¹ := by
          rw [pow_succ', mul_inv, inv_pow]; ring
        rw [h1, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ htp.ne'), mul_one]

omit [FiniteDimensional ℝ E] in
/-- **Smooth extension across the origin.** If `h` is smooth off the origin, `h 0 = 0`, and every
derivative satisfies `‖Dᵏh(x)‖ ≤ C ‖x‖²` for `0 < ‖x‖ ≤ 1`, then `h` is smooth and flat at
`0`. -/
theorem contDiff_of_bound {h : E → F} (hh : ContDiffOn ℝ ∞ h {0}ᶜ) (h0 : h 0 = 0)
    (hb : ∀ k, ∃ C, ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ k h x‖ ≤ C * ‖x‖ ^ 2) :
    ContDiff ℝ ∞ h ∧ ∀ k, iteratedFDeriv ℝ k h 0 = 0 := by
  have ho : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hder : ∀ k, iteratedFDeriv ℝ k h 0 = 0 → HasFDerivAt (iteratedFDeriv ℝ k h) (0 : E →L[ℝ] E [×k]→L[ℝ] F) (0 : E) := by
    intro k hk
    obtain ⟨C, hC⟩ := hb k
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, hk, sub_zero, zero_apply]
    refine IsBigO.trans_isLittleO (g := fun y : E => ‖y‖ ^ 2) ?_
      (isLittleO_norm_pow_id one_lt_two)
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [norm_pow, norm_norm]
    by_cases hy0 : y = 0
    · simp [hy0, hk]
    · exact hC y hy0 hy
  have hflat : ∀ k, iteratedFDeriv ℝ k h 0 = 0 := by
    intro k
    induction k with
    | zero => rw [← norm_eq_zero, norm_iteratedFDeriv_zero, h0, norm_zero]
    | succ k ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, (hder k ih).fderiv]
      exact LinearIsometryEquiv.map_zero _
  refine ⟨contDiff_of_differentiable_iteratedFDeriv fun k _ x => ?_, hflat⟩
  by_cases hx : x = 0
  · subst hx
    exact (hder k (hflat k)).differentiableAt
  · have hx' : x ∈ ({0}ᶜ : Set E) := hx
    exact (((hh.differentiableOn_iteratedFDerivWithin (m := k)
      (mod_cast ENat.natCast_lt_top k) ho.uniqueDiffOn) x hx').differentiableAt
        (ho.mem_nhds hx')).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (ho.mem_nhds hx') fun y hy =>
        (iteratedFDerivWithin_of_isOpen k ho hy).symm)

end General

variable {n : ℕ}

/-- The function `xⱼ / |x|²` on `ℝⁿ` (with value `0` at the origin), as a complex number. -/
noncomputable def divCoord (j : Fin n) (x : Fin n → ℝ) : ℂ := ((x j / ∑ i, x i ^ 2 : ℝ) : ℂ)

/-- `|x|² = ∑ᵢ xᵢ² > 0` for `x ≠ 0`. -/
theorem sumSq_pos {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  calc 0 < x i ^ 2 := by have : x i ≠ 0 := hi; positivity
    _ ≤ ∑ i, x i ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- `xⱼ / |x|²` is smooth off the origin. -/
theorem contDiffOn_divCoord (j : Fin n) : ContDiffOn ℝ ∞ (divCoord j) {0}ᶜ := by
  have h1 : ContDiff ℝ ∞ (fun x : Fin n → ℝ => x j) := contDiff_pi.mp contDiff_id j
  have h2 : ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑ i, x i ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_pi.mp contDiff_id i).pow 2
  exact ofRealCLM.contDiff.comp_contDiffOn
    (h1.contDiffOn.div h2.contDiffOn fun x hx => (sumSq_pos hx).ne')

/-- `xⱼ / |x|²` is homogeneous of degree `-1`. -/
theorem divCoord_smul (j : Fin n) {t : ℝ} (ht : t ≠ 0) (x : Fin n → ℝ) :
    divCoord j (t • x) = t⁻¹ • divCoord j x := by
  have : t * x j / ∑ i, (t * x i) ^ 2 = t⁻¹ * (x j / ∑ i, x i ^ 2) := by
    simp only [mul_pow, ← Finset.mul_sum]
    rw [mul_div_mul_comm, show t / t ^ 2 = t⁻¹ by field_simp]
  simp only [divCoord, Pi.smul_apply, smul_eq_mul, this, Complex.real_smul, Complex.ofReal_mul]

/-- **Division of a flat function by `|x|²`.** If `v` is smooth and flat at `0`, then
`v xⱼ / |x|²` is smooth and flat at `0`. -/
theorem flat_mul_divCoord {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (h0 : ∀ k, iteratedFDeriv ℝ k v 0 = 0) (j : Fin n) :
    ContDiff ℝ ∞ (fun x => v x * divCoord j x) ∧
      ∀ k, iteratedFDeriv ℝ k (fun x => v x * divCoord j x) 0 = 0 := by
  have ho : IsOpen ({0}ᶜ : Set (Fin n → ℝ)) := isOpen_compl_singleton
  have hg := contDiffOn_divCoord j
  refine contDiff_of_bound (hv.contDiffOn.mul hg) (by simp [divCoord]) fun k => ?_
  choose A hA0 hA using exists_bound_of_flat hv h0 (k + 3)
  choose M hM using exists_bound_of_homogeneous hg fun t ht x _ => divCoord_smul j ht.ne' x
  refine ⟨∑ i ∈ range (k + 1), (k.choose i : ℝ) * A i * M (k - i), fun x hx hx1 => ?_⟩
  have hx' : x ∈ ({0}ᶜ : Set (Fin n → ℝ)) := hx
  have hmul := norm_iteratedFDerivWithin_mul_le (N := ∞) hv.contDiffOn hg ho.uniqueDiffOn hx'
    (n := k) (mod_cast le_top)
  simp only [iteratedFDerivWithin_of_isOpen _ ho hx'] at hmul
  refine hmul.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 := hA i x hx1
  have h2 := hM (k - i) x hx
  have hsplit : ‖x‖ ^ (k + 3) = ‖x‖ ^ (i + 2) * ‖x‖ ^ (k - i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow : ‖x‖ ^ (i + 2) ≤ ‖x‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hx1 (by omega)
  have hcA : 0 ≤ (k.choose i : ℝ) * A i := mul_nonneg (Nat.cast_nonneg _) (hA0 i)
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i v x‖ *
        ‖iteratedFDeriv ℝ (k - i) (divCoord j) x‖
      ≤ (k.choose i : ℝ) * (A i * ‖x‖ ^ (k + 3)) *
        ‖iteratedFDeriv ℝ (k - i) (divCoord j) x‖ := by gcongr
    _ = (k.choose i : ℝ) * A i * ‖x‖ ^ (i + 2) *
        (‖x‖ ^ (k - i + 1) * ‖iteratedFDeriv ℝ (k - i) (divCoord j) x‖) := by
      rw [hsplit]; ring
    _ ≤ (k.choose i : ℝ) * A i * ‖x‖ ^ 2 * M (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hcA) h2 (by positivity)
        (mul_nonneg hcA (by positivity))
    _ = (k.choose i : ℝ) * A i * M (k - i) * ‖x‖ ^ 2 := by ring

/-- A smooth function that is flat at `0` and zero off `K` vanishes to every order `p`, as a
family constant in the parameter: `v = ∑ⱼ xⱼ (v xⱼ / |x|²)`, repeated. -/
theorem vanish_of_flat {K : Set (Fin n → ℝ)} : ∀ (p : ℕ) {v : (Fin n → ℝ) → ℂ},
    ContDiff ℝ ∞ v → (∀ k, iteratedFDeriv ℝ k v 0 = 0) → (∀ x ∉ K, v x = 0) →
    Vanish K p (fun _ x => v x)
  | 0, _, hv, _, hK => ⟨hv.comp contDiff_snd, fun _ x hx => hK x hx⟩
  | p + 1, v, hv, h0, hK => by
    have hv0 : v 0 = 0 := by
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := v), h0 0, norm_zero]
    refine ⟨fun j _ x => v x * divCoord j x, fun j => vanish_of_flat p
      (flat_mul_divCoord hv h0 j).1 (flat_mul_divCoord hv h0 j).2
      fun x hx => by simp [hK x hx], fun _ x => ?_⟩
    show v x = ∑ j, (x j : ℂ) * (v x * divCoord j x)
    by_cases hx : x = 0
    · simp [hx, hv0]
    · have hS := (sumSq_pos hx).ne'
      have hj : ∀ j, (x j : ℂ) * (v x * divCoord j x) =
          v x * ((x j ^ 2 / ∑ i, x i ^ 2 : ℝ) : ℂ) := fun j => by
        simp only [divCoord]
        push_cast
        ring
      simp only [hj, ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.sum_div, div_self hS,
        Complex.ofReal_one, mul_one]

end Lightlike.Oscillatory
