import Mathlib

/-!
# Derivatives of functions vanishing on the diagonal

For a smooth `Φ : E × E → G` with `Φ(w, w) = 0` for `w` in an open set `O`, the derivatives in `w` of
`w ↦ Φ(w + c, w)` are `O(‖c‖)`: for a compact `K ⊆ O` and `δ ≥ 0` there is `C` with
`‖D^ℓ_w Φ(w + c, w)‖ ≤ C ‖c‖` for `w ∈ K`, `‖c‖ ≤ δ` (`exists_norm_iteratedFDeriv_comp_diag_add_le`).

The derivative in `w` is the `ℓ`-th derivative of `Φ` at `(w + c, w)` composed with the diagonal map
(`iteratedFDeriv_comp_diag_add`); it vanishes at `c = 0` and the mean value inequality in `c` gives the bound, with
the `(ℓ + 1)`-th derivative of `Φ` bounded on a compact set. This is the substitute for the Taylor formula with
integral remainder in the bounds of the parametrix after the substitution `p = w − √t v`.
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The diagonal map `w ↦ (w, w)`. -/
def diagCLM : E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)

theorem diagCLM_apply (w : E) : (diagCLM : E →L[ℝ] E × E) w = (w, w) := rfl

theorem norm_diagCLM_le : ‖(diagCLM : E →L[ℝ] E × E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [diagCLM_apply, Prod.norm_def, max_self, one_mul]

/-- **The derivatives of `w ↦ Φ(w + c, w)`** are those of `Φ` at `(w + c, w)` along the diagonal. -/
theorem iteratedFDeriv_comp_diag_add {Φ : E × E → G} (hΦ : ContDiff ℝ ∞ Φ) (ℓ : ℕ) (c w : E) :
    iteratedFDeriv ℝ ℓ (fun w' => Φ (w' + c, w')) w =
      (iteratedFDeriv ℝ ℓ Φ (w + c, w)).compContinuousLinearMap fun _ => diagCLM := by
  have hfun : (fun w' => Φ (w' + c, w')) = (fun z => Φ (z + (c, 0))) ∘ (diagCLM : E →L[ℝ] E × E) := by
    funext w'; simp [diagCLM_apply]
  have hs : ContDiff ℝ ∞ (fun z : E × E => Φ (z + (c, 0))) := hΦ.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (f := fun z : E × E => Φ (z + (c, 0))) _ hs w
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right, diagCLM_apply]
  congr 2
  simp

/-- **Leibniz with uniform bounds**: if the derivatives of `f` and `g` of order `≤ ℓ` at `x` are bounded by `A` and `B`,
those of `f g` are bounded by `2^ℓ A B`. -/
theorem norm_iteratedFDeriv_mul_le_of_bounds {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : E)
    (ℓ : ℕ) {A B : ℝ} (hA : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m f x‖ ≤ A) (hB : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m h x‖ ≤ B) :
    ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun y => f y * h y) x‖ ≤ 2 ^ ℓ * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  intro m hm
  refine (norm_iteratedFDeriv_mul_le (N := ∞) hf hh x (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) h x‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        gcongr
        · exact hA i (hi'.trans hm)
        · exact hB (m - i) ((Nat.sub_le m i).trans hm)
    _ = 2 ^ m * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose m
    _ ≤ 2 ^ ℓ * A * B := by
        gcongr
        · norm_num

variable [FiniteDimensional ℝ E]

/-- **Vanishing on the diagonal gives a linear bound**: `‖D^ℓ_w Φ(w + c, w)‖ ≤ C ‖c‖` for `w ∈ K`, `‖c‖ ≤ δ`. -/
theorem exists_norm_iteratedFDeriv_comp_diag_add_le {Φ : E × E → G} (hΦ : ContDiff ℝ ∞ Φ) {K : Set E}
    (hK : IsCompact K) {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) (h0 : ∀ w ∈ O, Φ (w, w) = 0) (δ : ℝ)
    (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ c : E, ‖c‖ ≤ δ →
      ‖iteratedFDeriv ℝ ℓ (fun w' => Φ (w' + c, w')) w‖ ≤ C * ‖c‖ := by
  set K' := (fun z : E × E => (z.1 + z.2, z.1)) '' (K ×ˢ closedBall (0 : E) δ) with hK'def
  have hK' : IsCompact K' := (hK.prod (isCompact_closedBall 0 δ)).image (by fun_prop)
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := ℓ + 1) (by exact_mod_cast le_top)).continuousOn)
  refine ⟨|M|, abs_nonneg _, fun w hw c hc => ?_⟩
  set L := ContinuousMultilinearMap.compContinuousLinearMapL (F := G)
    (fun _ : Fin ℓ => (diagCLM : E →L[ℝ] E × E)) with hL
  have hLn : ‖L‖ ≤ 1 := (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le G _).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_diagCLM_le)
  set f : E → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => E) G :=
    fun c' => L (iteratedFDeriv ℝ ℓ Φ (w + c', w)) with hf
  have hfeq : ∀ c', iteratedFDeriv ℝ ℓ (fun w' => Φ (w' + c', w')) w = f c' := fun c' => by
    rw [iteratedFDeriv_comp_diag_add hΦ]; rfl
  have hf0 : f 0 = 0 := by
    rw [← hfeq]
    have hev : (fun w' => Φ (w' + 0, w')) =ᶠ[𝓝 w] fun _ => 0 :=
      Filter.eventually_of_mem (hO.mem_nhds (hKO hw)) fun w' hw' => by simpa using h0 w' hw'
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) ℓ).eq_of_nhds, iteratedFDeriv_fun_zero]; rfl
  -- the derivative in `c`
  set P : E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prod 0 with hP
  have hPn : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c' => by
    simp [hP, Prod.norm_def]
  have hdiff : ∀ c' ∈ closedBall (0 : E) δ, HasFDerivWithinAt f
      (L.comp ((fderiv ℝ (iteratedFDeriv ℝ ℓ Φ) (w + c', w)).comp P)) (closedBall (0 : E) δ) c' := by
    intro c' _
    have h1 : HasFDerivAt (fun c'' : E => (w + c'', w)) P c' :=
      ((hasFDerivAt_id c').const_add w).prodMk (hasFDerivAt_const w c')
    have h2 : HasFDerivAt (iteratedFDeriv ℝ ℓ Φ) (fderiv ℝ (iteratedFDeriv ℝ ℓ Φ) (w + c', w)) (w + c', w) :=
      ((hΦ.differentiable_iteratedFDeriv (m := ℓ) (by exact_mod_cast WithTop.coe_lt_top _)) _).hasFDerivAt
    exact (L.hasFDerivAt.comp c' (h2.comp c' h1)).hasFDerivWithinAt
  have hbound : ∀ c' ∈ closedBall (0 : E) δ,
      ‖L.comp ((fderiv ℝ (iteratedFDeriv ℝ ℓ Φ) (w + c', w)).comp P)‖ ≤ |M| := by
    intro c' hc'
    have hmem : (w + c', w) ∈ K' := ⟨(w, c'), ⟨hw, hc'⟩, rfl⟩
    have h3 : ‖fderiv ℝ (iteratedFDeriv ℝ ℓ Φ) (w + c', w)‖ ≤ |M| := by
      rw [norm_fderiv_iteratedFDeriv]; exact (hM _ hmem).trans (le_abs_self _)
    calc _ ≤ ‖L‖ * (‖fderiv ℝ (iteratedFDeriv ℝ ℓ Φ) (w + c', w)‖ * ‖P‖) :=
          (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (|M| * 1) := by gcongr
      _ = |M| := by ring
  have hδ : 0 ≤ δ := (norm_nonneg c).trans hc
  have hmvt := (convex_closedBall (0 : E) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound
    (mem_closedBall_self hδ) (by rwa [mem_closedBall, dist_zero_right])
  rw [hf0, sub_zero, sub_zero] at hmvt
  rw [hfeq]
  exact hmvt

omit [FiniteDimensional ℝ E] in
/-- **A sum of smooth functions with uniformly bounded derivatives.** -/
theorem norm_iteratedFDeriv_sum_le_of_bounds {ι : Type*} (u : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : E) (m : ℕ) {A : ℝ} (hA : ∀ i ∈ u, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ i ∈ u, f i y) x‖ ≤ u.card * A := by
  rw [iteratedFDeriv_sum fun i _ => (hf i).of_le (by exact_mod_cast le_top), Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ u, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ ∑ _i ∈ u, A := Finset.sum_le_sum hA
    _ = u.card * A := by rw [Finset.sum_const, nsmul_eq_mul]

end Lightlike

namespace Lightlike

variable {n : ℕ}

/-- **A quadratic form of functions vanishing on the diagonal**: for `Vx_a(w, w) = 0` near a compact `K` and smooth
`gx_ij`, the derivatives in `w` of `Σ gx_ij(w + c) Vx_i(w + c, w) Vx_j(w + c, w)` of order `≤ ℓ` are `O(‖c‖²)` for
`w ∈ K`, `‖c‖ ≤ δ`. -/
theorem exists_norm_iteratedFDeriv_quad_diag_le {Vx : Fin n → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {gx : Fin n → Fin n → (Fin n → ℝ) → ℝ} (hV : ∀ a, ContDiff ℝ ∞ (Vx a)) (hg : ∀ i j, ContDiff ℝ ∞ (gx i j))
    {K O : Set (Fin n → ℝ)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (h0 : ∀ a, ∀ w ∈ O, Vx a (w, w) = 0) (δ : ℝ) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ c : Fin n → ℝ, ‖c‖ ≤ δ → ∀ m ≤ ℓ,
      ‖iteratedFDeriv ℝ m (fun w' => ∑ i, ∑ j, gx i j (w' + c) * (Vx i (w' + c, w') * Vx j (w' + c, w'))) w‖ ≤
        C * ‖c‖ ^ 2 := by
  -- the bounds for `Vx`
  have hVb := fun am : Fin n × ℕ =>
    exists_norm_iteratedFDeriv_comp_diag_add_le (hV am.1) hK hO hKO (h0 am.1) δ am.2
  choose CV hCV0 hCV using hVb
  set Cv := ∑ a, ∑ m ∈ Finset.range (ℓ + 1), CV (a, m) with hCv
  have hCv0 : 0 ≤ Cv := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun m _ => hCV0 (a, m)
  have hVle : ∀ a, ∀ w ∈ K, ∀ c : Fin n → ℝ, ‖c‖ ≤ δ → ∀ m ≤ ℓ,
      ‖iteratedFDeriv ℝ m (fun w' => Vx a (w' + c, w')) w‖ ≤ Cv * ‖c‖ := by
    intro a w hw c hc m hm
    refine (hCV (a, m) w hw c hc).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h1 : CV (a, m) ≤ ∑ m' ∈ Finset.range (ℓ + 1), CV (a, m') :=
      Finset.single_le_sum (f := fun m' => CV (a, m')) (fun m' _ => hCV0 (a, m'))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
    have h2 : ∑ m' ∈ Finset.range (ℓ + 1), CV (a, m') ≤ Cv :=
      Finset.single_le_sum (f := fun a' => ∑ m' ∈ Finset.range (ℓ + 1), CV (a', m'))
        (fun a' _ => Finset.sum_nonneg fun m' _ => hCV0 (a', m')) (Finset.mem_univ a)
    linarith
  -- the bounds for `gx`
  set Kg := (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 + z.2) '' (K ×ˢ closedBall (0 : Fin n → ℝ) δ) with hKg
  have hKgc : IsCompact Kg := (hK.prod (isCompact_closedBall 0 δ)).image (by fun_prop)
  have hgb := fun ijm : Fin n × Fin n × ℕ => hKgc.exists_bound_of_continuousOn
    ((hg ijm.1 ijm.2.1).continuous_iteratedFDeriv (m := ijm.2.2) (by exact_mod_cast le_top)).continuousOn
  choose Mg hMg using hgb
  set Cg := ∑ i, ∑ j, ∑ m ∈ Finset.range (ℓ + 1), |Mg (i, j, m)| with hCg
  have hgle : ∀ i j, ∀ w ∈ K, ∀ c : Fin n → ℝ, ‖c‖ ≤ δ → ∀ m ≤ ℓ,
      ‖iteratedFDeriv ℝ m (fun w' => gx i j (w' + c)) w‖ ≤ Cg := by
    intro i j w hw c hc m hm
    rw [iteratedFDeriv_comp_add_right]
    have hmem : w + c ∈ Kg := ⟨(w, c), ⟨hw, by rwa [mem_closedBall, dist_zero_right]⟩, rfl⟩
    refine (hMg (i, j, m) _ hmem).trans ((le_abs_self _).trans ?_)
    have h1 : |Mg (i, j, m)| ≤ ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i, j, m')| :=
      Finset.single_le_sum (f := fun m' => |Mg (i, j, m')|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
    have h2 : ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i, j, m')| ≤ ∑ j', ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i, j', m')| :=
      Finset.single_le_sum (f := fun j' => ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i, j', m')|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h3 : ∑ j', ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i, j', m')| ≤ Cg :=
      Finset.single_le_sum (f := fun i' => ∑ j', ∑ m' ∈ Finset.range (ℓ + 1), |Mg (i', j', m')|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _
  refine ⟨(n : ℝ) * ((n : ℝ) * (2 ^ ℓ * Cg * (2 ^ ℓ * Cv * Cv))), by positivity, fun w hw c hc m hm => ?_⟩
  have hsm : ∀ a, ContDiff ℝ ∞ (fun w' : Fin n → ℝ => Vx a (w' + c, w')) := fun a =>
    (hV a).comp ((contDiff_id.add contDiff_const).prodMk contDiff_id)
  have hgs : ∀ i j, ContDiff ℝ ∞ (fun w' : Fin n → ℝ => gx i j (w' + c)) := fun i j =>
    (hg i j).comp (contDiff_id.add contDiff_const)
  have hVV : ∀ i j, ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => Vx i (w' + c, w') * Vx j (w' + c, w')) w‖ ≤
      2 ^ ℓ * (Cv * ‖c‖) * (Cv * ‖c‖) := fun i j =>
    norm_iteratedFDeriv_mul_le_of_bounds (hsm i) (hsm j) w ℓ (hVle i w hw c hc) (hVle j w hw c hc)
  have hgVV : ∀ i j, ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => gx i j (w' + c) *
      (Vx i (w' + c, w') * Vx j (w' + c, w'))) w‖ ≤ 2 ^ ℓ * Cg * (2 ^ ℓ * (Cv * ‖c‖) * (Cv * ‖c‖)) := fun i j =>
    norm_iteratedFDeriv_mul_le_of_bounds (hgs i j) ((hsm i).mul (hsm j)) w ℓ (hgle i j w hw c hc) (hVV i j)
  have hinner : ∀ i, ‖iteratedFDeriv ℝ m (fun w' => ∑ j, gx i j (w' + c) *
      (Vx i (w' + c, w') * Vx j (w' + c, w'))) w‖ ≤
        (Finset.univ : Finset (Fin n)).card * (2 ^ ℓ * Cg * (2 ^ ℓ * (Cv * ‖c‖) * (Cv * ‖c‖))) := fun i =>
    norm_iteratedFDeriv_sum_le_of_bounds _ (fun j => (hgs i j).mul ((hsm i).mul (hsm j))) w m
      fun j _ => hgVV i j m hm
  have houter := norm_iteratedFDeriv_sum_le_of_bounds (Finset.univ : Finset (Fin n))
    (f := fun i w' => ∑ j, gx i j (w' + c) * (Vx i (w' + c, w') * Vx j (w' + c, w')))
    (fun i => ContDiff.sum fun j _ => (hgs i j).mul ((hsm i).mul (hsm j))) w m fun i _ => hinner i
  simp only [Finset.card_univ, Fintype.card_fin] at houter
  calc _ ≤ _ := houter
    _ = (n : ℝ) * ((n : ℝ) * (2 ^ ℓ * Cg * (2 ^ ℓ * Cv * Cv))) * ‖c‖ ^ 2 := by ring

end Lightlike
