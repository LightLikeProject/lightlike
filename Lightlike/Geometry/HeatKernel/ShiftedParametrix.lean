import Mathlib
import Lightlike.Geometry.HeatKernel.DiagonalVanishing
import Lightlike.Geometry.HeatKernel.ChartBaseDelta
import Lightlike.Asymptotics.SmoothExtension
import Lightlike.Geometry.HeatKernel.GaussDerivBounds

/-!
# The chart parametrix after the substitution `p = w − s v`

For the chart parametrix `H` (`Lightlike.IsChartParametrix`) and `t = s²`, the function
`G(s, w, v) = sⁿ H(s², w − s v, w)` is, near the centre, a smooth function of `(w, v)` whose derivatives in `w` are
bounded by `C (1 + ‖v‖²)^ℓ e^{-c‖v‖²}` uniformly in `s ∈ (0, 1]` (`Lightlike.IsChartParametrix.exists_shifted`). This
is the estimate behind the uniform `C^ℓ` bound of the parametrix operators (Liu Bo, Thm 3.2.13(1), (3.2.98)–(3.2.100),
read): the world function `σ(w − s v, w) = g(V, V)` with `V` vanishing on the diagonal is `s²` times a function whose
derivatives in `w` are `O(‖v‖²)` (`Lightlike.exists_norm_iteratedFDeriv_quad_diag_le`).
-/

open Set Filter Metric Real Nat
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The derivatives of `e^{f}`**: if the derivatives of `f` of orders `1, …, ℓ` at `x` are bounded by `D ≥ 1`, those
of `e^f` are bounded by `ℓ! e^{f(x)} D^ℓ`. -/
theorem norm_iteratedFDeriv_exp_comp_le {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) (ℓ : ℕ) {D : ℝ} (hD1 : 1 ≤ D)
    (hD : ∀ i, 1 ≤ i → i ≤ ℓ → ‖iteratedFDeriv ℝ i f x‖ ≤ D) :
    ‖iteratedFDeriv ℝ ℓ (fun y => Real.exp (f y)) x‖ ≤ ℓ ! * Real.exp (f x) * D ^ ℓ := by
  have h := norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp hf (n := ℓ) (by exact_mod_cast le_top) x
    (C := Real.exp (f x)) (D := D) (fun i _ => by
      rw [← iteratedFDerivWithin_univ]; exact (norm_iteratedFDerivWithin_exp_univ i _).le)
    (fun i hi1 hiℓ => (hD i hi1 hiℓ).trans (le_self_pow₀ hD1 (by omega)))
  exact h

variable [FiniteDimensional ℝ E]

/-- **Uniform bounds for `w ↦ Φ(w + c, w)`**: its derivatives of order `≤ ℓ` are bounded for `w ∈ K`, `‖c‖ ≤ δ`. -/
theorem exists_bound_iteratedFDeriv_comp_diag_add {Φ : E × E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {K : Set E}
    (hK : IsCompact K) (δ : ℝ) (ℓ : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ K, ∀ c : E, ‖c‖ ≤ δ → ∀ m ≤ ℓ,
      ‖iteratedFDeriv ℝ m (fun w' => Φ (w' + c, w')) w‖ ≤ M := by
  set K' := (fun z : E × E => (z.1 + z.2, z.1)) '' (K ×ˢ closedBall (0 : E) δ) with hK'def
  have hK' : IsCompact K' := (hK.prod (isCompact_closedBall 0 δ)).image (by fun_prop)
  have hb := fun m : ℕ => hK'.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn)
  choose Mm hMm using hb
  refine ⟨∑ m ∈ Finset.range (ℓ + 1), |Mm m|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun w hw c hc m hm => ?_⟩
  rw [iteratedFDeriv_comp_diag_add hΦ]
  have hmem : (w + c, w) ∈ K' := ⟨(w, c), ⟨hw, by rwa [mem_closedBall, _root_.dist_zero_right]⟩, rfl⟩
  calc _ ≤ ‖iteratedFDeriv ℝ m Φ (w + c, w)‖ * ∏ _i : Fin m, ‖(diagCLM : E →L[ℝ] E × E)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ |Mm m| * 1 := by
        gcongr
        · exact (hMm m _ hmem).trans (le_abs_self _)
        · exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_diagCLM_le
    _ = |Mm m| := mul_one _
    _ ≤ _ := Finset.single_le_sum (f := fun m' => |Mm m'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

end Helpers

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The chart parametrix after the substitution `p = w − s v`**: there are `ρ ∈ (0, r)` and a function `G(s, w, v)`,
smooth in `(w, v)` for `s ≠ 0`, vanishing when `s v` is off the support of the cutoff, equal to `sⁿ H(s², w − s v, w)`
when `‖w − s v − x‖ ≤ ρ`, whose derivatives in `w` there are `≤ C (1 + ‖v‖²)^ℓ e^{-c‖v‖²}` for `s ∈ (0, 1]`. -/
theorem IsChartParametrix.exists_shifted {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∃ Gx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ,
      (∀ s ≠ 0, ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Gx s z.1 z.2)) ∧
      (∀ s v w, s • v ∉ tsupport θ → Gx s w v = 0) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, ∀ v w, ‖w - s • v - x‖ ≤ ρ → s ^ n * H (s ^ 2) (w - s • v) w = Gx s w v) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ ℓ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0 : ℝ) 1, ∀ v w, ‖w - s • v - x‖ ≤ ρ →
        ‖iteratedFDeriv ℝ ℓ (fun w' => Gx s w' v) w‖ ≤ C * (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2)) := by
  have hr := h.r_pos
  -- the support radius of the cutoff
  have hθc : IsCompact (tsupport θ) := (isCompact_closedBall (0 : Fin n → ℝ) r).of_isClosed_subset
    (isClosed_tsupport θ) (h.θ_tsupport.trans ball_subset_closedBall)
  obtain ⟨r₁, hr₁0, hr₁r, hθr₁⟩ : ∃ r₁ : ℝ, 0 ≤ r₁ ∧ r₁ < r ∧ ∀ z ∈ tsupport θ, ‖z‖ ≤ r₁ := by
    by_cases hne : (tsupport θ).Nonempty
    · obtain ⟨z₀, hz₀, hmax⟩ := hθc.exists_isMaxOn hne continuous_norm.continuousOn
      refine ⟨‖z₀‖, norm_nonneg _, ?_, fun z hz => hmax hz⟩
      have := h.θ_tsupport hz₀; rwa [mem_ball, _root_.dist_zero_right] at this
    · exact ⟨0, le_rfl, hr, fun z hz => absurd ⟨z, hz⟩ hne⟩
  set ρ := (r - r₁) / 2 with hρ
  have hρ0 : 0 < ρ := by linarith
  have hρr : ρ < r := by linarith
  have hρr₁ : ρ + r₁ < r := by linarith
  -- the domain and the compact set where the extensions agree
  set W := {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r} with hWdef
  have hWo : IsOpen W := (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
    (isOpen_lt (continuous_snd.sub continuous_fst).norm continuous_const)
  have hWΩ : W ⊆ Ω := fun q hq => h.mem_of_lt q.1 q.2 hq.1 hq.2
  set A1 := {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ ≤ ρ ∧ ‖q.2 - q.1‖ ≤ r₁} with hA1
  set A2 := (fun w : Fin n → ℝ => (w, w)) '' closedBall x (ρ + r₁) with hA2
  have hA1c : IsCompact A1 := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_fst.sub continuous_const).norm continuous_const).inter
        (isClosed_le (continuous_snd.sub continuous_fst).norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := ((x, x) : (Fin n → ℝ) × (Fin n → ℝ))) (r := ρ + r₁)).subset ?_
      intro q hq
      rw [mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      refine max_le (by linarith [hq.1]) ?_
      have := norm_sub_le_norm_sub_add_norm_sub q.2 q.1 x
      linarith [hq.1, hq.2]
  have hA2c : IsCompact A2 := (isCompact_closedBall x (ρ + r₁)).image (by fun_prop)
  have hKq : IsCompact (A1 ∪ A2) := hA1c.union hA2c
  have hKqW : A1 ∪ A2 ⊆ W := by
    rintro q (hq | ⟨w, hw, rfl⟩)
    · exact ⟨lt_of_le_of_lt hq.1 hρr, lt_of_le_of_lt hq.2 hr₁r⟩
    · rw [mem_closedBall, dist_eq_norm] at hw
      exact ⟨by simp only; linarith, by simpa using hr⟩
  -- the smooth extensions
  have hVsW : ∀ a, ContDiffOn ℝ ∞ (fun q => V q a) W := fun a => contDiffOn_pi.1 (h.V_smooth.mono hWΩ) a
  have hVe := fun a => exists_contDiff_eqOn_nhds hWo (hVsW a) hKq hKqW
  choose Vx hVxs NV hNVo hKNV hVxeq using hVe
  have hue := fun k => exists_contDiff_eqOn_nhds hWo ((h.u_smooth k).mono hWΩ) hKq hKqW
  choose ux huxs Nu hNuo hKNu huxeq using hue
  have hball : ∀ p : Fin n → ℝ, ‖p - x‖ < r → p ∈ U := fun p hp =>
    h.snd_mem (p, p) (h.mem_of_lt p p hp (by simpa using hr))
  have hKpU : closedBall x ρ ⊆ U := fun p hp => hball p (by
    rw [mem_closedBall, dist_eq_norm] at hp; linarith)
  have hge := fun ij : Fin n × Fin n =>
    exists_contDiff_eqOn_nhds hg.isOpen (hg.smooth ij.1 ij.2) (isCompact_closedBall x ρ) hKpU
  choose gx0 hgxs0 Ng hNgo hKNg hgxeq0 using hge
  set gx : Fin n → Fin n → (Fin n → ℝ) → ℝ := fun i j => gx0 (i, j) with hgx
  -- the diagonal set where the extensions of `V` vanish
  set O := {w : Fin n → ℝ | (w, w) ∈ W} ∩ ⋂ a, {w : Fin n → ℝ | (w, w) ∈ NV a} with hOdef
  have hOo : IsOpen O := (hWo.preimage (continuous_id.prodMk continuous_id)).inter
    (isOpen_iInter_of_finite fun a => (hNVo a).preimage (continuous_id.prodMk continuous_id))
  have hKwO : closedBall x (ρ + r₁) ⊆ O := fun w hw =>
    ⟨hKqW (Or.inr ⟨w, hw, rfl⟩), mem_iInter.2 fun a => hKNV a (Or.inr ⟨w, hw, rfl⟩)⟩
  have h0 : ∀ a, ∀ w ∈ O, Vx a (w, w) = 0 := fun a w hw => by
    rw [hVxeq a _ (mem_iInter.1 hw.2 a)]
    rw [(h.V_diag w (hWΩ hw.1)).1]; rfl
  -- the shifted world function and parametrix
  set Ax : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun s w v =>
    (∑ i, ∑ j, gx i j (w + -(s • v)) * (Vx i (w + -(s • v), w) * Vx j (w + -(s • v), w))) / s ^ 2 with hAx
  set Gx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun s w v => θ (s • v) * ((4 * π) ^ (-(n : ℝ) / 2) *
    Real.exp (-(Ax s w v) / 4) * ∑ k ∈ Finset.range (N + 1), (s ^ 2) ^ k * ux k (w + -(s • v), w)) with hGx
  have hgxs : ∀ i j, ContDiff ℝ ∞ (gx i j) := fun i j => hgxs0 (i, j)
  have hθs := h.θ_smooth
  refine ⟨ρ, hρ0, hρr, Gx, fun s _ => ?_, fun s v w hsv => ?_, fun s hs v w hw => ?_, ?_⟩
  · -- smoothness
    have hsh : ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 + -(s • z.2)) := by fun_prop
    have hpair : ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 + -(s • z.2), z.1)) :=
      hsh.prodMk contDiff_fst
    have hA : ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Ax s z.1 z.2) := by
      simp only [hAx]
      refine ContDiff.div_const (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_) _
      exact ((hgxs i j).comp hsh).mul (((hVxs i).comp hpair).mul ((hVxs j).comp hpair))
    simp only [hGx]
    refine (hθs.comp (contDiff_snd.const_smul s)).mul (ContDiff.mul (contDiff_const.mul ?_) ?_)
    · exact Real.contDiff_exp.comp (hA.neg.div_const _)
    · exact ContDiff.sum fun k _ => contDiff_const.mul ((huxs k).comp hpair)
  · -- the support
    simp only [hGx, image_eq_zero_of_notMem_tsupport hsv, zero_mul]
  · -- agreement with the parametrix
    have hs0 : 0 < s := hs.1
    have hneg : w + -(s • v) = w - s • v := (sub_eq_add_neg _ _).symm
    have hθw : w - (w - s • v) = s • v := by abel
    have hpow : s ^ n * (4 * π * s ^ 2) ^ (-(n : ℝ) / 2) = (4 * π) ^ (-(n : ℝ) / 2) := by
      rw [Real.mul_rpow (by positivity) (by positivity), show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ s ^ 2), ← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le,
        show ((2 : ℕ) : ℝ) * ((n : ℝ) / 2) = n by push_cast; ring, Real.rpow_natCast]
      field_simp
    rw [h.H_eq, hθw]
    by_cases hsv : s • v ∈ tsupport θ
    · have hq1 : (w - s • v, w) ∈ A1 := ⟨hw, by simp only; rw [hθw]; exact hθr₁ _ hsv⟩
      have hqK : (w - s • v, w) ∈ A1 ∪ A2 := Or.inl hq1
      have hpρ : w - s • v ∈ closedBall x ρ := by rw [mem_closedBall, dist_eq_norm]; exact hw
      have hσq := h.σ_eq _ (hWΩ (hKqW hqK))
      simp only [hGx, hAx, hneg, heatGaussian, gaussFactor, truncAnsatz, hσq, Geodesic.pairing,
        fun a => hVxeq a _ (hKNV a hqK), fun k => huxeq k _ (hKNu k hqK),
        fun i j => hgxeq0 (i, j) _ (hKNg (i, j) hpρ), hgx]
      have hσsum : ∑ i, ∑ j, V (w - s • v, w) i * (g (w - s • v) i j * V (w - s • v, w) j) =
          ∑ i, ∑ j, g (w - s • v) i j * (V (w - s • v, w) i * V (w - s • v, w) j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hs2 : s ^ 2 ≠ 0 := by positivity
      have he : (-∑ i, ∑ j, V (w - s • v, w) i * (g (w - s • v) i j * V (w - s • v, w) j)) / (4 * s ^ 2) =
          -((∑ i, ∑ j, g (w - s • v) i j * (V (w - s • v, w) i * V (w - s • v, w) j)) / s ^ 2) / 4 := by
        rw [hσsum]; field_simp
      rw [he, ← hpow]
      ring
    · simp only [hGx, image_eq_zero_of_notMem_tsupport hsv, zero_mul, mul_zero]
  · -- the bounds
    obtain ⟨cσ, hcσ, hσlow⟩ := h.σ_lower
    refine ⟨cσ / 4, by positivity, fun ℓ => ?_⟩
    obtain ⟨CQ, hCQ0, hCQ⟩ := exists_norm_iteratedFDeriv_quad_diag_le hVxs hgxs (isCompact_closedBall x (ρ + r₁))
      hOo hKwO h0 r₁ ℓ
    have hub := fun k => exists_bound_iteratedFDeriv_comp_diag_add (huxs k) (isCompact_closedBall x (ρ + r₁)) r₁ ℓ
    choose Mu hMu0 hMu using hub
    set Mu' := ∑ k ∈ Finset.range (N + 1), Mu k with hMu'
    have hMu'0 : 0 ≤ Mu' := Finset.sum_nonneg fun k _ => hMu0 k
    set B := CQ / 4 + 1 with hB
    have hB1 : 1 ≤ B := by rw [hB]; linarith
    refine ⟨(4 * π) ^ (-(n : ℝ) / 2) * (2 ^ ℓ * (ℓ ! * B ^ ℓ) * ((N + 1 : ℕ) * Mu')), by positivity,
      fun s hs v w hw => ?_⟩
    have hs0 : 0 < s := hs.1
    have hRHS0 : 0 ≤ (4 * π) ^ (-(n : ℝ) / 2) * (2 ^ ℓ * (ℓ ! * B ^ ℓ) * ((N + 1 : ℕ) * Mu')) *
        (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(cσ / 4 * ‖v‖ ^ 2)) := by positivity
    by_cases hsv : s • v ∈ tsupport θ
    swap
    · have hz : (fun w' => Gx s w' v) = fun _ => 0 := funext fun w' => by
        simp only [hGx, image_eq_zero_of_notMem_tsupport hsv, zero_mul]
      rw [hz, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]; exact hRHS0
    have hsvr : ‖s • v‖ ≤ r₁ := hθr₁ _ hsv
    have hθw : w - (w - s • v) = s • v := by abel
    have hwK : w ∈ closedBall x (ρ + r₁) := by
      rw [mem_closedBall, dist_eq_norm]
      have := norm_sub_le_norm_sub_add_norm_sub w (w - s • v) x
      rw [hθw] at this; linarith
    have hc : ‖-(s • v)‖ ≤ r₁ := by rwa [norm_neg]
    have hcn : ‖-(s • v)‖ = s * ‖v‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    have hsh : ContDiff ℝ ∞ (fun w' : Fin n → ℝ => w' + -(s • v)) := by fun_prop
    have hpair : ContDiff ℝ ∞ (fun w' : Fin n → ℝ => (w' + -(s • v), w')) := hsh.prodMk contDiff_id
    -- the quadratic form and the exponent
    set Q : (Fin n → ℝ) → ℝ := fun w' =>
      ∑ i, ∑ j, gx i j (w' + -(s • v)) * (Vx i (w' + -(s • v), w') * Vx j (w' + -(s • v), w')) with hQ
    have hQs : ContDiff ℝ ∞ Q := ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      ((hgxs i j).comp hsh).mul (((hVxs i).comp hpair).mul ((hVxs j).comp hpair))
    set f : (Fin n → ℝ) → ℝ := fun w' => (-(1 / (4 * s ^ 2))) * Q w' with hf
    have hfs : ContDiff ℝ ∞ f := contDiff_const.mul hQs
    have hfA : ∀ w', f w' = -(Ax s w' v) / 4 := fun w' => by
      simp only [hf, hQ, hAx]; field_simp
    have hD1 : 1 ≤ B * (1 + ‖v‖ ^ 2) := by nlinarith [sq_nonneg ‖v‖]
    have hfD : ∀ i, 1 ≤ i → i ≤ ℓ → ‖iteratedFDeriv ℝ i f w‖ ≤ B * (1 + ‖v‖ ^ 2) := by
      intro i _ hiℓ
      have hQb := hCQ w hwK (-(s • v)) hc i hiℓ
      rw [hcn] at hQb
      rw [show f = (-(1 / (4 * s ^ 2))) • Q from rfl,
        iteratedFDeriv_const_smul_apply (hQs.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * s ^ 2))]
      calc 1 / (4 * s ^ 2) * ‖iteratedFDeriv ℝ i Q w‖ ≤ 1 / (4 * s ^ 2) * (CQ * (s * ‖v‖) ^ 2) := by gcongr
        _ = CQ / 4 * ‖v‖ ^ 2 := by field_simp
        _ ≤ B * (1 + ‖v‖ ^ 2) := by rw [hB]; nlinarith [sq_nonneg ‖v‖]
    have hE : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => Real.exp (f w')) w‖ ≤
        ℓ ! * Real.exp (f w) * (B * (1 + ‖v‖ ^ 2)) ^ ℓ := by
      intro m hm
      refine (norm_iteratedFDeriv_exp_comp_le hfs w m hD1 fun i hi1 him => hfD i hi1 (him.trans hm)).trans ?_
      have h1 : (m ! : ℝ) ≤ ℓ ! := by exact_mod_cast Nat.factorial_le hm
      have h2 : (B * (1 + ‖v‖ ^ 2)) ^ m ≤ (B * (1 + ‖v‖ ^ 2)) ^ ℓ := pow_le_pow_right₀ hD1 hm
      have h3 := Real.exp_pos (f w)
      gcongr
    -- the coefficient sum
    have hS : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => ∑ k ∈ Finset.range (N + 1),
        (s ^ 2) ^ k * ux k (w' + -(s • v), w')) w‖ ≤ (N + 1 : ℕ) * Mu' := by
      intro m hm
      have := norm_iteratedFDeriv_sum_le_of_bounds (Finset.range (N + 1))
        (f := fun k w' => (s ^ 2) ^ k * ux k (w' + -(s • v), w'))
        (fun k => contDiff_const.mul ((huxs k).comp hpair)) w m (A := Mu') fun k hk => by
          rw [show (fun w' => (s ^ 2) ^ k * ux k (w' + -(s • v), w')) =
              ((s ^ 2) ^ k) • (fun w' => ux k (w' + -(s • v), w')) from rfl,
            iteratedFDeriv_const_smul_apply (f := fun w' => ux k (w' + -(s • v), w'))
              (((huxs k).comp hpair).contDiffAt.of_le (by exact_mod_cast le_top)),
            norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have hs1 : (s ^ 2) ^ k ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith [hs.2])
          calc (s ^ 2) ^ k * ‖iteratedFDeriv ℝ m (fun w' => ux k (w' + -(s • v), w')) w‖ ≤ 1 * Mu k :=
                mul_le_mul hs1 (hMu k w hwK _ hc m hm) (norm_nonneg _) zero_le_one
            _ = Mu k := one_mul _
            _ ≤ Mu' := Finset.single_le_sum (f := Mu) (fun k _ => hMu0 k) hk
      simpa using this
    have hprod := norm_iteratedFDeriv_mul_le_of_bounds (Real.contDiff_exp.comp hfs)
      (ContDiff.sum fun k _ => contDiff_const.mul ((huxs k).comp hpair)) w ℓ hE hS ℓ le_rfl
    -- the lower bound of the exponent
    have hq1 : (w - s • v, w) ∈ A1 := ⟨hw, by simp only; rw [hθw]; exact hsvr⟩
    have hqK : (w - s • v, w) ∈ A1 ∪ A2 := Or.inl hq1
    have hpρ : w - s • v ∈ closedBall x ρ := by rw [mem_closedBall, dist_eq_norm]; exact hw
    have hfw : f w ≤ -(cσ / 4 * ‖v‖ ^ 2) := by
      rw [hfA]
      have hσq := h.σ_eq _ (hWΩ (hKqW hqK))
      have hlow := hσlow (w - s • v) w (lt_of_le_of_lt hw hρr) (by rw [hθw]; exact lt_of_le_of_lt hsvr hr₁r)
      rw [hσq, hθw, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hlow
      have hAeq : Ax s w v * s ^ 2 = Geodesic.pairing g (w - s • v) (V (w - s • v, w)) (V (w - s • v, w)) := by
        simp only [hAx, ← sub_eq_add_neg, fun a => hVxeq a _ (hKNV a hqK),
          fun i j => hgxeq0 (i, j) _ (hKNg (i, j) hpρ), hgx, Geodesic.pairing]
        rw [div_mul_cancel₀ _ (by positivity)]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hA : cσ * ‖v‖ ^ 2 ≤ Ax s w v := by
        have hs2 : 0 < s ^ 2 := by positivity
        rw [← hAeq] at hlow
        nlinarith
      linarith
    -- assemble
    have hGeq : (fun w' => Gx s w' v) = (θ (s • v) * (4 * π) ^ (-(n : ℝ) / 2)) •
        fun w' => Real.exp (f w') * ∑ k ∈ Finset.range (N + 1), (s ^ 2) ^ k * ux k (w' + -(s • v), w') := by
      funext w'; simp only [hGx, Pi.smul_apply, smul_eq_mul, hfA]; ring
    rw [hGeq, iteratedFDeriv_const_smul_apply (f := fun w' => Real.exp (f w') *
        ∑ k ∈ Finset.range (N + 1), (s ^ 2) ^ k * ux k (w' + -(s • v), w')) ((((Real.contDiff_exp.comp hfs)).mul
      (ContDiff.sum fun k _ => contDiff_const.mul ((huxs k).comp hpair))).contDiffAt.of_le
        (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π) ^ (-(n : ℝ) / 2))]
    have hθ1 : |θ (s • v)| ≤ 1 := by rw [abs_of_nonneg (h.θ_mem _).1]; exact (h.θ_mem _).2
    have hexp : Real.exp (f w) ≤ Real.exp (-(cσ / 4 * ‖v‖ ^ 2)) := Real.exp_le_exp.2 hfw
    calc |θ (s • v)| * (4 * π) ^ (-(n : ℝ) / 2) * ‖iteratedFDeriv ℝ ℓ (fun w' => Real.exp (f w') *
          ∑ k ∈ Finset.range (N + 1), (s ^ 2) ^ k * ux k (w' + -(s • v), w')) w‖
        ≤ 1 * (4 * π) ^ (-(n : ℝ) / 2) * (2 ^ ℓ * (ℓ ! * Real.exp (f w) * (B * (1 + ‖v‖ ^ 2)) ^ ℓ) *
            ((N + 1 : ℕ) * Mu')) := by
          gcongr
          exact hprod
      _ ≤ 1 * (4 * π) ^ (-(n : ℝ) / 2) * (2 ^ ℓ * (ℓ ! * Real.exp (-(cσ / 4 * ‖v‖ ^ 2)) *
            (B * (1 + ‖v‖ ^ 2)) ^ ℓ) * ((N + 1 : ℕ) * Mu')) := by gcongr
      _ = _ := by rw [mul_pow]; ring

end Lightlike
