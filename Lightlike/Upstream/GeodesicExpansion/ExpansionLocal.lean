import Lightlike.Upstream.GeodesicExpansion.ExpansionBounds
import Mathlib

/-!
# The expansion of the distance: uniform local jets and the calibration estimate

On a compact subset `K ⊆ U` one triple `(B, δ, l)` gives `LocalJet g U x B δ l` at every `x ∈ K`
(`IsRiemMetric.exists_localJet`). Near `x`, the differential of the jet `F = distJet g x` is then
bounded by the metric (`LocalJet.abs_distJetDeriv_le`, the *calibration estimate*).

## Main declarations

* `IsRiemMetric.exists_localJet`
* `IsRiemMetric.abs_dot_le`: Cauchy–Schwarz for the metric
* `calib_real`: the real-variable step of the calibration
* `LocalJet.abs_distJetDeriv_le`
-/

open Matrix Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Uniform local bounds on a compact set**: for a compact `K ⊆ U` one triple `B, δ, l` gives
`LocalJet g U x B δ l` at every `x ∈ K`. -/
theorem IsRiemMetric.exists_localJet (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ B δ l : ℝ, ∀ x ∈ K, LocalJet g U x B δ l := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hδ : 0 < min δ₀ 1 := lt_min hδ₀ one_pos
  have hK' : IsCompact (cthickening (min δ₀ 1) K) := hK.cthickening
  have hK'U : cthickening (min δ₀ 1) K ⊆ U :=
    (cthickening_mono (min_le_left _ _) K).trans hδ₀U
  have hball : ∀ x ∈ K, ∀ u : Fin n → ℝ, ‖u‖ ≤ min δ₀ 1 → x + u ∈ cthickening (min δ₀ 1) K :=
    fun x hx u hu => closedBall_subset_cthickening hx _
      (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hu)
  obtain ⟨m, hm0, hm⟩ := hg.coord.exists_jet_bound hK' hK'U
  obtain ⟨l, L, hl, -, hlL⟩ := hg.exists_bounds_of_isCompact hK' hK'U
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 := mul_nonneg hn hm0
  have p2 := mul_nonneg (pow_nonneg hn 2) hm0
  have p3 := mul_nonneg (pow_nonneg hn 3) hm0
  have p4 := mul_nonneg (pow_nonneg hn 4) hm0
  have p5 := mul_nonneg (pow_nonneg hn 5) hm0
  set B : ℝ := n ^ 5 * m + n ^ 4 * m + n ^ 3 * m + n ^ 2 * m + n * m + 1 with hB
  have t1 : (n : ℝ) * m ≤ B := by linarith
  have t2 : (n : ℝ) ^ 2 * m ≤ B := by linarith
  have t3 : (n : ℝ) ^ 3 * m ≤ B := by linarith
  have t4 : (n : ℝ) ^ 4 * m ≤ B := by linarith
  have t5 : (n : ℝ) ^ 5 * m ≤ B := by linarith
  refine ⟨B, min δ₀ 1, l, fun x hx => ?_⟩
  have hx' : x ∈ cthickening (min δ₀ 1) K := self_subset_cthickening K hx
  have hseg : ∀ u : Fin n → ℝ, ‖u‖ ≤ min δ₀ 1 → ∀ s ∈ Icc (0 : ℝ) 1,
      x + s • u ∈ cthickening (min δ₀ 1) K := fun u hu s hs => hball x hx _ (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg u])
  refine ⟨by linarith, hδ, min_le_right _ _, hl, fun u hu => hK'U (hball x hx u hu), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro p q
    calc _ ≤ _ := abs_dot_mulVec_le hm0 (fun i j => (hm x hx' i j i i i).1) p q
      _ ≤ B * ‖p‖ * ‖q‖ := by gcongr
  · intro u p q
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity)
          (fun i j => abs_dmat_le (fun i j k => (hm x hx' i j k k k).2.2.1) i j) p q
      _ = n ^ 3 * m * ‖u‖ * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ * ‖p‖ * ‖q‖ := by gcongr
  · intro u u' p q
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity)
          (fun i j => abs_ddmat_le (fun i j k l => (hm x hx' i j k l l).2.2.2.1) i j) p q
      _ = n ^ 4 * m * ‖u‖ * ‖u'‖ * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ * ‖u'‖ * ‖p‖ * ‖q‖ := by gcongr
  · intro u v
    calc _ ≤ _ := norm_chr_le hm0 (fun i j k => (hm x hx' i j k k k).2.2.2.2.2.1)
      _ ≤ B * ‖u‖ * ‖v‖ := by gcongr
  · intro a
    calc _ ≤ _ := norm_mulVec_le hm0 (fun i j => (hm x hx' i j i i i).2.1) a
      _ ≤ B * ‖a‖ := by gcongr
  · intro u hu p q
    have hE : ∀ i j, |(g (x + u) - taylorMetric g x u) i j| ≤ n ^ 3 * m * ‖u‖ ^ 3 := by
      intro i j
      have h := taylor_three (f := fun y => g y i j) (hg.coord.smooth i j) hg.coord.isOpen
        (fun s hs => hK'U (hseg u hu s hs))
        (fun s hs k l p => (hm _ (hseg u hu s hs) i j k l p).2.2.2.2.1)
      have e : (g (x + u) - taylorMetric g x u) i j = g (x + u) i j - g x i j
          - ∑ k, u k * pd k (fun y => g y i j) x
          - (1 / 2) * ∑ k, ∑ l, u k * u l * pd l (pd k (fun y => g y i j)) x := by
        simp only [taylorMetric, dmat, ddmat, Matrix.sub_apply, Matrix.add_apply,
          Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        ring
      rw [e]; exact h
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity) hE p q
      _ = n ^ 5 * m * ‖u‖ ^ 3 * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ ^ 3 * ‖p‖ * ‖q‖ := by gcongr
  · intro u hu v
    exact (hlL _ (hball x hx u hu) v).1

/-! ## The calibration estimate -/

/-- **Cauchy–Schwarz** for the metric: `|g(p, v)| ≤ |p|_g |v|_g`. -/
theorem IsRiemMetric.abs_dot_le (hg : IsRiemMetric g U) {z : Fin n → ℝ} (hz : z ∈ U)
    (p v : Fin n → ℝ) : |p ⬝ᵥ (g z *ᵥ v)| ≤ √(normSq g z p) * √(normSq g z v) := by
  have hsym := dot_mulVec_comm (hg.coord.symm z hz) v p
  have hq : ∀ s : ℝ, 0 ≤ normSq g z p * (s * s) + 2 * (p ⬝ᵥ (g z *ᵥ v)) * s + normSq g z v := by
    intro s
    have h := hg.normSq_nonneg hz (v + s • p)
    have e : normSq g z (v + s • p) =
        normSq g z p * (s * s) + 2 * (p ⬝ᵥ (g z *ᵥ v)) * s + normSq g z v := by
      unfold normSq
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      linear_combination s * hsym
    rw [← e]; exact h
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [← Real.sqrt_mul (hg.normSq_nonneg hz p)]
  exact Real.abs_le_sqrt (by nlinarith [hd])

/-- The real-variable step of the calibration: if `F ≥ μ ε²`, `|A| ≤ √PP V` with
`PP ≤ F + D ε⁵`, `√l a ≤ V` and `|dF| ≤ 2 |A| + E ε⁴ a`, then
`|dF| ≤ 2 √F V (1 + κ ε³)` with `κ = D / (2μ) + E / (2 √μ √l)`. -/
theorem calib_real {F μ ε D E V a A PP dF l : ℝ} (hε : 0 ≤ ε) (hμ : 0 < μ) (hl : 0 < l)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : 0 ≤ a) (hF : μ * ε ^ 2 ≤ F) (hA : |A| ≤ √PP * V)
    (hPP : PP ≤ F + D * ε ^ 5) (hV : √l * a ≤ V) (hdF : |dF| ≤ 2 * |A| + E * ε ^ 4 * a) :
    |dF| ≤ 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ 3) := by
  have hF0 : 0 ≤ F := le_trans (by positivity) hF
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have hs0 : 0 ≤ √F := Real.sqrt_nonneg _
  have hss : √F ^ 2 = F := Real.sq_sqrt hF0
  have hsμ : √μ * ε ≤ √F := by
    have := Real.sqrt_le_sqrt hF
    rwa [Real.sqrt_mul hμ.le, Real.sqrt_sq hε] at this
  have hk1 : 0 ≤ D / (2 * μ) * ε ^ 3 := by positivity
  have h1 : F + D * ε ^ 5 ≤ (√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2 := by
    have e : 2 * (D / (2 * μ) * ε ^ 3) * F = D * ε ^ 3 * (F / μ) := by field_simp
    have hFμ : ε ^ 2 ≤ F / μ := by rw [le_div_iff₀ hμ]; linarith
    have h3 : D * ε ^ 5 ≤ 2 * (D / (2 * μ) * ε ^ 3) * F := by
      rw [e]
      calc D * ε ^ 5 = D * ε ^ 3 * ε ^ 2 := by ring
        _ ≤ D * ε ^ 3 * (F / μ) := by gcongr
    have e2 : (√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2 =
        F + 2 * (D / (2 * μ) * ε ^ 3) * F + (D / (2 * μ) * ε ^ 3) ^ 2 * F := by
      rw [mul_pow, hss]; ring
    rw [e2]
    nlinarith [sq_nonneg (D / (2 * μ) * ε ^ 3)]
  have h2 : √PP ≤ √F * (1 + D / (2 * μ) * ε ^ 3) :=
    calc √PP ≤ √(F + D * ε ^ 5) := Real.sqrt_le_sqrt hPP
      _ ≤ √((√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = √F * (1 + D / (2 * μ) * ε ^ 3) := Real.sqrt_sq (by positivity)
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  have hsm : 0 < √μ := Real.sqrt_pos.2 hμ
  have h3 : E * ε ^ 4 * a ≤ 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) := by
    have e : 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) = √F * V * E * ε ^ 3 / (√μ * √l) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc E * ε ^ 4 * a * (√μ * √l) = (E * ε ^ 3) * (√μ * ε) * (√l * a) := by ring
      _ ≤ (E * ε ^ 3) * √F * V := by gcongr
      _ = √F * V * E * ε ^ 3 := by ring
  have h4 : |A| ≤ √F * (1 + D / (2 * μ) * ε ^ 3) * V := hA.trans (mul_le_mul_of_nonneg_right h2 hV0)
  calc |dF| ≤ 2 * |A| + E * ε ^ 4 * a := hdF
    _ ≤ 2 * (√F * (1 + D / (2 * μ) * ε ^ 3) * V)
        + 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) := add_le_add (by linarith) h3
    _ = 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ 3) := by ring

/-- The constant of the calibration estimate. -/
def calibConst (B l : ℝ) : ℝ :=
  46 * B ^ 9 / (2 * (l / 2)) + 15 * B ^ 5 / (2 * (√(l / 2) * √l))

theorem calibConst_nonneg {B l : ℝ} (hB : 0 ≤ B) (hl : 0 < l) : 0 ≤ calibConst B l := by
  unfold calibConst; positivity

/-- **The calibration estimate.** Near `x`, the differential of the jet `F = distJet g x` is
bounded by the metric: `|dF_u(v)| ≤ 2 √F(u) |v|_g (1 + κ ‖u‖³)`, with `|v|_g` the length at
`x + u`. -/
theorem LocalJet.abs_distJetDeriv_le (hg : IsRiemMetric g U) {x : Fin n → ℝ} {B δ l : ℝ}
    (h : LocalJet g U x B δ l) {u : Fin n → ℝ} (hu : ‖u‖ ≤ δ) (hul : B ^ 3 * ‖u‖ ≤ l / 2)
    (v : Fin n → ℝ) :
    |distJetDeriv g x u v| ≤
      2 * √(distJet g x u) * √(normSq g (x + u) v) * (1 + calibConst B l * ‖u‖ ^ 3) := by
  have hu1 : ‖u‖ ≤ 1 := hu.trans h.δ_le_one
  have hx : x ∈ U := by simpa using h.mem 0 (by simpa using h.δ_pos.le)
  have hxu : x + u ∈ U := h.mem u hu
  have hB := h.B_nonneg
  have hε := norm_nonneg u
  have hν := norm_nonneg v
  have hP := h.norm_radial_le hu1
  have hP0 := norm_nonneg (radial g x u)
  have split : ∀ q, radial g x u ⬝ᵥ (taylorMetric g x u *ᵥ q) =
      radial g x u ⬝ᵥ (g (x + u) *ᵥ q)
        - radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ q) := by
    intro q; rw [Matrix.sub_mulVec, dotProduct_sub]; ring
  have tv : |radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ v)| ≤
      4 * (B ^ 5 * ‖u‖ ^ 4) * ‖v‖ := (h.tay_le u hu _ v).trans (by
    calc B * ‖u‖ ^ 3 * ‖radial g x u‖ * ‖v‖ ≤ B * ‖u‖ ^ 3 * (4 * (B ^ 4 * ‖u‖)) * ‖v‖ := by
          gcongr
      _ = _ := by ring)
  have tp : |radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ radial g x u)| ≤
      16 * (B ^ 9 * ‖u‖ ^ 5) := (h.tay_le u hu _ _).trans (by
    calc B * ‖u‖ ^ 3 * ‖radial g x u‖ * ‖radial g x u‖ ≤
          B * ‖u‖ ^ 3 * (4 * (B ^ 4 * ‖u‖)) * (4 * (B ^ 4 * ‖u‖)) := by gcongr
      _ = _ := by ring)
  have hPP : normSq g (x + u) (radial g x u) ≤ distJet g x u + 46 * B ^ 9 * ‖u‖ ^ 5 := by
    have e := split (radial g x u)
    rw [hg.coord.radial_quad_eq hx u] at e
    have a1 := (abs_le.mp (h.abs_radialErr2_le hu1)).2
    have a2 := (abs_le.mp tp).2
    unfold normSq
    linarith
  have hdF : |distJetDeriv g x u v| ≤
      2 * |radial g x u ⬝ᵥ (g (x + u) *ᵥ v)| + 15 * B ^ 5 * ‖u‖ ^ 4 * ‖v‖ := by
    rw [hg.coord.distJetDeriv_eq hx u v, split v]
    have a1 := abs_le.mp (h.abs_radialErr1_le hu1 v)
    have a2 := abs_le.mp tv
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (radial g x u ⬝ᵥ (g (x + u) *ᵥ v)),
        neg_abs_le (radial g x u ⬝ᵥ (g (x + u) *ᵥ v))]
  have hF : l / 2 * ‖u‖ ^ 2 ≤ distJet g x u := by
    have a1 := h.distJet_ge hu1
    have a2 : B ^ 3 * ‖u‖ ^ 3 ≤ l / 2 * ‖u‖ ^ 2 :=
      calc B ^ 3 * ‖u‖ ^ 3 = B ^ 3 * ‖u‖ * ‖u‖ ^ 2 := by ring
        _ ≤ l / 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hul (sq_nonneg _)
    linarith
  have hV : √l * ‖v‖ ≤ √(normSq g (x + u) v) := by
    have := Real.sqrt_le_sqrt
      ((mul_le_mul_of_nonneg_left (norm_sq_le_eNormSq v) h.l_pos.le).trans (h.low u hu v))
    rwa [Real.sqrt_mul h.l_pos.le, Real.sqrt_sq hν] at this
  unfold calibConst
  exact calib_real hε (by linarith [h.l_pos]) h.l_pos (by positivity) (by positivity) hν hF
    (hg.abs_dot_le hxu _ v) hPP hV hdF

end Lightlike.Upstream.GeodesicExpansion
