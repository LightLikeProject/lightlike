import Mathlib
import Lightlike.Regge.CMS.Bounds
import Lightlike.Regge.CMS.TriangleTL
import Lightlike.Regge.CMS.StarFlat

/-!
# One triangle of a star in normal coordinates (RC6b, step 8)

The displacement to normal coordinates is `h²`-close to the chart displacement, so the chart
area form `det(w, w')` of a fat triangle is `h³`-close to `det(u, u')`.

## Main results

* `IsRiemMetric.exists_normalDisp_bound`: `|u(w)_i - w_i| ≤ Cu h²` for `‖w‖ ≤ h ≤ 1`.
-/

open Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- The chart area form `det(a, b)` of two vectors of the plane. -/
def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

/-- **The displacement to normal coordinates is quadratically close to the identity.** -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.exists_normalDisp_bound
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ v ∈ K, ∀ w : Fin 2 → ℝ, ∀ h : ℝ, ‖w‖ ≤ h → h ≤ 1 → ∀ i,
      |normalDisp g v w i - w i| ≤ Cu * h ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound hK hKU
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  refine ⟨N ^ 2 * M / 2 + (N ^ 3 * M + N ^ 4 * M ^ 2) / 6, by positivity, fun v hv w h hw hh i => ?_⟩
  have hvU : v ∈ U := hKU hv
  have hgam : ∀ i j k, |gam (g v) (jetA g v) i j k| ≤ M := fun i j k => by
    rw [gam_eq_christoffel]; exact (hM v hv i j k i i).2.2.2.2.2.1
  have hdgam : ∀ l i j k, |dGam (g v) (jetA g v) (jetB g v) l i j k| ≤ M := fun l i j k => by
    have e : dGam (g v) (jetA g v) (jetB g v) l i j k = pd l (christoffel g i j k) v :=
      (pd_christoffel hg.coord hvU l i j k).symm
    rw [e]; exact (hM v hv i j k l l).2.2.2.2.2.2
  have hw0 := norm_nonneg w
  have hh0 : 0 ≤ h := hw0.trans hw
  have t1 : |chrV (g v) (jetA g v) w w i| ≤ N ^ 2 * ‖w‖ * ‖w‖ * M := by
    rw [hN]; exact abs_chrV_le hgam w w i
  have t2 : |cub (g v) (jetA g v) (jetB g v) w i| ≤ (N ^ 3 * M + N ^ 4 * M ^ 2) * ‖w‖ ^ 3 / 6 :=
    by rw [hN]; exact abs_cub_le hM0 hgam hdgam w i
  have hw2 : ‖w‖ ^ 2 ≤ h ^ 2 := by gcongr
  have hw3 : ‖w‖ ^ 3 ≤ h ^ 2 := by
    calc ‖w‖ ^ 3 ≤ h ^ 3 := by gcongr
      _ ≤ h ^ 2 := by nlinarith [sq_nonneg h]
  have e : normalDisp g v w i - w i =
      (1 / 2) * chrV (g v) (jetA g v) w w i + cub (g v) (jetA g v) (jetB g v) w i := by
    unfold normalDisp; ring
  rw [e]
  have h1 : |(1 / 2) * chrV (g v) (jetA g v) w w i| ≤ N ^ 2 * M / 2 * h ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : N ^ 2 * ‖w‖ * ‖w‖ * M ≤ N ^ 2 * M * h ^ 2 := by
      have : ‖w‖ * ‖w‖ ≤ h ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg N) hM0]
    linarith
  have h2 : |cub (g v) (jetA g v) (jetB g v) w i| ≤ (N ^ 3 * M + N ^ 4 * M ^ 2) / 6 * h ^ 2 := by
    refine t2.trans ?_
    have : 0 ≤ N ^ 3 * M + N ^ 4 * M ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hw3 this]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **The Gram identity of the plane.** For a symmetric `G`,
`|a|²_G |b|²_G - ⟨a, b⟩_G² = det G · det(a, b)²`. -/
theorem ip_gram {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0) (a b : Fin 2 → ℝ) :
    ip G a a * ip G b b - ip G a b ^ 2 = G.det * det2 a b ^ 2 := by
  simp only [ip, det2, Fin.sum_univ_two, Matrix.det_fin_two]
  rw [← hs]; ring

/-- Symmetry of `ip` for a symmetric `G`. -/
theorem ip_comm {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0) (a b : Fin 2 → ℝ) :
    ip G a b = ip G b a := by
  simp only [ip, Fin.sum_univ_two]; rw [← hs]; ring

/-- Expanding the square of a difference. -/
theorem ip_sub_self {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0) (a b : Fin 2 → ℝ) :
    ip G (fun i => b i - a i) (fun i => b i - a i) = ip G a a + ip G b b - 2 * ip G a b := by
  simp only [ip, Fin.sum_univ_two]; rw [← hs]; ring

/-- `det(a, b)` is bounded by `2 ‖a‖ ‖b‖`. -/
theorem abs_det2_le (a b : Fin 2 → ℝ) : |det2 a b| ≤ 2 * ‖a‖ * ‖b‖ := by
  have a0 := abs_le_norm_apply a 0
  have a1 := abs_le_norm_apply a 1
  have b0 := abs_le_norm_apply b 0
  have b1 := abs_le_norm_apply b 1
  unfold det2
  calc _ ≤ |a 0 * b 1| + |a 1 * b 0| := abs_sub _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul a0 b1 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul a1 b0 (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- `det` of nearby pairs: `|det(a', b') - det(a, b)| ≤ 2 ε (‖a‖ + ‖b‖ + ε)` when the entries move by
at most `ε`. -/
theorem abs_det2_sub_le (a b a' b' : Fin 2 → ℝ) {ε : ℝ} (ha : ‖fun i => a' i - a i‖ ≤ ε)
    (hb : ‖fun i => b' i - b i‖ ≤ ε) : |det2 a' b' - det2 a b| ≤ 2 * ε * (‖a‖ + ‖b‖ + ε) := by
  have e : det2 a' b' - det2 a b =
      det2 (fun i => a' i - a i) b' + det2 a (fun i => b' i - b i) := by
    simp only [det2]; ring
  rw [e]
  have h1 := abs_det2_le (fun i => a' i - a i) b'
  have h2 := abs_det2_le a (fun i => b' i - b i)
  have hb' : ‖b'‖ ≤ ‖b‖ + ε := by
    have : b' = b + (fun i => b' i - b i) := by ext i; simp
    calc ‖b'‖ = ‖b + (fun i => b' i - b i)‖ := by rw [← this]
      _ ≤ ‖b‖ + ‖fun i => b' i - b i‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hε : 0 ≤ ε := (norm_nonneg _).trans ha
  calc _ ≤ |det2 (fun i => a' i - a i) b'| + |det2 a (fun i => b' i - b i)| := abs_add_le _ _
    _ ≤ 2 * ‖fun i => a' i - a i‖ * ‖b'‖ + 2 * ‖a‖ * ‖fun i => b' i - b i‖ := add_le_add h1 h2
    _ ≤ 2 * ε * (‖b‖ + ε) + 2 * ‖a‖ * ε := by
        gcongr
    _ ≤ _ := by nlinarith [norm_nonneg a]

/-- **The product of the two sides and the sine of the frozen angle is the area form.** For the
frozen triangle `(u, u')` in the metric `G`, `√(a₀ b₀) · sin θ = √(det G) · det(u, u')`. -/
theorem sqrt_mul_qq_eq {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0) (hdet : 0 < G.det)
    {u u' : Fin 2 → ℝ} (hu : 0 < det2 u u') (ha : 0 < ip G u u) (hb : 0 < ip G u' u') :
    √(ip G u u * ip G u' u') *
      qq (cosArg (ip G u u) (ip G u' u')
        (ip G (fun i => u' i - u i) (fun i => u' i - u i))) = √G.det * det2 u u' := by
  have hab : 0 < ip G u u * ip G u' u' := mul_pos ha hb
  have hq : 0 < √(ip G u u * ip G u' u') := Real.sqrt_pos.mpr hab
  have hc : cosArg (ip G u u) (ip G u' u') (ip G (fun i => u' i - u i) (fun i => u' i - u i)) =
      ip G u u' / √(ip G u u * ip G u' u') := by
    unfold cosArg; rw [ip_sub_self hs]; field_simp; ring
  have hg := ip_gram hs u u'
  unfold qq
  rw [hc, ← Real.sqrt_mul hab.le]
  have e : ip G u u * ip G u' u' * (1 - (ip G u u' / √(ip G u u * ip G u' u')) ^ 2) =
      G.det * det2 u u' ^ 2 := by
    rw [div_pow, Real.sq_sqrt hab.le]
    field_simp
    linarith
  rw [e, Real.sqrt_mul hdet.le, Real.sqrt_sq hu.le]

/-- **The first-order angle term is a multiple of the area form.** -/
theorem firstorder_eq {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0) (hdet : 0 < G.det)
    {u u' w w' : Fin 2 → ℝ} (R : ℝ) (hu : 0 < det2 u u') (ha : 0 < ip G u u) (hb : 0 < ip G u' u') :
    (-(R / 6) * (ip G w w * ip G w' w' - ip G w w' ^ 2)) /
      (2 * √(ip G u u * ip G u' u') *
        qq (cosArg (ip G u u) (ip G u' u')
          (ip G (fun i => u' i - u i) (fun i => u' i - u i)))) =
      -(R / 12) * √G.det * det2 w w' ^ 2 / det2 u u' := by
  have h := sqrt_mul_qq_eq hs hdet hu ha hb
  rw [mul_assoc, h, ip_gram hs w w']
  have hq : 0 < √G.det := Real.sqrt_pos.mpr hdet
  have hd : √G.det * √G.det = G.det := Real.mul_self_sqrt hdet.le
  field_simp
  have hd2 : √G.det ^ 2 = G.det := Real.sq_sqrt hdet.le
  rw [hd2]; ring

set_option maxHeartbeats 2000000 in
/-- **Shape of a fat frozen triangle.** For a symmetric form `G` with `l ‖x‖² ≤ G(x, x) ≤ Lm ‖x‖²`
and `det G ≥ δ`, and vectors `u, u'` with norms at most `U h` and `det(u, u') ≥ ρ h²`, the squared
sides of the triangle `(0, u, u')` lie between `μ h²` and `Λ h²` and its angle has a cosine in
`[-s, s]`, with constants that depend only on `l, Lm, δ, ρ, U`. -/
theorem tri_shape {l Lm δ ρ U : ℝ} (hl : 0 < l) (hLm : 0 < Lm) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hU : 0 < U) :
    ∃ μ Λ s : ℝ, 0 < μ ∧ 0 < Λ ∧ 0 ≤ s ∧ s < 1 ∧ ∀ (G : Matrix (Fin 2) (Fin 2) ℝ) (h : ℝ),
      0 < h → G 0 1 = G 1 0 → (∀ x, l * ‖x‖ ^ 2 ≤ ip G x x) → (∀ x, ip G x x ≤ Lm * ‖x‖ ^ 2) →
      δ ≤ G.det → ∀ u u' : Fin 2 → ℝ, ‖u‖ ≤ U * h → ‖u'‖ ≤ U * h → ρ * h ^ 2 ≤ det2 u u' →
      (μ * h ^ 2 ≤ ip G u u ∧ μ * h ^ 2 ≤ ip G u' u' ∧
        μ * h ^ 2 ≤ ip G (fun i => u' i - u i) (fun i => u' i - u i)) ∧
      (ip G u u ≤ Λ * h ^ 2 ∧ ip G u' u' ≤ Λ * h ^ 2 ∧
        ip G (fun i => u' i - u i) (fun i => u' i - u i) ≤ Λ * h ^ 2) ∧
      cosArg (ip G u u) (ip G u' u') (ip G (fun i => u' i - u i) (fun i => u' i - u i)) ∈
        Set.Icc (-s) s := by
  set θ : ℝ := min (δ * ρ ^ 2 / (Lm ^ 2 * U ^ 4)) (1 / 2) with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ ≤ 1 / 2 := min_le_right _ _
  refine ⟨l * ρ ^ 2 / (4 * U ^ 2), 4 * Lm * U ^ 2, √(1 - θ), by positivity, by positivity,
    Real.sqrt_nonneg _, ?_, fun G h hh hs hlow hup hdet u u' hu hu' hd => ?_⟩
  · rw [Real.sqrt_lt' one_pos]; linarith
  have hH : 0 < h := hh
  have hd0 : 0 < det2 u u' := lt_of_lt_of_le (by positivity) hd
  have hdu : det2 u (fun i => u' i - u i) = det2 u u' := by simp only [det2]; ring
  set du : Fin 2 → ℝ := fun i => u' i - u i with hdu_def
  have hun : ‖u‖ ≥ ρ * h / (2 * U) := by
    have := abs_det2_le u u'
    rw [abs_of_pos hd0] at this
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg u, norm_nonneg u']
  have hdn : ‖du‖ ≥ ρ * h / (2 * U) := by
    have := abs_det2_le u du
    rw [hdu, abs_of_pos hd0] at this
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg u, norm_nonneg du]
  have hdn' : ‖du‖ ≤ 2 * U * h := by
    calc ‖du‖ = ‖u' - u‖ := rfl
      _ ≤ ‖u'‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hun' : ‖u'‖ ≥ ρ * h / (2 * U) := by
    have := abs_det2_le u u'
    rw [abs_of_pos hd0] at this
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg u, norm_nonneg u']
  have lo : ∀ x : Fin 2 → ℝ, ρ * h / (2 * U) ≤ ‖x‖ → l * ρ ^ 2 / (4 * U ^ 2) * h ^ 2 ≤ ip G x x := by
    intro x hx
    refine le_trans ?_ (hlow x)
    have : (ρ * h / (2 * U)) ^ 2 ≤ ‖x‖ ^ 2 := by gcongr
    calc l * ρ ^ 2 / (4 * U ^ 2) * h ^ 2 = l * (ρ * h / (2 * U)) ^ 2 := by field_simp; ring
      _ ≤ _ := by gcongr
  have up : ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 2 * U * h → ip G x x ≤ 4 * Lm * U ^ 2 * h ^ 2 := by
    intro x hx
    refine le_trans (hup x) ?_
    have : ‖x‖ ^ 2 ≤ (2 * U * h) ^ 2 := by gcongr
    nlinarith
  have ha := lo u hun
  have hb := lo u' hun'
  have hc := lo du hdn
  have ha' := up u (by nlinarith [norm_nonneg u])
  have hb' := up u' (by nlinarith [norm_nonneg u'])
  have hc' := up du hdn'
  refine ⟨⟨ha, hb, hc⟩, ⟨ha', hb', hc'⟩, ?_⟩
  -- the cosine
  have hμ : 0 < l * ρ ^ 2 / (4 * U ^ 2) * h ^ 2 := by positivity
  have hapos : 0 < ip G u u := lt_of_lt_of_le hμ ha
  have hbpos : 0 < ip G u' u' := lt_of_lt_of_le hμ hb
  have hab : 0 < ip G u u * ip G u' u' := mul_pos hapos hbpos
  have hgram := ip_gram hs u u'
  have hcosq : cosArg (ip G u u) (ip G u' u') (ip G du du) ^ 2 ≤ 1 - θ := by
    have hc : cosArg (ip G u u) (ip G u' u') (ip G du du) = ip G u u' / √(ip G u u * ip G u' u') := by
      unfold cosArg; rw [hdu_def, ip_sub_self hs]; field_simp; ring
    rw [hc, div_pow, Real.sq_sqrt hab.le, div_le_iff₀ hab]
    have h1 : ip G u u' ^ 2 = ip G u u * ip G u' u' - G.det * det2 u u' ^ 2 := by linarith
    rw [h1]
    have h2 : θ * (ip G u u * ip G u' u') ≤ G.det * det2 u u' ^ 2 := by
      have hA : ip G u u * ip G u' u' ≤ Lm ^ 2 * U ^ 4 * h ^ 4 := by
        have e1 : Lm * ‖u‖ ^ 2 ≤ Lm * (U * h) ^ 2 := by gcongr
        have e2 : Lm * ‖u'‖ ^ 2 ≤ Lm * (U * h) ^ 2 := by gcongr
        have := mul_le_mul (le_trans (hup u) e1) (le_trans (hup u') e2) hbpos.le (by positivity)
        calc _ ≤ _ := this
          _ = _ := by ring
      have hB : ρ ^ 2 * h ^ 4 ≤ det2 u u' ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hd 2
        calc ρ ^ 2 * h ^ 4 = (ρ * h ^ 2) ^ 2 := by ring
          _ ≤ _ := this
      have hθ' : θ ≤ δ * ρ ^ 2 / (Lm ^ 2 * U ^ 4) := min_le_left _ _
      have hθ2 : θ * (Lm ^ 2 * U ^ 4) ≤ δ * ρ ^ 2 := by
        rwa [le_div_iff₀ (by positivity)] at hθ'
      calc θ * (ip G u u * ip G u' u') ≤ θ * (Lm ^ 2 * U ^ 4 * h ^ 4) := by gcongr
        _ = (θ * (Lm ^ 2 * U ^ 4)) * h ^ 4 := by ring
        _ ≤ (δ * ρ ^ 2) * h ^ 4 := by gcongr
        _ = δ * (ρ ^ 2 * h ^ 4) := by ring
        _ ≤ G.det * (ρ ^ 2 * h ^ 4) := by gcongr
        _ ≤ G.det * det2 u u' ^ 2 := mul_le_mul_of_nonneg_left hB (hδ.le.trans hdet)
    nlinarith [h2]
  rw [Set.mem_Icc]
  have hsq : cosArg (ip G u u) (ip G u' u') (ip G du du) ^ 2 ≤ (√(1 - θ)) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; exact hcosq
  have := abs_le_of_sq_le_sq' hsq (Real.sqrt_nonneg _)
  exact ⟨this.1, this.2⟩

end Lightlike.CMS
