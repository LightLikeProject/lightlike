import Mathlib
import Lightlike.Regge.CMS.TriGeom
import Lightlike.Regge.CMS.StarPerturb

/-!
# The displaced star of a vertex (RC6b, step 10)

The edge vectors `w i` of a star in the chart are displaced to normal coordinates,
`u i = normalDisp g v (w i)`. For small size the displaced star is still positively oriented and
winds once around the vertex, so that its frozen-metric angles add up to `2 π`.

## Main results

* `IsRiemMetric.disp_facts`: size, area and displacement bounds of a displaced pair.
* `IsRiemMetric.star_displaced`: the displaced star is positively oriented with angle sum `2 π`.
-/

open Lightlike Lightlike.Geodesic Real

namespace Lightlike.CMS

theorem toC_im_eq (z z' : Fin 2 → ℝ) : (toC z' * (starRingEnd ℂ) (toC z)).im = det2 z z' := by
  simp [toC, det2, Complex.mul_im]; ring

theorem norm_toC_sq (z : Fin 2 → ℝ) : ‖toC z‖ ^ 2 = z ⬝ᵥ z := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [toC, dotProduct, Fin.sum_univ_two]

theorem norm_le_norm_toC (z : Fin 2 → ℝ) : ‖z‖ ≤ ‖toC z‖ := by
  have := norm_sq_le_dot z
  rw [← norm_toC_sq] at this
  exact le_of_sq_le_sq (by simpa using this) (norm_nonneg _)

theorem norm_toC_le (z : Fin 2 → ℝ) : ‖toC z‖ ≤ 2 * ‖z‖ := by
  have h1 := dot_le_two_norm_sq z
  rw [← norm_toC_sq] at h1
  have h0 := norm_nonneg z
  nlinarith [norm_nonneg (toC z)]

set_option maxHeartbeats 4000000 in
/-- **Facts about a displaced pair.** -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.disp_facts
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cu h₀ : ℝ, 0 ≤ Cu ∧ 0 < h₀ ∧ ∀ v ∈ K, ∀ w w' : Fin 2 → ℝ, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ‖w‖ ≤ h → ‖w'‖ ≤ h → ρ * h ^ 2 ≤ det2 w w' →
      ‖fun i => normalDisp g v w i - w i‖ ≤ Cu * h ^ 2 ∧ ‖normalDisp g v w‖ ≤ 2 * h ∧
      ρ / 2 * h ^ 2 ≤ det2 (normalDisp g v w) (normalDisp g v w') ∧
      |det2 (normalDisp g v w) (normalDisp g v w') - det2 w w'| ≤ 6 * Cu * h ^ 3 := by
  obtain ⟨Cu, hCu0, hCu⟩ := hg.exists_normalDisp_bound hK hKU
  refine ⟨Cu, min (min 1 (1 / (Cu + 1))) (ρ / (12 * (Cu + 1))), hCu0,
    lt_min (lt_min one_pos (by positivity)) (by positivity),
    fun v hv w w' h hh hh0 hw hw' hd => ?_⟩
  have hh1 : h ≤ 1 := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhc : h ≤ 1 / (Cu + 1) := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhρ : h ≤ ρ / (12 * (Cu + 1)) := hh0.trans (min_le_right _ _)
  have hCu1 : 0 < Cu + 1 := by linarith
  have hCuh : (Cu + 1) * h ≤ 1 := by
    rw [le_div_iff₀ hCu1] at hhc; linarith
  have h12 : 12 * (Cu + 1) * h ≤ ρ := by
    rw [le_div_iff₀ (by positivity)] at hhρ; linarith
  have hdisp : ∀ x : Fin 2 → ℝ, ‖x‖ ≤ h → ‖fun i => normalDisp g v x i - x i‖ ≤ Cu * h ^ 2 :=
    fun x hx => (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hCu v hv x h hx hh1 i
  have h3 : Cu * h ^ 2 ≤ h := by nlinarith [hCuh, hh]
  have hdn : ∀ x : Fin 2 → ℝ, ‖x‖ ≤ h → ‖normalDisp g v x‖ ≤ 2 * h := fun x hx => by
    have e : normalDisp g v x = x + (fun i => normalDisp g v x i - x i) := by
      funext i; simp
    rw [e]
    have h1 := norm_add_le x (fun i => normalDisp g v x i - x i)
    have h2 := hdisp x hx
    linarith
  have h1 := abs_det2_sub_le w w' (normalDisp g v w) (normalDisp g v w') (hdisp w hw) (hdisp w' hw')
  have h4 : 2 * (Cu * h ^ 2) * (‖w‖ + ‖w'‖ + Cu * h ^ 2) ≤ 2 * (Cu * h ^ 2) * (3 * h) := by
    gcongr; linarith
  have h6 : |det2 (normalDisp g v w) (normalDisp g v w') - det2 w w'| ≤ 6 * Cu * h ^ 3 := by
    refine h1.trans (h4.trans (le_of_eq ?_)); ring
  refine ⟨hdisp w hw, hdn w hw, ?_, h6⟩
  have h5' : 6 * Cu * h ^ 3 ≤ ρ / 2 * h ^ 2 := by
    have : 6 * Cu * h ^ 3 = h ^ 2 * (6 * Cu * h) := by ring
    rw [this]
    have : 6 * Cu * h ≤ ρ / 2 := by nlinarith [hh]
    nlinarith [sq_nonneg h]
  have := (abs_le.mp h6).1
  linarith


set_option maxHeartbeats 4000000 in
/-- **The displaced star winds once around the vertex.** If the chart star `w` is positively
oriented with angle sum `2 π`, has angles at most `π - θ`, and is small, then the star displaced to
normal coordinates is positively oriented and its Euclidean angles still add up to `2 π`. -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.star_displaced
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hθπ : θ ≤ π) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ v ∈ K, ∀ (n : ℕ) [NeZero n] (w : ZMod n → Fin 2 → ℝ) (h : ℝ),
      0 < h → h ≤ h₀ → (∀ i, ‖w i‖ ≤ h) → (∀ i, ρ * h ^ 2 ≤ det2 (w i) (w (i + 1))) →
      ∑ i, InnerProductGeometry.angle (toC (w i)) (toC (w (i + 1))) = 2 * π →
      (∀ i, InnerProductGeometry.angle (toC (w i)) (toC (w (i + 1))) ≤ π - θ) →
      IsPosStar (fun i => toC (normalDisp g v (w i))) ∧
        ∑ i, InnerProductGeometry.angle (toC (normalDisp g v (w i)))
          (toC (normalDisp g v (w (i + 1)))) = 2 * π := by
  obtain ⟨Cu, h₁, hCu0, hh₁, hfacts⟩ := hg.disp_facts hK hKU hρ
  have hsin : 0 < Real.sin (θ / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  refine ⟨min h₁ (ρ * Real.sin (θ / 4) / (16 * (Cu + 1))), lt_min hh₁ (by positivity),
    fun v hv n _ w h hh hh0 hw hd h2π hang => ?_⟩
  have hh1 : h ≤ h₁ := hh0.trans (min_le_left _ _)
  have hh2 : h ≤ ρ * Real.sin (θ / 4) / (16 * (Cu + 1)) := hh0.trans (min_le_right _ _)
  have hCu1 : 0 < Cu + 1 := by linarith
  have hh3 : 16 * (Cu + 1) * h ≤ ρ * Real.sin (θ / 4) := by
    rw [le_div_iff₀ (by positivity)] at hh2; linarith
  have hdet : ∀ i, 0 < det2 (w i) (w (i + 1)) := fun i =>
    lt_of_lt_of_le (by positivity) (hd i)
  have hF := fun i => hfacts v hv (w i) (w (i + 1)) h hh hh1 (hw i) (hw (i + 1)) (hd i)
  have hposw : IsPosStar (fun i => toC (w i)) := fun i => by
    rw [toC_im_eq]; exact hdet i
  have hposu : IsPosStar (fun i => toC (normalDisp g v (w i))) := fun i => by
    rw [toC_im_eq]
    have := (hF i).2.2.1
    have : 0 < ρ / 2 * h ^ 2 := by positivity
    linarith [(hF i).2.2.1]
  refine ⟨hposu, ?_⟩
  have hlow : ∀ i, ρ * h / 2 ≤ ‖toC (w i)‖ := fun i => by
    refine le_trans ?_ (norm_le_norm_toC _)
    have h1 := abs_det2_le (w i) (w (i + 1))
    rw [abs_of_pos (hdet i)] at h1
    have h2 := hd i
    have h3 : ‖w i‖ * (2 * h) ≥ ρ * h ^ 2 := by
      nlinarith [norm_nonneg (w i), norm_nonneg (w (i + 1)), hw (i + 1)]
    have : ρ * h / 2 * (2 * h) ≤ ‖w i‖ * (2 * h) := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  rw [← sum_angle_perturb (w := fun i => toC (w i)) (u := fun i => toC (normalDisp g v (w i)))
    hposw hposu (ε := 4 * Cu * h / ρ) hθ hθπ hang ?_ ?_] at h2π
  · exact h2π
  · rw [show 4 * (4 * Cu * h / ρ) = 16 * Cu * h / ρ by ring, div_le_iff₀ hρ]
    nlinarith [hh3, mul_nonneg hCu0 hh.le]
  · intro i
    have hb : 0 < ‖toC (w i)‖ := lt_of_lt_of_le (by positivity) (hlow i)
    have hb0 : toC (w i) ≠ 0 := norm_pos_iff.mp hb
    rw [div_sub_one hb0, norm_div, div_le_div_iff₀ hb hρ]
    have e : toC (normalDisp g v (w i)) - toC (w i) =
        toC (fun j => normalDisp g v (w i) j - w i j) := (toC_sub _ _).symm
    rw [e]
    have h1 := (norm_toC_le (fun j => normalDisp g v (w i) j - w i j)).trans
      (by linarith [(hF i).1] : 2 * ‖fun j => normalDisp g v (w i) j - w i j‖ ≤ 2 * (Cu * h ^ 2))
    have h2 := hlow i
    calc ‖toC (fun j => normalDisp g v (w i) j - w i j)‖ * ρ ≤ 2 * (Cu * h ^ 2) * ρ := by
          gcongr
      _ ≤ 4 * Cu * h * ‖toC (w i)‖ := by nlinarith [mul_nonneg hCu0 hh.le, mul_nonneg hCu0 hρ.le]


/-- The squared ratio of areas is the area up to a cubic error. -/
theorem area_ratio_err {D E h Cu ρ : ℝ} (hρ : 0 < ρ) (hCu : 0 ≤ Cu) (hh : 0 < h)
    (hD0 : ρ * h ^ 2 ≤ D) (hD1 : D ≤ 2 * h ^ 2) (hE : ρ / 2 * h ^ 2 ≤ E)
    (hDE : |E - D| ≤ 6 * Cu * h ^ 3) : |D ^ 2 / E - D| ≤ 24 * Cu / ρ * h ^ 3 := by
  have hE0 : 0 < E := lt_of_lt_of_le (by positivity) hE
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hD0
  have e : D ^ 2 / E - D = D * (D - E) / E := by field_simp
  rw [e, abs_div, abs_mul, abs_of_pos hD, abs_of_pos hE0, div_le_iff₀ hE0, abs_sub_comm]
  calc D * |E - D| ≤ (2 * h ^ 2) * (6 * Cu * h ^ 3) := by gcongr
    _ = 24 * Cu / ρ * h ^ 3 * (ρ / 2 * h ^ 2) := by field_simp; ring
    _ ≤ 24 * Cu / ρ * h ^ 3 * E := by gcongr

set_option maxHeartbeats 8000000 in
/-- **The deficit of a vertex to third order.** For a star `w` in the chart (positively oriented,
angle sum `2 π`, angles at most `π - θ`, edge vectors of norm at most `h` and consecutive areas at
least `ρ h²`, at most `N` triangles), the Regge deficit computed from geodesic distances is
`(R_v/12) √(det g_v) Σ det(w_i, w_{i+1})` up to `C h³`. -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.vertex_deficit_expansion
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ θ N : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hθπ : θ ≤ π) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ v ∈ K, ∀ (n : ℕ) [NeZero n] (w : ZMod n → Fin 2 → ℝ) (h : ℝ),
      0 < h → h ≤ h₀ → (n : ℝ) ≤ N → (∀ i, ‖w i‖ ≤ h) →
      (∀ i, ρ * h ^ 2 ≤ det2 (w i) (w (i + 1))) →
      ∑ i, InnerProductGeometry.angle (toC (w i)) (toC (w (i + 1))) = 2 * π →
      (∀ i, InnerProductGeometry.angle (toC (w i)) (toC (w (i + 1))) ≤ π - θ) →
      |(2 * π - ∑ i, triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
            (dist g U (v + w i) (v + w (i + 1)) ^ 2)) -
          jetScalar (g v) (jetA g v) (jetB g v) / 12 * √(g v).det *
            ∑ i, det2 (w i) (w (i + 1))| ≤ C * h ^ 3 := by
  obtain ⟨l, Lm, δ, Rm, hl, hLm, hδ, hRm0, hG⟩ := hg.exists_uniform_G hK hKU
  obtain ⟨C₁, h₁, hh₁, htg⟩ := hg.tri_geom hK hKU hρ
  obtain ⟨h₂, hh₂, hsd⟩ := hg.star_displaced hK hKU hρ hθ hθπ
  obtain ⟨Cu, h₃, hCu0, hh₃, hfacts⟩ := hg.disp_facts hK hKU hρ
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Rm / 12 * Lm * (24 * Cu / ρ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨max N 0 * (|C₁| + B), min (min h₁ h₂) h₃, lt_min (lt_min hh₁ hh₂) hh₃,
    fun v hv n _ w h hh hh0 hn hw hd h2π hang => ?_⟩
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ h₃ := hh0.trans (min_le_right _ _)
  obtain ⟨hsym, hlow, hup, hdet, hR⟩ := hG v hv
  have hvU := hKU hv
  obtain ⟨hposu, hsumu⟩ := hsd v hv n w h hh hh2 hw hd h2π hang
  have hdetpos : 0 < (g v).det := lt_of_lt_of_le hδ hdet
  have h00 : 0 < g v 0 0 := (hg.posDef v hvU).diag_pos
  have hdet' : 0 < g v 0 0 * g v 1 1 - g v 0 1 ^ 2 := by
    have := Matrix.det_fin_two (g v)
    rw [← hsym] at this
    nlinarith [this, hdetpos]
  have hF : ∑ i, triAngle (ip (g v) (normalDisp g v (w i)) (normalDisp g v (w i)))
      (ip (g v) (normalDisp g v (w (i + 1))) (normalDisp g v (w (i + 1))))
      (ip (g v) (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)
        (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)) = 2 * π :=
    sum_triAngle_gram (u := fun i => normalDisp g v (w i)) hsym h00 hdet' hposu hsumu
  -- upper bound of the square root of the determinant
  have h11 : 0 < g v 1 1 := by
    have := (hg.posDef v hvU).diag_pos (i := 1); exact this
  have hn1 : ∀ k : Fin 2, ‖(fun i : Fin 2 => if i = k then (1 : ℝ) else 0)‖ ≤ 1 := fun k =>
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
      by_cases hi : i = k <;> simp [hi]
  have hG00 : g v 0 0 ≤ Lm := by
    have := hup (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
    have e : ip (g v) (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = g v 0 0 := by
      simp [ip, Fin.sum_univ_two]
    rw [e] at this
    have h1 : ‖(fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (hn1 0)
    nlinarith
  have hG11 : g v 1 1 ≤ Lm := by
    have := hup (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)
    have e : ip (g v) (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)
        (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) = g v 1 1 := by
      simp [ip, Fin.sum_univ_two]
    rw [e] at this
    have h1 : ‖(fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (hn1 1)
    nlinarith
  have hsq : √(g v).det ≤ Lm := by
    rw [Real.sqrt_le_iff]
    refine ⟨hLm.le, ?_⟩
    have := Matrix.det_fin_two (g v)
    rw [← hsym] at this
    nlinarith [sq_nonneg (g v 0 1), mul_le_mul hG00 hG11 h11.le hLm.le]
  obtain ⟨R, hRdef⟩ : ∃ R, R = jetScalar (g v) (jetA g v) (jetB g v) := ⟨_, rfl⟩
  rw [← hRdef] at hR ⊢
  have hc : |R / 12 * √(g v).det| ≤ Rm / 12 * Lm := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12), abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
  have hi : ∀ i, |triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
        (dist g U (v + w i) (v + w (i + 1)) ^ 2) -
      triAngle (ip (g v) (normalDisp g v (w i)) (normalDisp g v (w i)))
        (ip (g v) (normalDisp g v (w (i + 1))) (normalDisp g v (w (i + 1))))
        (ip (g v) (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)
          (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)) +
      R / 12 * √(g v).det * det2 (w i) (w (i + 1))| ≤ (|C₁| + B) * h ^ 3 := fun i => by
    have t := htg v hv (w i) (w (i + 1)) h hh hh1 (hw i) (hw (i + 1)) (hd i)
    rw [← hRdef] at t
    obtain ⟨-, -, hE, hDE⟩ := hfacts v hv (w i) (w (i + 1)) h hh hh3 (hw i) (hw (i + 1)) (hd i)
    have hD1 : det2 (w i) (w (i + 1)) ≤ 2 * h ^ 2 := by
      have := abs_det2_le (w i) (w (i + 1))
      have h2 := (le_abs_self (det2 (w i) (w (i + 1)))).trans this
      have := mul_le_mul (hw i) (hw (i + 1)) (norm_nonneg _) hh.le
      nlinarith [norm_nonneg (w i)]
    have e := area_ratio_err hρ hCu0 hh (hd i) hD1 hE hDE
    set A := triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
        (dist g U (v + w i) (v + w (i + 1)) ^ 2) with hA
    set F := triAngle (ip (g v) (normalDisp g v (w i)) (normalDisp g v (w i)))
        (ip (g v) (normalDisp g v (w (i + 1))) (normalDisp g v (w (i + 1))))
        (ip (g v) (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)
          (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)) with hFd
    have k : A - F + R / 12 * √(g v).det * det2 (w i) (w (i + 1)) =
        (A - F - (-(R / 12) * √(g v).det * det2 (w i) (w (i + 1)) ^ 2 /
          det2 (normalDisp g v (w i)) (normalDisp g v (w (i + 1))))) +
        (-(R / 12 * √(g v).det)) * (det2 (w i) (w (i + 1)) ^ 2 /
          det2 (normalDisp g v (w i)) (normalDisp g v (w (i + 1))) - det2 (w i) (w (i + 1))) := by
      ring
    rw [k]
    rw [add_mul]
    refine (abs_add_le _ _).trans (add_le_add (t.trans ?_) ?_)
    · gcongr; exact le_abs_self _
    · rw [abs_mul, abs_neg]
      calc |R / 12 * √(g v).det| * |_| ≤ (Rm / 12 * Lm) * (24 * Cu / ρ * h ^ 3) := by gcongr
        _ = B * h ^ 3 := by rw [hB]; ring
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i => triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
        (dist g U (v + w i) (v + w (i + 1)) ^ 2) -
      triAngle (ip (g v) (normalDisp g v (w i)) (normalDisp g v (w i)))
        (ip (g v) (normalDisp g v (w (i + 1))) (normalDisp g v (w (i + 1))))
        (ip (g v) (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)
          (fun j => normalDisp g v (w (i + 1)) j - normalDisp g v (w i) j)) +
      R / 12 * √(g v).det * det2 (w i) (w (i + 1))) Finset.univ
  have hsum2 := hsum.trans (Finset.sum_le_sum fun i _ => hi i)
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsum2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hF, ← Finset.mul_sum] at hsum2
  have hnN : (n : ℝ) ≤ max N 0 := hn.trans (le_max_left _ _)
  have hCB : 0 ≤ |C₁| + B := by positivity
  have hfin : (n : ℝ) * ((|C₁| + B) * h ^ 3) ≤ max N 0 * (|C₁| + B) * h ^ 3 := by
    have : 0 ≤ (|C₁| + B) * h ^ 3 := by positivity
    calc (n : ℝ) * ((|C₁| + B) * h ^ 3) ≤ max N 0 * ((|C₁| + B) * h ^ 3) := by gcongr
      _ = _ := by ring
  have e : 2 * π - ∑ i, triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
        (dist g U (v + w i) (v + w (i + 1)) ^ 2) - R / 12 * √(g v).det * ∑ i, det2 (w i) (w (i + 1)) =
      -(∑ i, triAngle (dist g U v (v + w i) ^ 2) (dist g U v (v + w (i + 1)) ^ 2)
        (dist g U (v + w i) (v + w (i + 1)) ^ 2) - 2 * π +
        R / 12 * √(g v).det * ∑ i, det2 (w i) (w (i + 1))) := by ring
  rw [e, abs_neg]
  exact hsum2.trans hfin

end Lightlike.CMS
