import Mathlib
import Lightlike.Regge.CMS.Uniform

/-!
# The angle of a geodesic triangle in a chart, to third order (RC6b, step 9)

For `v` in a compact set and `w, w'` of norm at most `h` spanning an area `≥ ρ h²`, the angle at
`v` of the geodesic triangle `(v, v + w, v + w')` differs from the angle of the frozen triangle
`(0, u, u')` (displaced to normal coordinates, measured in `g_v`) by
`-(R_v/12) √(det g_v) det(w, w')² / det(u, u')`, up to `C h³`.

## Main results

* `IsRiemMetric.tri_geom`: the estimate.
-/

open Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

theorem ip_zero_left (G : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ip G 0 x = 0 := by
  simp [ip]

theorem ip_zero_right (G : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ip G x 0 = 0 := by
  simp [ip]

theorem normalDisp_zero {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} (v : Fin 2 → ℝ) :
    normalDisp g v 0 = 0 := by
  funext i
  simp [normalDisp, chrV, cub]


set_option maxHeartbeats 4000000 in
/-- **The angle of a geodesic triangle in a chart, to third order.** -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.tri_geom
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ v ∈ K, ∀ w w' : Fin 2 → ℝ, ∀ h : ℝ, 0 < h → h ≤ h₀ → ‖w‖ ≤ h →
      ‖w'‖ ≤ h → ρ * h ^ 2 ≤ det2 w w' →
      |triAngle (dist g U v (v + w) ^ 2) (dist g U v (v + w') ^ 2)
            (dist g U (v + w) (v + w') ^ 2) -
          triAngle (ip (g v) (normalDisp g v w) (normalDisp g v w))
            (ip (g v) (normalDisp g v w') (normalDisp g v w'))
            (ip (g v) (fun i => normalDisp g v w' i - normalDisp g v w i)
              (fun i => normalDisp g v w' i - normalDisp g v w i)) -
          (-(jetScalar (g v) (jetA g v) (jetB g v) / 12) * √(g v).det * det2 w w' ^ 2 /
            det2 (normalDisp g v w) (normalDisp g v w'))| ≤ C * h ^ 3 := by
  obtain ⟨l, Lm, δ, Rm, hl, hLm, hδ, hRm0, hG⟩ := hg.exists_uniform_G hK hKU
  obtain ⟨Cu, hCu0, hCu⟩ := hg.exists_normalDisp_bound hK hKU
  obtain ⟨C5, r5, hr5, h5⟩ := hg.edge_sq_normal hK hKU
  obtain ⟨μ, Λ, s, hμ, hΛ, hs0, hs1, hshape⟩ :=
    tri_shape hl hLm hδ (half_pos hρ) (by norm_num : (0 : ℝ) < 2)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max |C5| (Rm / 6 * Lm ^ 2) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hC5 : C5 ≤ C := by rw [hC]; exact le_trans (le_abs_self _) (le_max_left _ _)
  have hCP : Rm / 6 * Lm ^ 2 ≤ C := by rw [hC]; exact le_max_right _ _
  obtain ⟨C', h₁, hh₁, hexp⟩ := triangle_expansion hμ hΛ hC0 hs0 hs1
  refine ⟨C', min (min r5 h₁) (min (min 1 (1 / (Cu + 1))) (ρ / (12 * (Cu + 1)))),
    lt_min (lt_min hr5 hh₁) (lt_min (lt_min one_pos (by positivity)) (by positivity)),
    fun v hv w w' h hh hh0 hw hw' hd => ?_⟩
  have hhr : h ≤ r5 := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh1' : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh1 : h ≤ 1 :=
    hh0.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhc : h ≤ 1 / (Cu + 1) :=
    hh0.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhρ : h ≤ ρ / (12 * (Cu + 1)) := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsym, hlow, hup, hdet, hR⟩ := hG v hv
  have hvU := hKU hv
  have hCu1 : 0 < Cu + 1 := by linarith
  have hCuh : (Cu + 1) * h ≤ 1 := by
    rw [le_div_iff₀ hCu1] at hhc; linarith
  have h12 : 12 * (Cu + 1) * h ≤ ρ := by
    rw [le_div_iff₀ (by positivity)] at hhρ; linarith
  -- the displaced vectors
  have hdisp : ∀ x : Fin 2 → ℝ, ‖x‖ ≤ h → ‖fun i => normalDisp g v x i - x i‖ ≤ Cu * h ^ 2 :=
    fun x hx => (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hCu v hv x h hx hh1 i
  have hdn : ∀ x : Fin 2 → ℝ, ‖x‖ ≤ h → ‖normalDisp g v x‖ ≤ 2 * h := fun x hx => by
    have e : normalDisp g v x = x + (fun i => normalDisp g v x i - x i) := by
      funext i; simp
    rw [e]
    have h1 := norm_add_le x (fun i => normalDisp g v x i - x i)
    have h2 := hdisp x hx
    have h3 : Cu * h ^ 2 ≤ h := by nlinarith [hCuh, hh]
    linarith
  have hdet2 : ρ / 2 * h ^ 2 ≤ det2 (normalDisp g v w) (normalDisp g v w') := by
    have h1 := abs_det2_sub_le w w' (normalDisp g v w) (normalDisp g v w') (hdisp w hw) (hdisp w' hw')
    have h3 : Cu * h ^ 2 ≤ h := by nlinarith [hCuh, hh]
    have h4 : 2 * (Cu * h ^ 2) * (‖w‖ + ‖w'‖ + Cu * h ^ 2) ≤ 2 * (Cu * h ^ 2) * (3 * h) := by
      gcongr; linarith
    have h5' : 2 * (Cu * h ^ 2) * (3 * h) ≤ ρ / 2 * h ^ 2 := by
      have : 2 * (Cu * h ^ 2) * (3 * h) = h ^ 2 * (6 * Cu * h) := by ring
      rw [this]
      have : 6 * Cu * h ≤ ρ / 2 := by nlinarith [hh]
      nlinarith [sq_nonneg h]
    have := (abs_le.mp h1).1
    linarith
  obtain ⟨⟨hlo1, hlo2, hlo3⟩, ⟨hup1, hup2, hup3⟩, hcos⟩ :=
    hshape (g v) h hh hsym hlow hup hdet (normalDisp g v w) (normalDisp g v w') (hdn w hw)
      (hdn w' hw') hdet2
  have hpos : 0 < det2 (normalDisp g v w) (normalDisp g v w') := by
    have : 0 < ρ / 2 * h ^ 2 := by positivity
    linarith
  have hdetpos : 0 < (g v).det := lt_of_lt_of_le hδ hdet
  have hμh : 0 < μ * h ^ 2 := by positivity
  -- the three squared distances
  have hz : ‖(0 : Fin 2 → ℝ)‖ ≤ h := by simp [hh.le]
  have e1 := h5 v hv 0 w h hz hw hhr
  have e2 := h5 v hv 0 w' h hz hw' hhr
  have e3 := h5 v hv w w' h hw hw' hhr
  simp only [add_zero, normalDisp_zero, Pi.zero_apply, sub_zero, ip_zero_left, ip_zero_right,
    zero_mul, mul_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at e1 e2
  have hh5 : 0 ≤ h ^ 5 := by positivity
  have hC5h : C5 * h ^ 5 ≤ C * h ^ 5 := by gcongr
  -- the perturbation of the opposite side
  obtain ⟨R, hRdef⟩ : ∃ R, R = jetScalar (g v) (jetA g v) (jetB g v) := ⟨_, rfl⟩
  rw [← hRdef] at e3 hR ⊢
  have hQ := ip_gram hsym w w'
  have hww : 0 ≤ ip (g v) w w := le_trans (by positivity) (hlow w)
  have hww' : 0 ≤ ip (g v) w' w' := le_trans (by positivity) (hlow w')
  have hQ0 : 0 ≤ ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2 := by
    rw [hQ]; positivity
  have hwb : ip (g v) w w ≤ Lm * h ^ 2 := by
    refine (hup w).trans ?_
    have : ‖w‖ ^ 2 ≤ h ^ 2 := by gcongr
    nlinarith
  have hwb' : ip (g v) w' w' ≤ Lm * h ^ 2 := by
    refine (hup w').trans ?_
    have : ‖w'‖ ^ 2 ≤ h ^ 2 := by gcongr
    nlinarith
  have hQ1 : ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2 ≤ Lm ^ 2 * h ^ 4 := by
    have : ip (g v) w w * ip (g v) w' w' ≤ (Lm * h ^ 2) * (Lm * h ^ 2) := by gcongr
    nlinarith [sq_nonneg (ip (g v) w w')]
  have hP : |-(R / 6) * (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2)| ≤ C * h ^ 4 := by
    rw [abs_mul, abs_neg, abs_div, abs_of_nonneg hQ0]
    have h6 : |R| / |(6 : ℝ)| ≤ Rm / 6 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]; gcongr
    calc |R| / |(6 : ℝ)| * (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2)
        ≤ Rm / 6 * (Lm ^ 2 * h ^ 4) := by gcongr
      _ = (Rm / 6 * Lm ^ 2) * h ^ 4 := by ring
      _ ≤ C * h ^ 4 := by gcongr
  have e3' : |dist g U (v + w) (v + w') ^ 2 -
      ip (g v) (fun i => normalDisp g v w' i - normalDisp g v w i)
        (fun i => normalDisp g v w' i - normalDisp g v w i) -
      (-(R / 6) * (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2))| ≤ C * h ^ 5 := by
    refine le_trans (le_of_eq ?_) (e3.trans hC5h)
    congr 1; ring
  have hmain := hexp h hh hh1' (ip (g v) (normalDisp g v w) (normalDisp g v w))
    (ip (g v) (normalDisp g v w') (normalDisp g v w'))
    (ip (g v) (fun i => normalDisp g v w' i - normalDisp g v w i)
      (fun i => normalDisp g v w' i - normalDisp g v w i))
    (dist g U v (v + w) ^ 2) (dist g U v (v + w') ^ 2) (dist g U (v + w) (v + w') ^ 2)
    (-(R / 6) * (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2))
    hlo1 hlo2 hlo3 hup1 hup2 hup3
    (by simpa using e1.trans hC5h) (by simpa using e2.trans hC5h) e3' hP hcos
  have hfo := firstorder_eq (G := g v) hsym hdetpos (w := w) (w' := w') R hpos
    (lt_of_lt_of_le hμh hlo1) (lt_of_lt_of_le hμh hlo2)
  rw [hfo] at hmain
  exact hmain

end Lightlike.CMS
