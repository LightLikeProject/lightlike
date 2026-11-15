import Mathlib
import Lightlike.Regge.CMS.Sensitivity
import Lightlike.Regge.CMS.Lipschitz

/-!
# The angle of a triangle whose opposite side has a known first-order error (RC6b, step 6)

The two sides at the vertex are known to `O(h⁵)` and the opposite side to `O(h⁵)` once its leading
correction `P = O(h⁴)` is accounted for. With all sides of order `h` and a bounded cosine, the angle
is the frozen angle plus `P / (2 √(a₀ b₀) q)` up to `O(h³)`, with a constant that depends only on
the shape bounds.

## Main results

* `triangle_expansion`: the statement above, with explicit hypotheses and constants quantified
  before the triangle.
-/

open Real

namespace Lightlike.CMS

set_option maxHeartbeats 3000000 in
/-- **Angle of a nearly flat triangle to order `h³`.** Shape bounds `μ h² ≤ a₀, b₀, c₀ ≤ Λ h²`, a
cosine in `[-s, s]`, and squared lengths `a, b, c` with `|a - a₀|, |b - b₀| ≤ C h⁵`,
`|c - c₀ - P| ≤ C h⁵`, `|P| ≤ C h⁴`. Then `triAngle a b c` is `triAngle a₀ b₀ c₀` plus
`P / (2 √(a₀ b₀) q)`, `q = √(1 - cos²)`, up to `C' h³`. -/
theorem triangle_expansion {μ Λ s C : ℝ} (hμ : 0 < μ) (hΛ : 0 < Λ) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hs : s < 1) :
    ∃ C' h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ a₀ b₀ c₀ a b c P : ℝ,
      μ * h ^ 2 ≤ a₀ → μ * h ^ 2 ≤ b₀ → μ * h ^ 2 ≤ c₀ → a₀ ≤ Λ * h ^ 2 → b₀ ≤ Λ * h ^ 2 →
      c₀ ≤ Λ * h ^ 2 → |a - a₀| ≤ C * h ^ 5 → |b - b₀| ≤ C * h ^ 5 → |c - c₀ - P| ≤ C * h ^ 5 →
      |P| ≤ C * h ^ 4 → cosArg a₀ b₀ c₀ ∈ Set.Icc (-s) s →
      |triAngle a b c - triAngle a₀ b₀ c₀ - P / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀))|
        ≤ C' * h ^ 3 := by
  set Rr : ℝ := 3 * Λ / (2 * μ) with hRr
  have hRr0 : 0 < Rr := by positivity
  set L : ℝ := Λ / μ + 1 with hL
  have hL1 : 1 ≤ L := by have : 0 ≤ Λ / μ := by positivity
                         linarith
  set D : ℝ := 2 * C * L / μ with hD
  have hD0 : 0 ≤ D := by positivity
  set s' : ℝ := (1 + s) / 2 with hs'
  have hs'0 : 0 ≤ s' := by linarith
  have hs'1 : s' < 1 := by linarith
  set η : ℝ := min (1 / 2) ((1 - s) / (4 * (2 * Rr + 1))) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by apply div_pos <;> [linarith; positivity])
  set m : ℝ := √(1 - s ^ 2) with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  set m' : ℝ := √(1 - s' ^ 2) with hm'
  have hm'0 : 0 < m' := Real.sqrt_pos.mpr (by nlinarith)
  refine ⟨KT Rr m' * (C / μ + (2 * C / μ) ^ 2) + C / (2 * μ * m), min 1 (η / (D + 1)),
    lt_min one_pos (by positivity), fun h hh hh0 a₀ b₀ c₀ a b c P ha hb hc haΛ hbΛ hcΛ ha' hb' hc' hP
      hcos => ?_⟩
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hhη : h ≤ η / (D + 1) := hh0.trans (min_le_right _ _)
  have hDh : D * h ≤ η := by
    have : D * h ≤ D * (η / (D + 1)) := by gcongr
    have h2 : D * (η / (D + 1)) ≤ η := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hh3 : h ^ 3 ≤ h ^ 2 := by nlinarith [sq_nonneg h]
  have hh4 : h ^ 4 ≤ h ^ 3 := by nlinarith [pow_pos hh 3]
  have hh5 : h ^ 5 ≤ h ^ 4 := by nlinarith [pow_pos hh 4]
  have hH2 : 0 < h ^ 2 := by positivity
  have ha0 : 0 < a₀ := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < b₀ := lt_of_lt_of_le (by positivity) hb
  have hc0 : 0 < c₀ := lt_of_lt_of_le (by positivity) hc
  have hq : μ * h ^ 2 ≤ √(a₀ * b₀) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ μ * h ^ 2)]
    exact Real.sqrt_le_sqrt (by rw [sq]; exact mul_le_mul ha hb (by positivity) ha0.le)
  have hq0 : 0 < √(a₀ * b₀) := lt_of_lt_of_le (by positivity) hq
  -- relative errors
  set x := (a - a₀) / a₀ with hx
  set y := (b - b₀) / b₀ with hy
  set z := (c - c₀) / c₀ with hz
  have hax : a = a₀ * (1 + x) := by rw [hx]; field_simp; ring
  have hby : b = b₀ * (1 + y) := by rw [hy]; field_simp; ring
  have hcz : c = c₀ * (1 + z) := by rw [hz]; field_simp; ring
  have hc0z : c₀ * z = c - c₀ := by rw [hz]; field_simp
  set ε₃ : ℝ := C / μ * h ^ 3 with hε₃
  set ε₂ : ℝ := 2 * C / μ * h ^ 2 with hε₂
  have hε30 : 0 ≤ ε₃ := by positivity
  have hx' : |x| ≤ ε₃ := by
    rw [hx, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    calc |a - a₀| ≤ C * h ^ 5 := ha'
      _ = C / μ * h ^ 3 * (μ * h ^ 2) := by field_simp
      _ ≤ _ := by gcongr
  have hy' : |y| ≤ ε₃ := by
    rw [hy, abs_div, abs_of_pos hb0, div_le_iff₀ hb0]
    calc |b - b₀| ≤ C * h ^ 5 := hb'
      _ = C / μ * h ^ 3 * (μ * h ^ 2) := by field_simp
      _ ≤ _ := by gcongr
  have hcP : |c - c₀| ≤ 2 * C * h ^ 4 := by
    have : |c - c₀| ≤ |c - c₀ - P| + |P| := by
      have := abs_add_le (c - c₀ - P) P
      simpa using this
    have h5 := mul_le_mul_of_nonneg_left hh5 hC
    have h4 : |P| ≤ C * h ^ 4 := hP
    have h6 : C * h ^ 5 ≤ C * h ^ 4 := h5
    linarith
  have hz' : |z| ≤ ε₂ := by
    rw [hz, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    calc |c - c₀| ≤ 2 * C * h ^ 4 := hcP
      _ = 2 * C / μ * h ^ 2 * (μ * h ^ 2) := by field_simp
      _ ≤ _ := by gcongr
  have h32 : ε₃ ≤ ε₂ := by
    rw [hε₃, hε₂]
    have : C / μ * h ^ 3 ≤ C / μ * h ^ 2 := by gcongr
    have h2 : C / μ * h ^ 2 ≤ 2 * C / μ * h ^ 2 := by
      have : 0 ≤ C / μ * h ^ 2 := by positivity
      have e : 2 * C / μ * h ^ 2 = 2 * (C / μ * h ^ 2) := by ring
      rw [e]; linarith
    linarith
  have hε2D : ε₂ * L ≤ D * h := by
    have : ε₂ * L = D * h ^ 2 := by rw [hε₂, hD]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hh2 hD0
  have hε2L : ε₂ * L ≤ η := hε2D.trans hDh
  have hε0 : 0 ≤ ε₂ := hε30.trans h32
  have hε2 : ε₂ ≤ 1 / 2 := by
    have : ε₂ ≤ ε₂ * L := by nlinarith
    exact this.trans (hε2L.trans (min_le_left _ _))
  have hR : a₀ + b₀ + c₀ ≤ 2 * Rr * √(a₀ * b₀) := by
    have h1 : a₀ + b₀ + c₀ ≤ 3 * Λ * h ^ 2 := by linarith
    calc _ ≤ 3 * Λ * h ^ 2 := h1
      _ = 2 * Rr * (μ * h ^ 2) := by rw [hRr]; field_simp
      _ ≤ _ := by gcongr
  -- the perturbed cosine
  have hcl : |a₀ + b₀ - c₀| ≤ 2 * √(a₀ * b₀) := by
    have := hcos
    unfold cosArg at this
    have h1 := this.1; have h2 := this.2
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ (by positivity)] at h1; nlinarith
    · rw [div_le_iff₀ (by positivity)] at h2; nlinarith
  have hf : cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) ∈ Set.Icc (-s') s' := by
    rw [← hax, ← hby, ← hcz]
    have key := abs_cosArg_sub_le (R := 2 * Rr) (ε := ε₂ * L) ha0 hb0 (by positivity)
      (hε2L.trans (min_le_left _ _)) (a' := a) (b' := b) (c' := c) (c := c₀) ?_ ?_ ?_ ?_ hcl
    · have hk : 2 * (2 * Rr + 1) * (ε₂ * L) ≤ (1 - s) / 2 := by
        have : ε₂ * L ≤ (1 - s) / (4 * (2 * Rr + 1)) := hε2L.trans (min_le_right _ _)
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith
      have hc1 := hcos.1; have hc2 := hcos.2
      have := abs_le.mp (show |(a + b - c) / (2 * √(a * b)) - (a₀ + b₀ - c₀) / (2 * √(a₀ * b₀))|
        ≤ 2 * (2 * Rr + 1) * (ε₂ * L) from key)
      unfold cosArg at hc1 hc2 ⊢
      constructor <;> linarith [this.1, this.2]
    · calc |a - a₀| ≤ ε₃ * a₀ := by
            have := hx'; rw [hx, abs_div, abs_of_pos ha0, div_le_iff₀ ha0] at this; exact this
        _ ≤ ε₂ * L * a₀ := by gcongr; nlinarith
    · calc |b - b₀| ≤ ε₃ * b₀ := by
            have := hy'; rw [hy, abs_div, abs_of_pos hb0, div_le_iff₀ hb0] at this; exact this
        _ ≤ ε₂ * L * b₀ := by gcongr; nlinarith
    · have h1 : |c - c₀| ≤ ε₂ * c₀ := by
        have := hz'; rw [hz, abs_div, abs_of_pos hc0, div_le_iff₀ hc0] at this; exact this
      have h2 : c₀ ≤ L * (a₀ + b₀) := by
        have : Λ * h ^ 2 ≤ Λ / μ * (a₀ + b₀) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hμ]; nlinarith [mul_pos hΛ hH2]
        have : Λ / μ * (a₀ + b₀) ≤ L * (a₀ + b₀) := by gcongr; linarith
        linarith
      calc |c - c₀| ≤ ε₂ * c₀ := h1
        _ ≤ ε₂ * (L * (a₀ + b₀)) := by gcongr
        _ = _ := by ring
    · have : a₀ + b₀ ≤ 2 * Rr * √(a₀ * b₀) := by linarith
      exact this
  have hu' : cosArg a₀ b₀ c₀ ∈ Set.Icc (-s') s' :=
    ⟨by linarith [hcos.1], by linarith [hcos.2]⟩
  have main := abs_triAngle_firstorder_le (R := Rr) (s := s') (ε₂ := ε₂) (ε₃ := ε₃) ha0 hb0 hc0.le
    hx' hy' hz' h32 hε2 hR hs'0 hs'1 hu' hf
  rw [← hax, ← hby, ← hcz, hc0z] at main
  -- the difference between c - c₀ and P
  have hqq : m ≤ qq (cosArg a₀ b₀ c₀) := qq_ge hs hcos
  have hden : μ * h ^ 2 * m ≤ √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀) := mul_le_mul hq hqq hm0.le hq0.le
  have hden0 : 0 < μ * h ^ 2 * m := by positivity
  have hdiff : |(c - c₀) / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀)) -
      P / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀))| ≤ C / (2 * μ * m) * h ^ 3 := by
    rw [← sub_div, abs_div, abs_of_pos (by nlinarith : 0 < 2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀)),
      div_le_iff₀ (by nlinarith)]
    calc |c - c₀ - P| ≤ C * h ^ 5 := hc'
      _ = C / (2 * μ * m) * h ^ 3 * (2 * (μ * h ^ 2 * m)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hden]) (by positivity)
  have hKT : KT Rr m' * (ε₃ + ε₂ ^ 2) ≤ KT Rr m' * (C / μ + (2 * C / μ) ^ 2) * h ^ 3 := by
    have hKT0 : 0 ≤ KT Rr m' := by unfold KT angK; positivity
    have hsum : ε₃ + ε₂ ^ 2 ≤ (C / μ + (2 * C / μ) ^ 2) * h ^ 3 := by
      rw [hε₃, hε₂]
      have e : (2 * C / μ * h ^ 2) ^ 2 = (2 * C / μ) ^ 2 * h ^ 4 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hh4 (sq_nonneg (2 * C / μ))]
    calc _ ≤ KT Rr m' * ((C / μ + (2 * C / μ) ^ 2) * h ^ 3) :=
          mul_le_mul_of_nonneg_left hsum hKT0
      _ = _ := by ring
  calc _ = |(triAngle a b c - triAngle a₀ b₀ c₀ - (c - c₀) / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀))) +
        ((c - c₀) / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀)) -
          P / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ KT Rr m' * (ε₃ + ε₂ ^ 2) + C / (2 * μ * m) * h ^ 3 := add_le_add main hdiff
    _ ≤ _ := by linarith [hKT]

/-- **Non-vacuity.** The hypotheses of `triangle_expansion` hold for the equilateral triangles
`a₀ = b₀ = c₀ = h²` with no perturbation (`μ = Λ = 1`, `C = 0`, `s = 3/5`). -/
example : ∃ C' h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
    |triAngle (h ^ 2) (h ^ 2) (h ^ 2) - triAngle (h ^ 2) (h ^ 2) (h ^ 2) -
      0 / (2 * √(h ^ 2 * h ^ 2) * qq (cosArg (h ^ 2) (h ^ 2) (h ^ 2)))| ≤ C' * h ^ 3 := by
  obtain ⟨C', h₀, h0, H⟩ := triangle_expansion (μ := 1) (Λ := 1) (s := 3 / 5) (C := 0)
    one_pos one_pos le_rfl (by norm_num) (by norm_num)
  refine ⟨C', h₀, h0, fun h hh hh0 => ?_⟩
  have hs : √(h ^ 2 * h ^ 2) = h ^ 2 := by rw [← sq, Real.sqrt_sq (by positivity)]
  have hc : cosArg (h ^ 2) (h ^ 2) (h ^ 2) = 1 / 2 := by
    unfold cosArg; rw [hs]; field_simp; ring
  have := H h hh hh0 (h ^ 2) (h ^ 2) (h ^ 2) (h ^ 2) (h ^ 2) (h ^ 2) 0 (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by rw [hc]; constructor <;> norm_num)
  simpa using this

