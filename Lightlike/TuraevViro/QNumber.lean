import Lightlike.PonzanoRegge.Pentagon
import Mathlib

/-!
# Quantum integers at a root of unity

For an integer `r ≥ 3`, take `q = e^{iπ/r}`. The quantum integer is
`[n] = (qⁿ - q⁻ⁿ)/(q - q⁻¹) = sin(nπ/r)/sin(π/r)`, a real number.

* `qnum_pos`: `[n] > 0` for `0 < n < r`. Also `[r] = 0` and the symmetry `[r - n] = [n]`.
* `tendsto_qnum`: `[n] → n` as `r → ∞` (the classical limit `q → 1`).
* `qfact`: the quantum factorial, positive below `r`.
* `qAdm r a b c`: admissibility at level `r - 2` (doubled spins): a triangle with
  `a + b + c ≤ 2(r - 2)`.
* `sum_qAdm_qnum`: **the truncated fusion count** `Σ_{b admissible} [b + 1] = [p + 1] [d + 1]`.
  Quantum dimensions respect the level-`(r-2)` fusion rules: the terms that truncation removes
  cancel in pairs. This is the quantum analogue of `sum_tri_succ`.
-/

open Real Finset Filter Topology Lightlike.Pentagon

namespace Lightlike.TV

/-- The quantum integer `[n] = sin(nπ/r)/sin(π/r)`. -/
noncomputable def qnum (r n : ℕ) : ℝ := sin (n * π / r) / sin (π / r)

lemma sin_pi_div_pos {r : ℕ} (hr : 2 ≤ r) : 0 < sin (π / r) := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast hr
  exact sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self pi_pos hr')

lemma qnum_zero (r : ℕ) : qnum r 0 = 0 := by simp [qnum]

lemma qnum_one {r : ℕ} (hr : 2 ≤ r) : qnum r 1 = 1 := by
  rw [qnum, Nat.cast_one, one_mul, div_self (sin_pi_div_pos hr).ne']

/-- Quantum integers `[n] = sin(nπ/r)/sin(π/r)` are positive for `0 < n < r`. -/
lemma qnum_pos {r n : ℕ} (hr : 2 ≤ r) (h0 : 0 < n) (hn : n < r) : 0 < qnum r n := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  refine div_pos (sin_pos_of_pos_of_lt_pi (by positivity) ?_) (sin_pi_div_pos hr)
  rw [div_lt_iff₀ hr0]
  have : (n : ℝ) < r := by exact_mod_cast hn
  nlinarith [pi_pos]

lemma qnum_self {r : ℕ} (hr : 2 ≤ r) : qnum r r = 0 := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [qnum, show (r : ℝ) * π / r = π by field_simp, sin_pi, zero_div]

/-- `[r - n] = [n]`. -/
lemma qnum_sub {r n : ℕ} (hr : 2 ≤ r) (hn : n ≤ r) : qnum r (r - n) = qnum r n := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold qnum
  congr 1
  rw [Nat.cast_sub hn, show ((r : ℝ) - n) * π / r = π - n * π / r by field_simp, sin_pi_sub]

/-- **Classical limit**: `[n] → n` as `r → ∞`. -/
theorem tendsto_qnum (n : ℕ) : Tendsto (fun r : ℕ => qnum r n) atTop (𝓝 n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [qnum_zero]
  have hx : Tendsto (fun r : ℕ => π / (r : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact div_ne_zero pi_ne_zero (by exact_mod_cast hr.ne')
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnx : Tendsto (fun r : ℕ => n * (π / (r : ℝ))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_nhdsWithin_iff.mp hx).1.const_mul (n : ℝ)
    · filter_upwards [(tendsto_nhdsWithin_iff.mp hx).2] with r hr
      exact mul_ne_zero hn' hr
  have h1 := tendsto_sin_div_nhdsNE_zero.comp hx
  have h2 := tendsto_sin_div_nhdsNE_zero.comp hnx
  have := (h2.div h1 one_ne_zero).const_mul (n : ℝ)
  simp only [div_one, mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hs := (sin_pi_div_pos hr).ne'
  show (n : ℝ) * ((sin (n * (π / r)) / (n * (π / r))) / (sin (π / r) / (π / r))) =
    sin (n * π / r) / sin (π / r)
  rw [show (n : ℝ) * π / r = n * (π / r) by ring]
  field_simp

/-- The quantum factorial `[n]! = [1][2]⋯[n]`. -/
noncomputable def qfact (r n : ℕ) : ℝ := ∏ k ∈ range n, qnum r (k + 1)

lemma qfact_pos {r n : ℕ} (hr : 2 ≤ r) (hn : n < r) : 0 < qfact r n :=
  prod_pos fun k hk => qnum_pos hr (by omega) (by have := mem_range.mp hk; omega)

/-- Admissibility at level `r - 2` (doubled spins): a triangle with perimeter `≤ 2(r - 2)`. -/
def qAdm (r a b c : ℕ) : Prop := Tri a b c ∧ a + b + c ≤ 2 * (r - 2)

instance (r a b c : ℕ) : Decidable (qAdm r a b c) := by unfold qAdm Tri; infer_instance

/-! ## The truncated fusion count -/

/-- Telescoping: `Σ_{k ≤ m} sin((l + 2k + 1)θ) sin θ = (cos(lθ) - cos((l + 2m + 2)θ))/2`. -/
lemma sum_sin_mul_sin (θ : ℝ) (l m : ℕ) :
    ∑ k ∈ range (m + 1), sin (((l + 2 * k + 1 : ℕ) : ℝ) * θ) * sin θ =
      (cos ((l : ℝ) * θ) - cos (((l + 2 * m + 2 : ℕ) : ℝ) * θ)) / 2 := by
  have hterm : ∀ k : ℕ, sin (((l + 2 * k + 1 : ℕ) : ℝ) * θ) * sin θ =
      (cos (((l + 2 * k : ℕ) : ℝ) * θ) - cos (((l + 2 * (k + 1) : ℕ) : ℝ) * θ)) / 2 := by
    intro k
    have e1 : ((l + 2 * k : ℕ) : ℝ) * θ = ((l + 2 * k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    have e2 : ((l + 2 * (k + 1) : ℕ) : ℝ) * θ = ((l + 2 * k + 1 : ℕ) : ℝ) * θ + θ := by
      push_cast; ring
    rw [e1, e2, cos_sub, cos_add]
    ring
  rw [sum_congr rfl fun k _ => hterm k, ← sum_div,
    sum_range_sub' (fun k => cos (((l + 2 * k : ℕ) : ℝ) * θ))]
  push_cast
  ring_nf

/-- If the admissible `b` are `l, l + 2, …, l + 2m`, the fusion sum telescopes. -/
lemma sum_qnum_of_image {r p d l m : ℕ} (hr : 2 ≤ r)
    (himg : (range (r - 1)).filter (fun b => qAdm r p b d) = (range (m + 1)).image (· * 2 + l)) :
    ∑ b ∈ range (r - 1), (if qAdm r p b d then qnum r (b + 1) else 0) =
      (cos ((l : ℝ) * (π / r)) - cos (((l + 2 * m + 2 : ℕ) : ℝ) * (π / r))) /
        (2 * sin (π / r) ^ 2) := by
  have hs := (sin_pi_div_pos hr).ne'
  rw [← sum_filter, himg, sum_image (fun k _ k' _ (h : k * 2 + l = k' * 2 + l) => by omega)]
  have := sum_sin_mul_sin (π / r) l m
  have hq : ∀ k : ℕ, qnum r (k * 2 + l + 1) =
      sin (((l + 2 * k + 1 : ℕ) : ℝ) * (π / r)) * sin (π / r) / sin (π / r) ^ 2 := by
    intro k
    rw [qnum]
    field_simp
    congr 1
    push_cast; ring
  rw [sum_congr rfl fun k _ => hq k, ← sum_div, this]
  field_simp

/-- `sin A sin B` in cosines. -/
lemma sin_mul_sin' (A B : ℝ) : sin A * sin B = (cos (A - B) - cos (A + B)) / 2 := by
  rw [cos_sub, cos_add]; ring

lemma qsum_target {r p d : ℕ} (hr : 2 ≤ r) :
    qnum r (p + 1) * qnum r (d + 1) =
      (cos (((d : ℝ) - p) * (π / r)) - cos (((p + d + 2 : ℕ) : ℝ) * (π / r))) /
        (2 * sin (π / r) ^ 2) := by
  have hs := (sin_pi_div_pos hr).ne'
  rw [qnum, qnum, div_mul_div_comm, ← pow_two, sin_mul_sin']
  have e1 : ((p + 1 : ℕ) : ℝ) * π / r - ((d + 1 : ℕ) : ℝ) * π / r =
      -(((d : ℝ) - p) * (π / r)) := by push_cast; ring
  have e2 : ((p + 1 : ℕ) : ℝ) * π / r + ((d + 1 : ℕ) : ℝ) * π / r =
      ((p + d + 2 : ℕ) : ℝ) * (π / r) := by push_cast; ring
  rw [e1, e2, cos_neg]
  field_simp

lemma sum_qAdm_qnum_of_le {r p d : ℕ} (hr : 2 ≤ r) (hpd : p ≤ d) (hd : d ≤ r - 2) :
    ∑ b ∈ range (r - 1), (if qAdm r p b d then qnum r (b + 1) else 0) =
      qnum r (p + 1) * qnum r (d + 1) := by
  have hπ : (r : ℝ) * (π / r) = π := by
    have : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    field_simp
  rw [qsum_target hr]
  by_cases htr : p + d ≤ r - 2
  · -- no truncation: b = d - p, …, d + p
    rw [sum_qnum_of_image (l := d - p) (m := p) hr]
    · congr 2
      · congr 1; push_cast [Nat.cast_sub hpd]; ring
      · rw [show d - p + 2 * p + 2 = p + d + 2 by omega]
    · ext b
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hb, hadm⟩
        unfold qAdm Tri at hadm
        exact ⟨(b - (d - p)) / 2, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        unfold qAdm Tri
        omega
  · -- truncated: b = d - p, …, 2(r-2) - p - d
    rw [sum_qnum_of_image (l := d - p) (m := r - 2 - d) hr]
    · congr 2
      · congr 1; push_cast [Nat.cast_sub hpd]; ring
      · -- cos((2r - 2 - p - d)θ) = cos(2π - (p+d+2)θ) = cos((p+d+2)θ)
        have he : (((d - p + 2 * (r - 2 - d) + 2 : ℕ)) : ℝ) * (π / r) =
            2 * π - ((p + d + 2 : ℕ) : ℝ) * (π / r) := by
          rw [show d - p + 2 * (r - 2 - d) + 2 = 2 * r - (p + d + 2) by omega,
            Nat.cast_sub (by omega)]
          push_cast
          linear_combination 2 * hπ
        rw [he, cos_two_pi_sub]
    · ext b
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hb, hadm⟩
        unfold qAdm Tri at hadm
        exact ⟨(b - (d - p)) / 2, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        unfold qAdm Tri
        omega

/-- **The truncated fusion count**: `Σ_{b adm} [b + 1] = [p + 1][d + 1]` for `p, d ≤ r - 2`. -/
theorem sum_qAdm_qnum {r p d : ℕ} (hr : 2 ≤ r) (hp : p ≤ r - 2) (hd : d ≤ r - 2) :
    ∑ b ∈ range (r - 1), (if qAdm r p b d then qnum r (b + 1) else 0) =
      qnum r (p + 1) * qnum r (d + 1) := by
  rcases le_total p d with h | h
  · exact sum_qAdm_qnum_of_le hr h hd
  · have hsymm : ∀ b, qAdm r p b d ↔ qAdm r d b p := fun b => by unfold qAdm Tri; omega
    simp only [hsymm]
    rw [sum_qAdm_qnum_of_le hr h hp, mul_comm]

end Lightlike.TV
