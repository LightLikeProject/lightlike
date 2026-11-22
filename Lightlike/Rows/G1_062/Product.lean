import Mathlib
import Lightlike.Rows.G1_062.Torus

/-!
# Heat traces of products

The heat trace of a product spectrum `λ₁ + λ₂` (multiplicities multiplied) is the product of
the heat traces, and "`Z = c t^{-d/2} (1 + r)` with `r` smaller than every power of `t`" is
stable under products.  Iterating on circles gives the flat `n`-torus (`Torus.lean`'s circle).

## Main results

* `Lightlike.Rows.G1_062.heatTrace_prod`: the heat trace of a product is the product of the traces.
* `Lightlike.Rows.G1_062.PolyTrace.mul`: product of two traces of the form
  `c t^{-d/2}(1 + r)`, `r = O(t^N)` for all `N`.
* `Lightlike.Rows.G1_062.circleTrace_polyTrace`: the circle heat trace is of this form.
-/

open Filter Topology Asymptotics

namespace Lightlike.Rows.G1_062

/-- The Gaussian theta terms `e^{-π y n²}` are summable over `ℤ` for `y > 0`. -/
theorem summable_exp_int_sq {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℤ => Real.exp (-Real.pi * y * (n : ℝ) ^ 2) := by
  have h := (summable_jacobiTheta₂_term_iff 0 (Complex.I * y)).mpr (by simpa using hy)
  rw [← Complex.summable_ofReal]
  refine h.congr fun n => ?_
  rw [jacobiTheta₂_term, Complex.ofReal_exp]
  congr 1
  push_cast
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((Real.pi : ℂ) * (n : ℂ) ^ 2 * y) * this

/-- The heat trace of a product spectrum is the product of the heat traces, and the product
series is summable. -/
theorem heatTrace_prod {ι₁ ι₂ : Type*} (ev₁ : ι₁ → ℝ) (ev₂ : ι₂ → ℝ) (m₁ : ι₁ → ℕ)
    (m₂ : ι₂ → ℕ) {t : ℝ}
    (h₁ : Summable fun i => (m₁ i : ℝ) * Real.exp (-t * ev₁ i))
    (h₂ : Summable fun i => (m₂ i : ℝ) * Real.exp (-t * ev₂ i)) :
    (Summable fun p : ι₁ × ι₂ =>
        ((m₁ p.1 * m₂ p.2 : ℕ) : ℝ) * Real.exp (-t * (ev₁ p.1 + ev₂ p.2))) ∧
      heatTrace (fun p : ι₁ × ι₂ => ev₁ p.1 + ev₂ p.2) (fun p => m₁ p.1 * m₂ p.2) t
        = heatTrace ev₁ m₁ t * heatTrace ev₂ m₂ t := by
  have key : ∀ p : ι₁ × ι₂,
      ((m₁ p.1 * m₂ p.2 : ℕ) : ℝ) * Real.exp (-t * (ev₁ p.1 + ev₂ p.2))
        = ((m₁ p.1 : ℝ) * Real.exp (-t * ev₁ p.1)) * ((m₂ p.2 : ℝ) * Real.exp (-t * ev₂ p.2)) := by
    intro p
    rw [mul_add, Real.exp_add]
    push_cast
    ring
  have n₁ : Summable fun i => ‖(m₁ i : ℝ) * Real.exp (-t * ev₁ i)‖ := h₁.norm
  have n₂ : Summable fun i => ‖(m₂ i : ℝ) * Real.exp (-t * ev₂ i)‖ := h₂.norm
  refine ⟨?_, ?_⟩
  · simp_rw [key]
    exact summable_mul_of_summable_norm n₁ n₂
  · unfold heatTrace
    simp_rw [key]
    exact (tsum_mul_tsum_of_summable_norm n₁ n₂).symm

/-- `Z(t) = c t^{-d/2} (1 + r(t))` for `t > 0`, where `r = O(t^N)` as `t → 0⁺` for every `N`. -/
def PolyTrace (Z : ℝ → ℝ) (c : ℝ) (d : ℕ) : Prop :=
  ∃ r : ℝ → ℝ, (∀ N : ℕ, r =O[𝓝[>] 0] fun t => t ^ N) ∧
    ∀ t : ℝ, 0 < t → Z t = c * t ^ (-((d : ℝ) / 2)) * (1 + r t)

/-- Products of traces of the form `c t^{-d/2}(1 + r)` are of this form (with `c₁c₂`, `d₁+d₂`). -/
theorem PolyTrace.mul {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ} {d₁ d₂ : ℕ}
    (h₁ : PolyTrace Z₁ c₁ d₁) (h₂ : PolyTrace Z₂ c₂ d₂) :
    PolyTrace (fun t => Z₁ t * Z₂ t) (c₁ * c₂) (d₁ + d₂) := by
  obtain ⟨r₁, hr₁, e₁⟩ := h₁
  obtain ⟨r₂, hr₂, e₂⟩ := h₂
  refine ⟨fun t => r₁ t + r₂ t + r₁ t * r₂ t, fun N => ?_, fun t ht => ?_⟩
  · have a := hr₁ N
    have b := hr₂ N
    have c : (fun t => r₁ t * r₂ t) =O[𝓝[>] 0] fun t : ℝ => t ^ N := by
      have := (hr₁ N).mul (hr₂ 0)
      simp only [pow_zero, mul_one] at this
      exact this
    exact (a.add b).add c
  · beta_reduce
    rw [e₁ t ht, e₂ t ht]
    have : t ^ (-(((d₁ + d₂ : ℕ) : ℝ) / 2)) = t ^ (-((d₁ : ℝ) / 2)) * t ^ (-((d₂ : ℝ) / 2)) := by
      rw [← Real.rpow_add ht]
      congr 1
      push_cast
      ring
    rw [this]
    ring

/-- A trace of the form `c t^{-d/2}(1 + r)` with `r` smaller than every power has the heat
expansion with `a₀ = c` and `aₖ = 0` for `k ≥ 1`. -/
theorem PolyTrace.hasHeatExpansion {Z : ℝ → ℝ} {c : ℝ} {d : ℕ} (h : PolyTrace Z c d) {K : ℕ}
    (hK : 1 ≤ K) :
    HasHeatExpansion Z d (fun k => if k = 0 then c else 0) K := by
  obtain ⟨r, hr, e⟩ := h
  have hsum : ∀ t : ℝ, ∑ k ∈ Finset.range K,
      (fun k : ℕ => if k = 0 then c else 0) k * t ^ ((k : ℝ) - (d : ℝ) / 2)
      = c * t ^ (-((d : ℝ) / 2)) := by
    intro t
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_range.mpr hK) h
  unfold HasHeatExpansion
  simp_rw [hsum]
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have h2 : (fun t : ℝ => c * t ^ (-((d : ℝ) / 2)) * r t) =O[𝓝[>] 0]
      fun t => t ^ (-((d : ℝ) / 2)) * t ^ K :=
    ((isBigO_refl (fun t : ℝ => t ^ (-((d : ℝ) / 2))) _).const_mul_left c).mul (hr K)
  have h3 : (fun t : ℝ => t ^ (-((d : ℝ) / 2)) * t ^ K) =ᶠ[𝓝[>] 0]
      fun t => t ^ ((K : ℝ) - (d : ℝ) / 2) := by
    filter_upwards [hpos] with t ht
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    ring
  refine (h2.trans h3.isBigO).congr' ?_ EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  rw [e t ht]
  ring

/-- The circle heat trace is of the form `c t^{-1/2}(1 + r)` with `r` smaller than every power
(`c = L/√(4π)`). -/
theorem circleTrace_polyTrace {L : ℝ} (hL : 0 < L) :
    PolyTrace (circleTrace L) (L / Real.sqrt (4 * Real.pi)) 1 := by
  have hpi := Real.pi_pos
  refine ⟨fun t => ∑' n : ℤ, Real.exp (-Real.pi * (L ^ 2 / (4 * Real.pi * t)) * (n : ℝ) ^ 2) - 1,
    fun N => ?_, fun t ht => ?_⟩
  · have hexp := exp_neg_div_isBigO_pow (c := L ^ 2 / 4) (by positivity) N
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < L ^ 2 / (4 * Real.pi) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
    have hbound : (fun t : ℝ => ∑' n : ℤ, Real.exp (-Real.pi * (L ^ 2 / (4 * Real.pi * t))
        * (n : ℝ) ^ 2) - 1) =O[𝓝[>] 0] fun t => Real.exp (-(L ^ 2 / 4) / t) := by
      refine IsBigO.of_bound (2 / (1 - Real.exp (-Real.pi))) ?_
      filter_upwards [hpos, hsmall] with t ht hts
      have hy : 1 ≤ L ^ 2 / (4 * Real.pi * t) := by
        rw [le_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hts
        nlinarith
      have := abs_tsum_exp_sub_one_le hy
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine this.trans (le_of_eq ?_)
      congr 2
      field_simp
    exact hbound.trans hexp
  · rw [circleTrace_eq hL ht]
    simp only [Nat.cast_one]
    ring

end Lightlike.Rows.G1_062
