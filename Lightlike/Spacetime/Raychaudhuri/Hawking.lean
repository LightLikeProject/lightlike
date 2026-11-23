import Lightlike.Spacetime.Raychaudhuri.Shifted

/-!
# The analytic core of Hawking's bound: a uniform initial expansion (GE3, Tier 2)

Hawking's cosmological singularity theorem (Hawking 1967; milestone CO3) says: under the timelike convergence condition,
a Cauchy surface of mean curvature `K ≤ C < 0` admits no past-directed timelike curve longer than `-3/C`. Its analytic
step is the Riccati inequality `Θ' ≤ -Θ²/m` (`m = n - 1 = 3`) for the expansion of the normal geodesic congruence: a
*uniform* bound `Θ(0) ≤ C < 0` on the initial expansion bounds the lifetime of the congruence by `m/|C|`, independently of
the point of the surface. This file states that step for functions of one variable (`focusing_hawking`), in the
time-reversed form used for the past-directed congruence of an expanding universe (`focusing_hawking_backward`), and its
sharpness (`hawking_profile_hasDerivAt`: the profile `Θ(s) = m C/(m + C s)` solves the equality case and blows up at
exactly `s = m/|C|`). Manifold versions are in `HawkingManifold.lean`.
-/

open Set Filter Topology

namespace Lightlike

/-- **Hawking's bound, forward**: if `Θ' ≤ -Θ²/m` on `[0, L)` and `Θ(0) ≤ C < 0`, then `L ≤ m/|C|`. -/
theorem focusing_hawking {Θ Θ' : ℝ → ℝ} {L m C : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ico 0 L, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ico 0 L, Θ' s ≤ -(Θ s) ^ 2 / m)
    (hC : C < 0) (h0 : Θ 0 ≤ C) : L ≤ m / |C| := by
  have h := focusing hm hd hle (lt_of_le_of_lt h0 hC)
  refine h.trans (div_le_div_of_nonneg_left hm.le (abs_pos.2 hC.ne) ?_)
  rw [abs_of_neg hC, abs_of_neg (lt_of_le_of_lt h0 hC)]
  linarith

/-- **Hawking's bound from a shifted start**: if `Θ' ≤ -Θ²/m` on `[a, L)` and `Θ(a) ≤ C < 0`, then `L ≤ a + m/|C|`. -/
theorem focusing_hawking_shifted {Θ Θ' : ℝ → ℝ} {a L m C : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ico a L, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ico a L, Θ' s ≤ -(Θ s) ^ 2 / m)
    (hC : C < 0) (h0 : Θ a ≤ C) : L ≤ a + m / |C| := by
  have h := focusing_shifted hm hd hle (lt_of_le_of_lt h0 hC)
  have : m / |Θ a| ≤ m / |C| := by
    refine div_le_div_of_nonneg_left hm.le (abs_pos.2 hC.ne) ?_
    rw [abs_of_neg hC, abs_of_neg (lt_of_le_of_lt h0 hC)]
    linarith
  linarith

/-- **Hawking's bound, backward** (expanding universe, past-directed): if `Θ' ≤ -Θ²/m` on `(a, 0]` and `Θ(0) ≥ H > 0`,
then `-a ≤ m/H`: the congruence cannot extend to the past by more than `m/H` (for `m = 3`, `H = 3H₀`: by more than
`1/H₀`). -/
theorem focusing_hawking_backward {Θ Θ' : ℝ → ℝ} {a m H : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ioc a 0, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ioc a 0, Θ' s ≤ -(Θ s) ^ 2 / m)
    (hH : 0 < H) (h0 : H ≤ Θ 0) : -a ≤ m / H := by
  have h := focusing_backward hm hd hle (lt_of_lt_of_le hH h0)
  exact h.trans (div_le_div_of_nonneg_left hm.le hH h0)

/-- **Sharpness of the Hawking bound**: the profile `Θ(s) = m C/(m + C s)` solves the equality case
`Θ' = -Θ²/m` of the Riccati equation on `s < m/|C|` (for `C < 0`), with `Θ(0) = C`. -/
theorem hawking_profile_hasDerivAt {m C s : ℝ} (_hm : 0 < m) (hC : C < 0) (hs : s < m / |C|) :
    HasDerivAt (fun t => m * C / (m + C * t)) (-(m * C / (m + C * s)) ^ 2 / m) s := by
  have hpos : 0 < m + C * s := by
    rw [abs_of_neg hC, lt_div_iff₀ (by linarith)] at hs
    nlinarith
  have h1 : HasDerivAt (fun t => m + C * t) C s := by
    simpa using ((hasDerivAt_id s).const_mul C).const_add m
  have h2 := (hasDerivAt_const s (m * C)).div h1 hpos.ne'
  convert h2 using 1
  field_simp
  ring

/-- The Hawking profile starts at `C`. -/
theorem hawking_profile_zero {m C : ℝ} (hm : 0 < m) : m * C / (m + C * 0) = C := by
  rw [mul_zero, add_zero, mul_div_cancel_left₀ _ hm.ne']

/-- The Hawking profile is unbounded below as `s ↑ m/|C|`: for `C < 0` it tends to `-∞`. -/
theorem hawking_profile_tendsto {m C : ℝ} (hm : 0 < m) (hC : C < 0) :
    Tendsto (fun t => m * C / (m + C * t)) (𝓝[<] (m / |C|)) atBot := by
  have hs : m + C * (m / |C|) = 0 := by
    have := hC.ne
    rw [abs_of_neg hC]; field_simp; ring
  have hcont : Tendsto (fun t => m + C * t) (𝓝[<] (m / |C|)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun t : ℝ => m + C * t := by fun_prop
      have h := (this.tendsto (m / |C|)).mono_left (nhdsWithin_le_nhds (s := Iio (m / |C|)))
      rwa [hs] at h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : t < m / |C| := ht
      rw [abs_of_neg hC, lt_div_iff₀ (by linarith)] at this
      show 0 < m + C * t
      nlinarith
  have hmC : m * C < 0 := mul_neg_of_pos_of_neg hm hC
  have h2 : Tendsto (fun x : ℝ => m * C * x⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hmC
  exact (h2.comp hcont).congr fun t => by simp [div_eq_mul_inv]

end Lightlike
