module

public import Lightlike.Lorentz.Spherical

/-!
# Trust checks for the spherical function of SL(2,ℂ) (milestone HA2)

1. **Known values.** `⟨e₀, π_{0,ρ}(g) e₀⟩ = 1` at `g = 1` (`norm_sphVec`). The spherical function
   `sin(ρr)/(ρ sinh r)` vanishes at `r = π/ρ`; for `ρ = 1` the vector `π(a_π) e₀` is orthogonal
   to `e₀` (`inner_sphVec_diagR_pi`). The kernel `I(g)` equals `π = ∫_ℂ d²z/(1 + |z|²)²` on
   `SU(2)` (`kernelI_ofSU2`).
2. **Non-vacuity.** For `r ≠ 0` the coefficient at `ρ = 0` is `r / sinh r < 1`
   (`inner_sphVec_diagR_zero_lt`), so `e₀` is not fixed by `a_r`: the invariance under `SU(2)`
   does not extend to `SL(2,ℂ)` (`principalSeries_diagR_sphVec_ne`).
3. **Wrong inputs give different answers.** The spherical function of flat `ℝ³`,
   `sin(ρr)/(ρr)`, takes the value `1` at `ρ = 0`, but the coefficient on `SL(2,ℂ)` is
   `1 / sinh 1 ≠ 1` at `r = 1` (`inner_sphVec_ne_flat`). The coefficient depends on `ρ`: at
   `r = π` it is `0` for `ρ = 1` and `π / sinh π ≠ 0` for `ρ = 0` (`inner_sphVec_depends_on_rho`).

The numerical cross-check `scripts/lorentz/spherical_check.py` evaluates `⟨e₀, π(g) e₀⟩` by
two-dimensional quadrature for non-diagonal `g` and compares it with `sphericalFn`.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace

namespace Lightlike.Lorentz

/-- **Known zero**: for `ρ = 1`, `π(a_π) e₀` is orthogonal to `e₀`, since `sin π = 0`. -/
theorem inner_sphVec_diagR_pi :
    ⟪sphVec 1, principalSeries 0 1 (diagR Real.pi) (sphVec 1)⟫_ℂ = 0 := by
  rw [inner_sphVec_diagR]
  simp [sphericalFn, Real.pi_ne_zero, Real.sin_pi]

/-- At `ρ = 0` and `r > 0` the coefficient is `r / sinh r`, strictly less than `1`. -/
theorem inner_sphVec_diagR_zero_lt {r : ℝ} (hr : 0 < r) :
    ⟪sphVec 0, principalSeries 0 0 (diagR r) (sphVec 0)⟫_ℂ = (r / Real.sinh r : ℝ) ∧
      r / Real.sinh r < 1 := by
  refine ⟨?_, ?_⟩
  · rw [inner_sphVec_diagR]; simp [sphericalFn, hr.ne']
  · rw [div_lt_one (Real.sinh_pos_iff.mpr hr)]
    exact Real.self_lt_sinh_iff.mpr hr

/-- **Non-vacuity**: `e₀` is not fixed by `a_r` for `r > 0`. -/
theorem principalSeries_diagR_sphVec_ne {r : ℝ} (hr : 0 < r) :
    principalSeries 0 0 (diagR r) (sphVec 0) ≠ sphVec 0 := by
  intro h
  obtain ⟨h1, h2⟩ := inner_sphVec_diagR_zero_lt hr
  rw [h, inner_self_eq_norm_sq_to_K, norm_sphVec] at h1
  have h3 : ((r / Real.sinh r : ℝ) : ℂ) = 1 := by rw [← h1]; simp
  exact h2.ne (by exact_mod_cast h3)

/-- **Wrong model**: the flat spherical function `sin(ρr)/(ρr)` is `1` at `ρ = 0`, but the
coefficient of `SL(2,ℂ)` at `r = 1` is not. -/
theorem inner_sphVec_ne_flat :
    ⟪sphVec 0, principalSeries 0 0 (diagR 1) (sphVec 0)⟫_ℂ ≠ 1 := by
  obtain ⟨h1, h2⟩ := inner_sphVec_diagR_zero_lt one_pos
  rw [h1]
  intro h
  exact h2.ne (by exact_mod_cast h)

/-- The coefficient depends on `ρ`: at `r = π` it is `0` for `ρ = 1` and nonzero for `ρ = 0`. -/
theorem inner_sphVec_depends_on_rho :
    ⟪sphVec 1, principalSeries 0 1 (diagR Real.pi) (sphVec 1)⟫_ℂ ≠
      ⟪sphVec 0, principalSeries 0 0 (diagR Real.pi) (sphVec 0)⟫_ℂ := by
  rw [inner_sphVec_diagR_pi, (inner_sphVec_diagR_zero_lt Real.pi_pos).1]
  have hs := Real.sinh_pos_iff.mpr Real.pi_pos
  intro h
  have h' : Real.pi / Real.sinh Real.pi = 0 := by exact_mod_cast h.symm
  exact (div_pos Real.pi_pos hs).ne' h'

/-- **Known value**: on `SU(2)`, `I(u) = π = ∫_ℂ d²z / (1 + |z|²)²`. -/
theorem kernelI_ofSU2 (u : Lightlike.SU2) : kernelI (SL2C.ofSU2 u) = Real.pi := by
  have h := coshDist_cartan u 1 0
  rw [show diagR 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [coe_diagR],
    map_one, mul_one, mul_one, Real.cosh_zero] at h
  rw [kernelI_eq, h, Real.arcosh_zero]
  simp [sphericalFn]

end Lightlike.Lorentz
