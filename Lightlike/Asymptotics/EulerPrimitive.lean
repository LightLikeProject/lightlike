import Mathlib
import Lightlike.Asymptotics.MorseLemma

/-!
# The Euler equation `DK(v) v = H(v)`: the order-0 transport equation in normal coordinates

For a smooth `H : ℝⁿ → ℝ` with `H(0) = 0`,

`K(v) = ∫₀¹ Φ(τ, v) dτ`,   `Φ(τ, v) = ∫₀¹ DH(στ v) v dσ`   (`eulerPrimitive`)

is smooth, `K(0) = 0`, and `DK(v) v = H(v)` for every `v` (`fderiv_eulerPrimitive_apply_self`): `K` is the primitive
of `H` along the rays from `0` (`Φ(τ, v) = H(τ v)/τ` for `τ ≠ 0`, by Hadamard's lemma, so
`K(λ v) = ∫₀^λ H(r v)/r dr`). Hence `U = e^K` solves the **Euler (radial transport) equation**
`DU(v) v = H(v) U(v)` with `U(0) = 1` (`fderiv_exp_eulerPrimitive_apply_self`). Both `K` and the radial averages depend smoothly on a
parameter (`contDiff_eulerPrimitive_param`, `contDiff_radialAverage_param`).

In normal coordinates `v` at a point `p`, the Euler operator `DU(v) v` is `g⁻¹(dσ, du)/2` (the gradient of the world
function `σ` is twice the radial vector field), so this solves the transport equation of order `0` with `u₀(p) = 1`,
for `H` the transport coefficient `Δσ/4 + n/2`, which vanishes at `p`
(`Lightlike.IsCoordMetric.transportCoeff_diag`).
-/

open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The inner integral `Φ(τ, v) = ∫₀¹ DH(στ v) v dσ`, equal to `H(τ v)/τ` for `τ ≠ 0`. -/
def eulerKernel (H : (Fin n → ℝ) → ℝ) (τ : ℝ) (v : Fin n → ℝ) : ℝ :=
  ∫ σ in (0 : ℝ)..1, fderiv ℝ H ((σ * τ) • v) v

/-- **The Euler primitive** `K(v) = ∫₀¹ Φ(τ, v) dτ`. -/
def eulerPrimitive (H : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, eulerKernel H τ v

/-- A parametric integral over `[0, 1]` of a smooth function is smooth (`Morse.contDiff_integral_unit` for every
finite order). -/
theorem contDiff_infty_integral_unit {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f : ℝ → X → ℝ} (hf : ContDiff ℝ ∞ (fun p : ℝ × X => f p.1 p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, f t x) :=
  contDiff_infty.2 fun m => Morse.contDiff_integral_unit m (hf.of_le (by exact_mod_cast le_top))

/-- `(x, w) ↦ DH(x) w` is smooth for smooth `H`. -/
theorem contDiff_fderiv_apply {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fderiv ℝ H p.1 p.2) :=
  ((hH.fderiv_right (m := ∞) (by exact_mod_cast le_top)).comp contDiff_fst).clm_apply contDiff_snd

/-- `Φ` is smooth in `(τ, v)`. -/
theorem contDiff_eulerKernel {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => eulerKernel H p.1 p.2) := by
  unfold eulerKernel
  refine contDiff_infty_integral_unit (X := ℝ × (Fin n → ℝ)) (f := fun σ p => fderiv ℝ H ((σ * p.1) • p.2) p.2) ?_
  have hm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × (Fin n → ℝ)) => (((q.1 * q.2.1) • q.2.2), q.2.2)) := by fun_prop
  exact (contDiff_fderiv_apply hH).comp hm

/-- **The Euler primitive is smooth.** -/
theorem contDiff_eulerPrimitive {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (eulerPrimitive H) :=
  contDiff_infty_integral_unit (X := Fin n → ℝ) (f := fun τ v => eulerKernel H τ v) (contDiff_eulerKernel hH)

/-- **Hadamard's lemma**: `H(w) − H(0) = ∫₀¹ DH(σ w) w dσ`. -/
theorem integral_fderiv_ray {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (w : Fin n → ℝ) :
    ∫ σ in (0 : ℝ)..1, fderiv ℝ H (σ • w) w = H w - H 0 := by
  have hd : ∀ σ : ℝ, HasDerivAt (fun s : ℝ => H (s • w)) (fderiv ℝ H (σ • w) w) σ := fun σ => by
    have h1 : HasDerivAt (fun s : ℝ => s • w) ((1 : ℝ) • w) σ := (hasDerivAt_id σ).smul_const w
    have h2 := ((hH.differentiable (by simp)) (σ • w)).hasFDerivAt.comp_hasDerivAt σ h1
    rw [one_smul] at h2
    exact h2
  have hc : Continuous (fun σ : ℝ => fderiv ℝ H (σ • w) w) :=
    (contDiff_fderiv_apply hH).continuous.comp (by fun_prop : Continuous fun σ : ℝ => (σ • w, w))
  rw [integral_eq_sub_of_hasDerivAt (fun σ _ => hd σ) (hc.intervalIntegrable 0 1)]
  simp

/-- `Φ(1, v) = H(v) − H(0)`. -/
theorem eulerKernel_one {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (v : Fin n → ℝ) :
    eulerKernel H 1 v = H v - H 0 := by
  unfold eulerKernel
  simp only [mul_one]
  exact integral_fderiv_ray hH v

/-- The scaling `Φ(τ, λ v) = λ Φ(λ τ, v)`. -/
theorem eulerKernel_smul {H : (Fin n → ℝ) → ℝ} (τ c : ℝ) (v : Fin n → ℝ) :
    eulerKernel H τ (c • v) = c * eulerKernel H (c * τ) v := by
  unfold eulerKernel
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [map_smul, smul_eq_mul, smul_smul]
  ring_nf

/-- `K(λ v) = ∫₀^λ Φ(r, v) dr`. -/
theorem eulerPrimitive_smul {H : (Fin n → ℝ) → ℝ} (c : ℝ) (v : Fin n → ℝ) :
    eulerPrimitive H (c • v) = ∫ r in (0 : ℝ)..c, eulerKernel H r v := by
  unfold eulerPrimitive
  simp only [eulerKernel_smul]
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_left (f := fun r => eulerKernel H r v)]
  simp

/-- **The Euler equation**: `DK(v) v = H(v)` when `H(0) = 0`. -/
theorem fderiv_eulerPrimitive_apply_self {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (v : Fin n → ℝ) : fderiv ℝ (eulerPrimitive H) v v = H v := by
  have hK := contDiff_eulerPrimitive hH
  -- the derivative of `λ ↦ K(λ v)` at `1`, by the chain rule
  have h1 : HasDerivAt (fun c : ℝ => eulerPrimitive H (c • v)) (fderiv ℝ (eulerPrimitive H) v v) 1 := by
    have hs : HasDerivAt (fun c : ℝ => c • v) ((1 : ℝ) • v) 1 := (hasDerivAt_id 1).smul_const v
    have hK1 : HasFDerivAt (eulerPrimitive H) (fderiv ℝ (eulerPrimitive H) v) ((1 : ℝ) • v) := by
      rw [one_smul]; exact ((hK.differentiable (by simp)) v).hasFDerivAt
    have := hK1.comp_hasDerivAt (1 : ℝ) hs
    rw [one_smul] at this
    exact this
  -- and by the fundamental theorem of calculus
  have hc : Continuous (fun r => eulerKernel H r v) :=
    (contDiff_eulerKernel hH).continuous.comp (by fun_prop : Continuous fun r : ℝ => (r, v))
  have h2 : HasDerivAt (fun c : ℝ => eulerPrimitive H (c • v)) (eulerKernel H 1 v) 1 := by
    have := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 1)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun c => ?_)
    exact eulerPrimitive_smul c v
  rw [h1.unique h2, eulerKernel_one hH, h0, sub_zero]

/-- `K(0) = 0`. -/
theorem eulerPrimitive_zero (H : (Fin n → ℝ) → ℝ) : eulerPrimitive H 0 = 0 := by
  have := eulerPrimitive_smul (H := H) 0 (0 : Fin n → ℝ)
  rw [zero_smul] at this
  rw [this]
  simp

/-- **The solution of the radial transport equation of order `0`**: `U = e^K` has `U(0) = 1` and
`DU(v) v = H(v) U(v)`. -/
theorem fderiv_exp_eulerPrimitive_apply_self {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (v : Fin n → ℝ) :
    fderiv ℝ (fun w => Real.exp (eulerPrimitive H w)) v v = H v * Real.exp (eulerPrimitive H v) := by
  have hKd := ((contDiff_eulerPrimitive hH).differentiable (by simp)) v
  have h := hKd.hasFDerivAt.exp
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, fderiv_eulerPrimitive_apply_self hH h0 v]
  ring

/-- **The radial average of order `k`**: `W(v) = ∫₀¹ τ^{k-1} G(τ v) dτ`. -/
def radialAverage (k : ℕ) (G : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, τ ^ (k - 1) * G (τ • v)

/-- **The radial average is smooth.** -/
theorem contDiff_radialAverage (k : ℕ) {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (radialAverage k G) := by
  unfold radialAverage
  refine contDiff_infty_integral_unit (X := Fin n → ℝ) (f := fun τ v => τ ^ (k - 1) * G (τ • v)) ?_
  have hm : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => p.1 • p.2) := by fun_prop
  exact (contDiff_fst.pow _).mul (hG.comp hm)

/-- `λᵏ W(λ v) = ∫₀^λ r^{k-1} G(r v) dr`. -/
theorem radialAverage_smul (k : ℕ) (hk : 1 ≤ k) (G : (Fin n → ℝ) → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    c ^ k * radialAverage k G (c • v) = ∫ r in (0 : ℝ)..c, r ^ (k - 1) * G (r • v) := by
  unfold radialAverage
  have hck : c ^ k = c * c ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : ∀ τ : ℝ, c ^ k * (τ ^ (k - 1) * G (τ • c • v)) = c * ((c * τ) ^ (k - 1) * G ((c * τ) • v)) := by
    intro τ
    rw [smul_smul, mul_pow, mul_comm τ c, hck]
    ring
  rw [← intervalIntegral.integral_const_mul]
  simp only [this]
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_left (f := fun r => r ^ (k - 1) * G (r • v))]
  simp

/-- **The radial transport equation of order `k ≥ 1`**: `DW(v) v + k W(v) = G(v)`. -/
theorem fderiv_radialAverage_apply_self (k : ℕ) (hk : 1 ≤ k) {G : (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (v : Fin n → ℝ) :
    fderiv ℝ (radialAverage k G) v v + k * radialAverage k G v = G v := by
  have hW := contDiff_radialAverage k hG
  -- `λ ↦ λᵏ W(λ v)` has derivative `DW(v) v + k W(v)` at `1` (product and chain rule)
  have hs : HasDerivAt (fun c : ℝ => c • v) ((1 : ℝ) • v) 1 := (hasDerivAt_id 1).smul_const v
  have hW1 : HasFDerivAt (radialAverage k G) (fderiv ℝ (radialAverage k G) v) ((1 : ℝ) • v) := by
    rw [one_smul]; exact ((hW.differentiable (by simp)) v).hasFDerivAt
  have hcomp := hW1.comp_hasDerivAt (1 : ℝ) hs
  rw [one_smul] at hcomp
  have h1 : HasDerivAt (fun c : ℝ => c ^ k * radialAverage k G (c • v))
      (k * 1 ^ (k - 1) * radialAverage k G ((1 : ℝ) • v) + 1 ^ k * fderiv ℝ (radialAverage k G) v v) 1 :=
    (hasDerivAt_pow k 1).mul hcomp
  -- and by the fundamental theorem of calculus its derivative is `G(v)`
  have hc : Continuous (fun r : ℝ => r ^ (k - 1) * G (r • v)) :=
    (continuous_pow _).mul (hG.continuous.comp (by fun_prop))
  have h2 : HasDerivAt (fun c : ℝ => c ^ k * radialAverage k G (c • v)) (1 ^ (k - 1) * G ((1 : ℝ) • v)) 1 := by
    have := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 1)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun c => radialAverage_smul k hk G c v)
  have := h1.unique h2
  simp only [one_pow, mul_one, one_mul, one_smul] at this
  linarith

/-- **The solution of the radial transport equation of order `k ≥ 1`** with the order-`0` coefficient: for `H(0) = 0`
and `U₀ = e^K`, the function `U = U₀ · W(F/U₀)` solves `DU(v) v + (k − H(v)) U(v) = F(v)`. -/
theorem fderiv_transportSolution_apply_self (k : ℕ) (hk : 1 ≤ k) {H F : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (h0 : H 0 = 0) (hF : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    let U₀ := fun w => Real.exp (eulerPrimitive H w)
    let U := fun w => U₀ w * radialAverage k (fun w' => F w' / U₀ w') w
    fderiv ℝ U v v + (k - H v) * U v = F v := by
  intro U₀ U
  have hK := contDiff_eulerPrimitive hH
  have hU₀ : ContDiff ℝ ∞ U₀ := Real.contDiff_exp.comp hK
  have hG : ContDiff ℝ ∞ (fun w' => F w' / U₀ w') :=
    hF.div hU₀ fun w => (Real.exp_pos _).ne'
  have hWs := contDiff_radialAverage k hG
  have hd0 := ((hU₀.differentiable (by simp)) v).hasFDerivAt
  have hdW := ((hWs.differentiable (by simp)) v).hasFDerivAt
  have hprod : HasFDerivAt (fun w => U₀ w * radialAverage k (fun w' => F w' / U₀ w') w)
      (U₀ v • fderiv ℝ (radialAverage k fun w' => F w' / U₀ w') v +
        radialAverage k (fun w' => F w' / U₀ w') v • fderiv ℝ U₀ v) v := hd0.mul hdW
  rw [show U = fun w => U₀ w * radialAverage k (fun w' => F w' / U₀ w') w from rfl, hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
  have e0 : fderiv ℝ U₀ v v = H v * U₀ v := fderiv_exp_eulerPrimitive_apply_self hH h0 v
  have eW := fderiv_radialAverage_apply_self k hk hG v
  rw [e0]
  have hpos : U₀ v ≠ 0 := (Real.exp_pos _).ne'
  have : fderiv ℝ (radialAverage k fun w' => F w' / U₀ w') v v =
      F v / U₀ v - k * radialAverage k (fun w' => F w' / U₀ w') v := by linarith
  rw [this]
  field_simp
  ring

section Parametric

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Smooth dependence on a parameter**: for `H : P × ℝⁿ → ℝ` smooth, `(p, v) ↦ K_{H(p, ·)}(v)` is smooth. -/
theorem contDiff_eulerPrimitive_param {H : P × (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun q : P × (Fin n → ℝ) => eulerPrimitive (fun v => H (q.1, v)) q.2) := by
  -- the partial derivative in `v`, as a jointly smooth function
  have hD : ContDiff ℝ ∞ (fun r : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
      fderiv ℝ (fun v => H (r.1.1, v)) r.1.2 r.2) := by
    have hpart : ∀ r : P × (Fin n → ℝ), fderiv ℝ (fun v => H (r.1, v)) r.2 =
        (fderiv ℝ H r).comp (ContinuousLinearMap.inr ℝ P (Fin n → ℝ)) := fun r => by
      have hd : HasFDerivAt H (fderiv ℝ H r) (r.1, r.2) := ((hH.differentiable (by simp)) r).hasFDerivAt
      have := hd.comp r.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) r.1 r.2)
      exact this.fderiv
    simp only [hpart]
    have h1 : ContDiff ℝ ∞ (fun r : (P × (Fin n → ℝ)) × (Fin n → ℝ) => fderiv ℝ H r.1) :=
      (hH.fderiv_right (m := ∞) (by exact_mod_cast le_top)).comp contDiff_fst
    exact (h1.clm_comp contDiff_const).clm_apply contDiff_snd
  unfold eulerPrimitive eulerKernel
  refine contDiff_infty_integral_unit (X := P × (Fin n → ℝ))
    (f := fun τ q => ∫ σ in (0 : ℝ)..1, fderiv ℝ (fun v => H (q.1, v)) ((σ * τ) • q.2) q.2) ?_
  refine contDiff_infty_integral_unit (X := ℝ × (P × (Fin n → ℝ)))
    (f := fun σ r => fderiv ℝ (fun v => H (r.2.1, v)) ((σ * r.1) • r.2.2) r.2.2) ?_
  have hm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × (P × (Fin n → ℝ))) =>
      (((z.2.2.1, (z.1 * z.2.1) • z.2.2.2)), z.2.2.2)) := by fun_prop
  exact hD.comp hm

/-- **Smooth dependence on a parameter** of the radial average: for `G : P × ℝⁿ → ℝ` smooth,
`(p, v) ↦ W_k(G(p, ·))(v)` is smooth. -/
theorem contDiff_radialAverage_param (k : ℕ) {G : P × (Fin n → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q : P × (Fin n → ℝ) => radialAverage k (fun v => G (q.1, v)) q.2) := by
  unfold radialAverage
  refine contDiff_infty_integral_unit (X := P × (Fin n → ℝ))
    (f := fun τ q => τ ^ (k - 1) * G (q.1, τ • q.2)) ?_
  have hm : ContDiff ℝ ∞ (fun z : ℝ × (P × (Fin n → ℝ)) => (z.2.1, z.1 • z.2.2)) := by fun_prop
  exact (contDiff_fst.pow _).mul (hG.comp hm)

end Parametric

end Lightlike
