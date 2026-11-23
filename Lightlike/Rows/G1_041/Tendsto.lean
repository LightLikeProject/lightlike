import Lightlike.Rows.G1_041.NoHair

/-!
# Cosmic no-hair for Bianchi models: the limits (G1-041)

Qualitative form of `Lightlike.Cosmology.Bianchi.no_hair_bounds`: as `t → ∞` the Hubble rate tends to the
de Sitter rate `√(Λ/3)`, and the density, the shear and the spatial curvature tend to `0`.
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology
namespace Bianchi

variable {Λ t₀ : ℝ} {H ρ p σ2 R : ℝ → ℝ}

/-- The decay factor `e^{-2L(t - t₀)}` tends to `0` when `L > 0`. -/
lemma tendsto_decay {L : ℝ} (hL : 0 < L) (t₀ : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * L * (t - t₀)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t - t₀) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have h2 : Tendsto (fun t : ℝ => 2 * L * (t - t₀)) atTop atTop :=
    h1.const_mul_atTop (by positivity)
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)

/-- **Cosmic no-hair for the Bianchi models other than type IX, limit form** (Wald 1983; Rendall 2005,
Section 4). Under the hypotheses of `no_hair_bounds`, `H(t) → √(Λ/3)` and `ρ, σ², R → 0` as `t → ∞`. -/
theorem no_hair_tendsto (hΛ : 0 < Λ) (hs : IsSolution Λ t₀ H ρ p σ2 R)
    (ha : IsAdmissible t₀ ρ p σ2 R) (h0 : 0 < H t₀) :
    Tendsto H atTop (𝓝 (deSitterRate Λ)) ∧ Tendsto ρ atTop (𝓝 0) ∧
    Tendsto σ2 atTop (𝓝 0) ∧ Tendsto R atTop (𝓝 0) := by
  set L := deSitterRate Λ with hLdef
  have hL : 0 < L := deSitterRate_pos hΛ
  have hE := tendsto_decay hL t₀
  have hev : ∀ᶠ t in atTop, t₀ ≤ t := eventually_ge_atTop t₀
  have hb := fun t (ht : t₀ ≤ t) => no_hair_bounds hΛ hs ha h0 ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hup : Tendsto (fun t : ℝ => L + (H t₀ - L) * Real.exp (-(2 * L * (t - t₀)))) atTop
        (𝓝 (L + (H t₀ - L) * 0)) := (hE.const_mul _).const_add _
    rw [mul_zero, add_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev.mono fun t ht => (hb t ht).1) (hev.mono fun t ht => (hb t ht).2.1)
  · have hup : Tendsto (fun t : ℝ => 3 * (H t₀ ^ 2 - L ^ 2) * Real.exp (-(2 * L * (t - t₀)))) atTop
        (𝓝 (3 * (H t₀ ^ 2 - L ^ 2) * 0)) := hE.const_mul _
    rw [mul_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev.mono fun t ht => ha.rho_nonneg t ht) (hev.mono fun t ht => (hb t ht).2.2.1)
  · have hup : Tendsto (fun t : ℝ => 3 * (H t₀ ^ 2 - L ^ 2) * Real.exp (-(2 * L * (t - t₀)))) atTop
        (𝓝 (3 * (H t₀ ^ 2 - L ^ 2) * 0)) := hE.const_mul _
    rw [mul_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev.mono fun t ht => ha.shear_nonneg t ht) (hev.mono fun t ht => (hb t ht).2.2.2.1)
  · have hup : Tendsto (fun t : ℝ => 2 * (3 * (H t₀ ^ 2 - L ^ 2) * Real.exp (-(2 * L * (t - t₀)))))
        atTop (𝓝 (2 * (3 * (H t₀ ^ 2 - L ^ 2) * 0))) := (hE.const_mul _).const_mul _
    rw [mul_zero, mul_zero] at hup
    have hneg : Tendsto (fun t => -R t) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (hev.mono fun t ht => neg_nonneg.2 (ha.curvature_nonpos t ht))
        (hev.mono fun t ht => (hb t ht).2.2.2.2)
    simpa using hneg.neg

end Bianchi
end Cosmology
end Lightlike
