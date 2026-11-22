module

public import Lightlike.Cosmology.FLRW

/-!
# The effective Friedmann equation of loop quantum cosmology

The effective equation `H² = (8πG/3) ρ (1 − ρ/ρ_c)` of the flat FLRW model in loop quantum
cosmology (Ashtekar–Pawlowski–Singh 2006, `aps-2006`), units `c = ħ = 1`, so `ℓ_P² = G` and
the Planck density is `ρ_Pl = G⁻²`.

* `LQCFriedmann a ρ ρc G t` : the effective Friedmann equation at the time `t`.
* `areaGap G γ = 4√3 π γ G` : the area gap `Δ = 4√3 π γ ℓ_P²` of loop quantum gravity.
* `critDensity G γ Δ = 3 / (8π G γ² Δ)` : the critical density `ρ_c`.
* `critDensity_areaGap` : `ρ_c = √3 / (32 π² γ³) · ρ_Pl`.
* `effHubble`, `effDensity` : the Hubble rate `sin (2λb) / (2γλ)` and the density
  `ρ_c sin² (λ b)` of the effective Hamiltonian constraint, in the connection variable `b`
  with `λ² = Δ`.
* `effHubble_sq` : `H² = (8πG/3) ρ (1 − ρ/ρ_c)` for these.
* `LQCFriedmann.density_le`, `LQCFriedmann.hubble_eq_zero_iff` : the density is bounded by
  `ρ_c` and the expansion stops exactly at `ρ = ρ_c` (or `ρ = 0`).

**References.** A. Ashtekar, T. Pawlowski, P. Singh, *Quantum nature of the big bang: improved
dynamics* (`aps-2006`).
-/

@[expose] public section

noncomputable section

namespace Lightlike

namespace Cosmology

namespace LQC

/-- The effective Friedmann equation of loop quantum cosmology at time `t`,
`(a'/a)² = (8πG/3) ρ (1 − ρ/ρ_c)`, units `c = 1`. -/
def LQCFriedmann (a ρ : ℝ → ℝ) (ρc Gn : ℝ) (t : ℝ) : Prop :=
  (deriv a t / a t) ^ 2 = 8 * Real.pi * Gn / 3 * ρ t * (1 - ρ t / ρc)

/-- The area gap `Δ = 4√3 π γ ℓ_P²` with `ℓ_P² = G` (`ħ = c = 1`), for the Barbero–Immirzi
parameter `γ`. -/
def areaGap (Gn γ : ℝ) : ℝ := 4 * Real.sqrt 3 * Real.pi * γ * Gn

/-- The critical density `ρ_c = 3 / (8π G γ² Δ)` of the effective dynamics with area parameter
`Δ = λ²`. -/
def critDensity (Gn γ Δ : ℝ) : ℝ := 3 / (8 * Real.pi * Gn * γ ^ 2 * Δ)

/-- The Hubble rate `H = sin (2λb) / (2γλ)` of the effective Hamiltonian constraint, in the
connection variable `b` and the improved-dynamics parameter `λ`. -/
def effHubble (γ lam b : ℝ) : ℝ := Real.sin (2 * lam * b) / (2 * γ * lam)

/-- The energy density `ρ = ρ_c sin² (λ b)` fixed by the effective Hamiltonian constraint,
`ρ_c = 3 / (8π G γ² λ²)`. -/
def effDensity (Gn γ lam b : ℝ) : ℝ :=
  critDensity Gn γ (lam ^ 2) * Real.sin (lam * b) ^ 2

/-- **The critical density in Planck units**: with the area gap `Δ = 4√3 π γ ℓ_P²`,
`ρ_c = √3 / (32 π² γ³) · ρ_Pl`, where `ρ_Pl = G⁻²`. -/
theorem critDensity_areaGap {Gn γ : ℝ} (hG : Gn ≠ 0) (hγ : γ ≠ 0) :
    critDensity Gn γ (areaGap Gn γ) = Real.sqrt 3 / (32 * Real.pi ^ 2 * γ ^ 3) * (Gn ^ 2)⁻¹ := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  unfold critDensity areaGap
  field_simp
  nlinarith [hs]

/-- **The effective Friedmann equation from the effective Hamiltonian constraint**: for
`H = sin (2λb)/(2γλ)` and `ρ = ρ_c sin² (λb)` with `ρ_c = 3/(8πGγ²λ²)`,
`H² = (8πG/3) ρ (1 − ρ/ρ_c)`. -/
theorem effHubble_sq {Gn γ lam : ℝ} (hG : Gn ≠ 0) (hγ : γ ≠ 0) (hl : lam ≠ 0) (b : ℝ) :
    effHubble γ lam b ^ 2 =
      8 * Real.pi * Gn / 3 * effDensity Gn γ lam b *
        (1 - effDensity Gn γ lam b / critDensity Gn γ (lam ^ 2)) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc : critDensity Gn γ (lam ^ 2) ≠ 0 := by
    unfold critDensity; positivity
  unfold effDensity
  rw [mul_div_cancel_left₀ _ hc]
  have h2 : Real.sin (2 * lam * b) = 2 * Real.sin (lam * b) * Real.cos (lam * b) := by
    rw [show 2 * lam * b = 2 * (lam * b) by ring, Real.sin_two_mul]
  have h1 : 1 - Real.sin (lam * b) ^ 2 = Real.cos (lam * b) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (lam * b)]
  rw [h1]
  unfold effHubble critDensity
  rw [h2]
  field_simp

/-- The density of the effective dynamics never exceeds `ρ_c`. -/
theorem effDensity_le {Gn γ lam : ℝ} (hG : 0 < Gn) (hγ : γ ≠ 0) (hl : lam ≠ 0) (b : ℝ) :
    effDensity Gn γ lam b ≤ critDensity Gn γ (lam ^ 2) := by
  have hc : 0 < critDensity Gn γ (lam ^ 2) := by
    unfold critDensity; positivity
  unfold effDensity
  nlinarith [Real.sin_sq_le_one (lam * b)]

/-- **No density above `ρ_c`**: if the effective Friedmann equation holds at `t` with
`ρ_c > 0`, `G > 0`, `a t ≠ 0` and `ρ t > 0`, then `ρ t ≤ ρ_c`. -/
theorem LQCFriedmann.density_le {a ρ : ℝ → ℝ} {ρc Gn t : ℝ} (h : LQCFriedmann a ρ ρc Gn t)
    (hG : 0 < Gn) (hc : 0 < ρc) (hρ : 0 < ρ t) : ρ t ≤ ρc := by
  unfold LQCFriedmann at h
  have hsq : 0 ≤ (deriv a t / a t) ^ 2 := sq_nonneg _
  rw [h] at hsq
  have hpos : 0 < 8 * Real.pi * Gn / 3 * ρ t := by positivity
  have h1 : 0 ≤ 1 - ρ t / ρc := nonneg_of_mul_nonneg_right hsq hpos
  have : ρ t / ρc ≤ 1 := by linarith
  rwa [div_le_one hc] at this

/-- **The bounce**: where the effective Friedmann equation holds (`G > 0`, `ρ_c > 0`), the
expansion rate vanishes exactly when `ρ = 0` or `ρ = ρ_c`. -/
theorem LQCFriedmann.hubble_eq_zero_iff {a ρ : ℝ → ℝ} {ρc Gn t : ℝ}
    (h : LQCFriedmann a ρ ρc Gn t) (hG : 0 < Gn) (hc : 0 < ρc) :
    deriv a t / a t = 0 ↔ ρ t = 0 ∨ ρ t = ρc := by
  unfold LQCFriedmann at h
  have hπ : 0 < 8 * Real.pi * Gn / 3 := by positivity
  rw [← sq_eq_zero_iff (a := deriv a t / a t), h]
  constructor
  · intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hπ.ne'
      · exact Or.inl h2
    · right
      have : ρ t / ρc = 1 := by linarith
      rwa [div_eq_one_iff_eq hc.ne'] at this
  · rintro (h0 | h0)
    · simp [h0]
    · rw [h0, div_self hc.ne']; simp

end LQC

end Cosmology

end Lightlike
