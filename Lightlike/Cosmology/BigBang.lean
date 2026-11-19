import Lightlike.Cosmology.FLRW

/-!
# The big bang: finite age and divergent density (G1-025)

For a scale factor `a > 0` on an open interval `(t₁, t₂)` satisfying Friedmann's second equation with `Λ = 0` and the strong
energy condition `ρ + 3p ≥ 0`, so `a'' ≤ 0`, and expanding at a time `t₀ ∈ (t₁, t₂)` (`a'(t₀) > 0`):

* `bigBang_age_le`: the age is at most the Hubble time, `t₀ - t₁ ≤ a(t₀) / a'(t₀)`;
* `deriv_ge_of_strong_energy`: `a'(t) ≥ a'(t₀)` for `t ≤ t₀` (the expansion rate was larger in the past);
* `bigBang_density_tendsto_atTop`: with Friedmann's first equation and `k ≥ 0`, if `a (t) → 0` as `t ↓ t₁` then `ρ (t) → ∞`.

* `bigBang_age_lt_of_pos_density`: with Carroll's hypotheses `ρ > 0`, `p ≥ 0` (so `a'' < 0`) the age is strictly less than the
  Hubble time;
* `bigBang_density_tendsto_atTop_of_pos`: for every `k`, if `ρ(t₀) > 0` and `a → 0` then `ρ → ∞`; `milne_friedmann`: the Milne universe
  (`a = t`, `k = -1`, `ρ = 0`) shows that the positivity of the density is needed when `k < 0`.

**Limits.** Real-variable statements for functions of the time (no manifold): that the interval of the solution is
*maximal*, so that `a → 0` at its left end, is not proved (it needs the blow-up theory of the Friedmann equations, a
follow-up). Units `c = 1`.
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology

variable {a ρ p : ℝ → ℝ} {Gn t₁ t₂ t₀ : ℝ}

/-- The strong energy condition gives `a'' ≤ 0` for a positive scale factor. -/
theorem deriv2_nonpos_of_strong_energy (hG : 0 < Gn) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t)
    (hF : ∀ t ∈ Ioo t₁ t₂, SecondFriedmann a ρ p 0 Gn t) (hS : ∀ t ∈ Ioo t₁ t₂, 0 ≤ ρ t + 3 * p t) :
    ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0 := by
  intro t ht
  have h := hF t ht
  unfold SecondFriedmann at h
  have hat := hpos t ht
  have : deriv (deriv a) t = a t * (-(4 * Real.pi * Gn / 3) * (ρ t + 3 * p t) + 0 / 3) := by
    field_simp at h ⊢
    linarith
  rw [this]
  have : 0 ≤ 4 * Real.pi * Gn / 3 * (ρ t + 3 * p t) := by
    have := hS t ht; positivity
  nlinarith

/-- `a'` is nonincreasing on `(t₁, t₂)`, hence `a'(t) ≥ a'(t₀)` for `t ≤ t₀`. -/
theorem deriv_ge_of_strong_energy (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0) {t t₀ : ℝ} (ht : t ∈ Ioo t₁ t₂) (ht₀ : t₀ ∈ Ioo t₁ t₂)
    (hle : t ≤ t₀) : deriv a t₀ ≤ deriv a t := by
  have hd1 : ContDiffOn ℝ 1 (deriv a) (Ioo t₁ t₂) := hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hanti : AntitoneOn (deriv a) (Ioo t₁ t₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo t₁ t₂) hd1.continuousOn ?_ ?_
    · exact (hd1.differentiableOn (by norm_num)).mono interior_subset
    · rw [interior_Ioo]; exact hdd
  exact hanti ht ht₀ hle

/-- The tangent line at `t₀` bounds `a` from above in the past: `a(t) ≤ a(t₀) + a'(t₀)(t - t₀)` for `t ≤ t₀`. -/
theorem le_tangent_of_strong_energy (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0) {t t₀ : ℝ} (ht : t ∈ Ioo t₁ t₂) (ht₀ : t₀ ∈ Ioo t₁ t₂)
    (hle : t ≤ t₀) : a t ≤ a t₀ + deriv a t₀ * (t - t₀) := by
  have hdiff : ∀ s ∈ Ioo t₁ t₂, DifferentiableAt ℝ a s := fun s hs =>
    ((hC.differentiableOn (by norm_num)) s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
  have hsub : Icc t t₀ ⊆ Ioo t₁ t₂ := fun s hs => ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩
  set h : ℝ → ℝ := fun s => a s - a t₀ - deriv a t₀ * (s - t₀) with hh
  have hmono : MonotoneOn h (Icc t t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t t₀) ?_ ?_ ?_
    · intro s hs
      exact ((hdiff s (hsub hs)).sub_const _ |>.sub ((differentiableAt_id.sub_const t₀).const_mul _)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro s hs
      exact (((hdiff s (hsub (Ioo_subset_Icc_self hs))).sub_const _).sub
        ((differentiableAt_id.sub_const t₀).const_mul _)).differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs' : s ∈ Ioo t₁ t₂ := hsub (Ioo_subset_Icc_self hs)
      have hd : HasDerivAt h (deriv a s - deriv a t₀) s := by
        have := ((hdiff s hs').hasDerivAt.sub_const (a t₀)).sub (((hasDerivAt_id s).sub_const t₀).const_mul (deriv a t₀))
        convert this using 1
        · funext x; simp [hh]
        · simp
      rw [hd.deriv]
      have := deriv_ge_of_strong_energy hC hdd hs' ht₀ hs.2.le
      linarith
  have := hmono ⟨le_refl t, hle⟩ ⟨hle, le_refl t₀⟩ hle
  simp only [hh] at this
  linarith

/-- **The age of the universe is at most the Hubble time**: `t₀ - t₁ ≤ a(t₀) / a'(t₀)` for a positive, expanding scale factor
with `a'' ≤ 0` on `(t₁, t₂)`. -/
theorem bigBang_age_le (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂)) (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀) :
    t₀ - t₁ ≤ a t₀ / deriv a t₀ := by
  rw [le_div_iff₀ hH]
  by_contra hcon
  push Not at hcon
  -- a time `t` close to `t₁` with `a t ≤ 0`
  set t : ℝ := t₀ - (a t₀ / deriv a t₀ + (t₀ - t₁ - a t₀ / deriv a t₀) / 2) with ht
  have hlt : a t₀ / deriv a t₀ < t₀ - t₁ := by
    rwa [div_lt_iff₀ hH]
  have hmem : t ∈ Ioo t₁ t₂ := by
    constructor
    · simp only [ht]; linarith
    · simp only [ht]
      have : 0 < a t₀ / deriv a t₀ := div_pos (hpos t₀ ht₀) hH
      linarith [ht₀.2]
  have hle : t ≤ t₀ := by
    simp only [ht]
    have : 0 < a t₀ / deriv a t₀ := div_pos (hpos t₀ ht₀) hH
    linarith
  have h1 := le_tangent_of_strong_energy hC hdd hmem ht₀ hle
  have h2 := hpos t hmem
  have h3 : a t₀ + deriv a t₀ * (t - t₀) < 0 := by
    have : t - t₀ = -(a t₀ / deriv a t₀ + (t₀ - t₁ - a t₀ / deriv a t₀) / 2) := by simp only [ht]; ring
    rw [this]
    have e : deriv a t₀ * (a t₀ / deriv a t₀) = a t₀ := by field_simp
    nlinarith [mul_pos hH (show 0 < (t₀ - t₁ - a t₀ / deriv a t₀) / 2 by linarith)]
  linarith

/-- **The density diverges at the big bang** (`k ≥ 0`, `Λ = 0`): if `a → 0` at the left end of the interval then `ρ → ∞`. -/
theorem bigBang_density_tendsto_atTop {k : ℝ} (hG : 0 < Gn) (hk : 0 ≤ k) (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t)
    (hF : ∀ t ∈ Ioo t₁ t₂, FirstFriedmann a ρ k 0 Gn t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀)
    (hlim : Tendsto a (𝓝[>] t₁) (𝓝 0)) : Tendsto ρ (𝓝[>] t₁) atTop := by
  set c : ℝ := deriv a t₀ with hc
  set C : ℝ := 3 * c ^ 2 / (8 * Real.pi * Gn) with hC0
  have hCpos : 0 < C := by positivity
  have hlim' : Tendsto a (𝓝[>] t₁) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, by
      filter_upwards [Ioo_mem_nhdsGT (lt_of_lt_of_le ht₀.1 ht₀.2.le |>.trans_le le_rfl : t₁ < t₂)] with t ht using hpos t ht⟩
  have h1 : Tendsto (fun t => (a t)⁻¹ ^ 2) (𝓝[>] t₁) atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (tendsto_inv_nhdsGT_zero.comp hlim')
  have h2 : Tendsto (fun t => C * (a t)⁻¹ ^ 2) (𝓝[>] t₁) atTop := h1.const_mul_atTop hCpos
  refine tendsto_atTop_mono' _ ?_ h2
  filter_upwards [Ioo_mem_nhdsGT (show t₁ < t₀ from ht₀.1)] with t ht
  have hmem : t ∈ Ioo t₁ t₂ := ⟨ht.1, ht.2.trans ht₀.2⟩
  have hat := hpos t hmem
  have hge := deriv_ge_of_strong_energy hC hdd hmem ht₀ ht.2.le
  have h := hF t hmem
  unfold FirstFriedmann at h
  have hp : 0 < 8 * Real.pi * Gn / 3 := by positivity
  have hρ : ρ t = ((deriv a t / a t) ^ 2 + k / a t ^ 2) / (8 * Real.pi * Gn / 3) := by
    field_simp at h ⊢
    linarith
  rw [hρ, le_div_iff₀ hp]
  have hd : c ≤ deriv a t := hge
  have hq : c / a t ≤ deriv a t / a t := div_le_div_of_nonneg_right hd hat.le
  have hq2 : (c / a t) ^ 2 ≤ (deriv a t / a t) ^ 2 := by
    have : 0 ≤ c / a t := div_nonneg hH.le hat.le
    nlinarith
  have hk' : 0 ≤ k / a t ^ 2 := by positivity
  have e : C * (a t)⁻¹ ^ 2 * (8 * Real.pi * Gn / 3) = (c / a t) ^ 2 := by
    simp only [hC0]; field_simp
  rw [e]
  linarith

/-- With `ρ > 0` and `p ≥ 0` (Carroll's hypotheses), Friedmann's second equation with `Λ = 0` gives `a'' < 0`. -/
theorem deriv2_neg_of_pos_density (hG : 0 < Gn) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t)
    (hF : ∀ t ∈ Ioo t₁ t₂, SecondFriedmann a ρ p 0 Gn t) (hρ : ∀ t ∈ Ioo t₁ t₂, 0 < ρ t)
    (hp : ∀ t ∈ Ioo t₁ t₂, 0 ≤ p t) : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t < 0 := by
  intro t ht
  have h := hF t ht
  unfold SecondFriedmann at h
  have hat := hpos t ht
  have : deriv (deriv a) t = a t * (-(4 * Real.pi * Gn / 3) * (ρ t + 3 * p t) + 0 / 3) := by
    field_simp at h ⊢
    linarith
  rw [this]
  have : 0 < 4 * Real.pi * Gn / 3 * (ρ t + 3 * p t) := by
    have := hρ t ht; have := hp t ht; positivity
  nlinarith

/-- With `a'' < 0`, the tangent line at `t₀` lies strictly above `a` in the past: `a(s) < a(t₀) + a'(t₀)(s - t₀)` for `s < t₀`. -/
theorem lt_tangent_of_deriv2_neg (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t < 0) {s t₀ : ℝ} (hs : s ∈ Ioo t₁ t₂) (ht₀ : t₀ ∈ Ioo t₁ t₂)
    (hlt : s < t₀) : a s < a t₀ + deriv a t₀ * (s - t₀) := by
  have hd1 : ContDiffOn ℝ 1 (deriv a) (Ioo t₁ t₂) := hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hanti : StrictAntiOn (deriv a) (Ioo t₁ t₂) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo t₁ t₂) hd1.continuousOn ?_
    rw [interior_Ioo]; exact hdd
  have hdiff : ∀ x ∈ Ioo t₁ t₂, DifferentiableAt ℝ a x := fun x hx =>
    ((hC.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hsub : Icc s t₀ ⊆ Ioo t₁ t₂ := fun x hx => ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 ht₀.2⟩
  set h : ℝ → ℝ := fun x => a x - a t₀ - deriv a t₀ * (x - t₀) with hh
  have hmono : StrictMonoOn h (Icc s t₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc s t₀) ?_ ?_
    · intro x hx
      exact ((hdiff x (hsub hx)).sub_const _ |>.sub ((differentiableAt_id.sub_const t₀).const_mul _)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Ioo t₁ t₂ := hsub (Ioo_subset_Icc_self hx)
      have hd : HasDerivAt h (deriv a x - deriv a t₀) x := by
        have := ((hdiff x hx').hasDerivAt.sub_const (a t₀)).sub (((hasDerivAt_id x).sub_const t₀).const_mul (deriv a t₀))
        convert this using 1
        · funext y; simp [hh]
        · simp
      rw [hd.deriv]
      have := hanti hx' ht₀ hx.2
      linarith
  have := hmono ⟨le_refl s, hlt.le⟩ ⟨hlt.le, le_refl t₀⟩ hlt
  simp only [hh] at this
  linarith

/-- **The age is strictly less than the Hubble time** when `a'' < 0`: `t₀ - t₁ < a(t₀) / a'(t₀)` (Carroll: "the universe must be
somewhat younger than that", for `ρ > 0`, `p ≥ 0`). -/
theorem bigBang_age_lt (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂)) (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t < 0)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀) :
    t₀ - t₁ < a t₀ / deriv a t₀ := by
  set s : ℝ := (t₁ + t₀) / 2 with hsdef
  have hs : s ∈ Ioo t₁ t₂ := ⟨by simp only [hsdef]; linarith [ht₀.1], by simp only [hsdef]; linarith [ht₀.1, ht₀.2]⟩
  have hst : s < t₀ := by simp only [hsdef]; linarith [ht₀.1]
  have hdd' : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0 := fun t ht => (hdd t ht).le
  have hd1 : ContDiffOn ℝ 1 (deriv a) (Ioo t₁ t₂) := hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hanti : StrictAntiOn (deriv a) (Ioo t₁ t₂) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo t₁ t₂) hd1.continuousOn ?_
    rw [interior_Ioo]; exact hdd
  have hds : deriv a t₀ < deriv a s := hanti hs ht₀ hst
  have hHs : 0 < deriv a s := hH.trans hds
  -- the bound at `s`
  have hage := bigBang_age_le hC hdd' hpos hs hHs
  -- the strict tangent inequality at `t₀`
  have htan := lt_tangent_of_deriv2_neg hC hdd hs ht₀ hst
  have has := hpos s hs
  -- `a(t₀)/a'(t₀) > (t₀ - s) + a(s)/a'(t₀) > (t₀ - s) + a(s)/a'(s)`
  have h1 : (t₀ - s) + a s / deriv a t₀ < a t₀ / deriv a t₀ := by
    rw [← sub_pos]
    have : a t₀ / deriv a t₀ - ((t₀ - s) + a s / deriv a t₀) = (a t₀ + deriv a t₀ * (s - t₀) - a s) / deriv a t₀ := by
      field_simp; ring
    rw [this]; exact div_pos (by linarith) hH
  have h2 : a s / deriv a s < a s / deriv a t₀ := div_lt_div_of_pos_left has hH hds
  linarith

/-- **Carroll's statement of the age** (`Λ = 0`, `ρ > 0`, `p ≥ 0`): the age is strictly less than the Hubble time. -/
theorem bigBang_age_lt_of_pos_density (hG : 0 < Gn) (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t) (hF : ∀ t ∈ Ioo t₁ t₂, SecondFriedmann a ρ p 0 Gn t)
    (hρ : ∀ t ∈ Ioo t₁ t₂, 0 < ρ t) (hp : ∀ t ∈ Ioo t₁ t₂, 0 ≤ p t) (ht₀ : t₀ ∈ Ioo t₁ t₂)
    (hH : 0 < deriv a t₀) : t₀ - t₁ < a t₀ / deriv a t₀ :=
  bigBang_age_lt hC (deriv2_neg_of_pos_density hG hpos hF hρ hp) hpos ht₀ hH

/-- **The density diverges at the big bang for every `k`** (`Λ = 0`), when the density is positive at one expanding time `t₀`:
if `a → 0` at the left end of the interval then `ρ → ∞` (`ρ(t) ≥ ρ(t₀) a(t₀)² / a(t)²` for `t ≤ t₀`). -/
theorem bigBang_density_tendsto_atTop_of_pos {k : ℝ} (hG : 0 < Gn) (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hdd : ∀ t ∈ Ioo t₁ t₂, deriv (deriv a) t ≤ 0) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t)
    (hF : ∀ t ∈ Ioo t₁ t₂, FirstFriedmann a ρ k 0 Gn t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀)
    (hρ₀ : 0 < ρ t₀) (hlim : Tendsto a (𝓝[>] t₁) (𝓝 0)) : Tendsto ρ (𝓝[>] t₁) atTop := by
  set D : ℝ := ρ t₀ * a t₀ ^ 2 with hD
  have hDpos : 0 < D := by have := hpos t₀ ht₀; positivity
  have hp : 0 < 8 * Real.pi * Gn / 3 := by positivity
  have hρeq : ∀ t ∈ Ioo t₁ t₂, ρ t * a t ^ 2 = (deriv a t ^ 2 + k) / (8 * Real.pi * Gn / 3) := by
    intro t ht
    have h := hF t ht
    have hat := hpos t ht
    unfold FirstFriedmann at h
    rw [eq_div_iff hp.ne']
    field_simp at h
    linarith
  have hlim' : Tendsto a (𝓝[>] t₁) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, by
      filter_upwards [Ioo_mem_nhdsGT (lt_of_lt_of_le ht₀.1 ht₀.2.le |>.trans_le le_rfl : t₁ < t₂)] with t ht using hpos t ht⟩
  have h1 : Tendsto (fun t => (a t)⁻¹ ^ 2) (𝓝[>] t₁) atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (tendsto_inv_nhdsGT_zero.comp hlim')
  have h2 : Tendsto (fun t => D * (a t)⁻¹ ^ 2) (𝓝[>] t₁) atTop := h1.const_mul_atTop hDpos
  refine tendsto_atTop_mono' _ ?_ h2
  filter_upwards [Ioo_mem_nhdsGT (show t₁ < t₀ from ht₀.1)] with t ht
  have hmem : t ∈ Ioo t₁ t₂ := ⟨ht.1, ht.2.trans ht₀.2⟩
  have hat := hpos t hmem
  have hge : deriv a t₀ ≤ deriv a t := deriv_ge_of_strong_energy hC hdd hmem ht₀ ht.2.le
  have hsq : deriv a t₀ ^ 2 ≤ deriv a t ^ 2 := by nlinarith
  have e0 := hρeq t₀ ht₀
  have e1 := hρeq t hmem
  have hle : D ≤ ρ t * a t ^ 2 := by
    rw [hD, e0, e1]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  have ha2 : 0 < a t ^ 2 := by positivity
  calc D * (a t)⁻¹ ^ 2 = D / a t ^ 2 := by rw [inv_pow, div_eq_mul_inv]
    _ ≤ ρ t * a t ^ 2 / a t ^ 2 := div_le_div_of_nonneg_right hle ha2.le
    _ = ρ t := by field_simp

/-- **The positivity of the density is needed for `k < 0`** (trust check): the Milne universe `a(t) = t`, `k = -1`, `ρ = p = 0`
solves Friedmann's equations with `Λ = 0` on `(0, ∞)`, `a → 0` as `t ↓ 0`, and the density stays zero. -/
theorem milne_friedmann (Gn : ℝ) :
    (∀ t ∈ Ioi (0 : ℝ), FirstFriedmann (fun t => t) (fun _ => 0) (-1) 0 Gn t ∧
      SecondFriedmann (fun t => t) (fun _ => 0) (fun _ => 0) 0 Gn t) ∧
    Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) ∧ ¬ Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) atTop := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, ?_⟩
  · have ht0 : t ≠ 0 := (ne_of_gt ht)
    unfold FirstFriedmann
    simp only [deriv_id'', mul_zero, zero_div, add_zero]
    field_simp
    ring
  · unfold SecondFriedmann
    simp
  · intro h
    have := h.eventually (eventually_gt_atTop 0)
    obtain ⟨x, hx⟩ := this.exists
    exact lt_irrefl _ hx

end Cosmology
end Lightlike
