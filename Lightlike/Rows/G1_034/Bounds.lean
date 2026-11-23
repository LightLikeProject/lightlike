module

public import Mathlib
public import Lightlike.Rows.G1_034.Basic

/-!
# The freeze-out equation: a priori bounds

Row G1-034 (milestone CO7).  Generic comparison lemmas for a function `Y` with right derivative
`d` on `[x₀, ∞)`, and their use on the freeze-out equation:

* `nonneg_of_deriv`: if `d ≥ 0` wherever `Y < 0`, then `Y x₀ ≥ 0` propagates.
* `antitoneOn_add_div`: if `d x ≤ c / x²` then `Y x + c / x` is antitone.
* `exists_tendsto_of_antitoneOn`: such a `Y`, if `≥ 0`, has a finite limit.
* `Bsol`: the explicit solution for `Y_eq = 0`, `Y₀ / (1 + λ Y₀ (1/x₀ - 1/x))`.
* `IsSol.bsol_le`: a nonnegative solution is `≥ Bsol`.
-/

@[expose] public section

namespace Lightlike.Rows.G1_034

open Set Filter Topology

/-- Sign propagation: if `Y x₀ ≥ 0` and `d x ≥ 0` wherever `Y x < 0`, then `Y ≥ 0` on `[x₀, ∞)`. -/
lemma nonneg_of_deriv {Y d : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousOn Y (Ici x₀)) (h0 : 0 ≤ Y x₀)
    (hd : ∀ x, x₀ ≤ x → HasDerivWithinAt Y (d x) (Ici x₀) x)
    (hneg : ∀ x, x₀ ≤ x → Y x < 0 → 0 ≤ d x) : ∀ x, x₀ ≤ x → 0 ≤ Y x := by
  intro x₁ hx₁
  by_contra hlt
  replace hlt := not_le.1 hlt
  set S : Set ℝ := Icc x₀ x₁ ∩ Y ⁻¹' Ici 0 with hS
  have hSc : IsClosed S :=
    (hc.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hx₀S : x₀ ∈ S := ⟨⟨le_rfl, hx₁⟩, h0⟩
  have hbdd : BddAbove S := ⟨x₁, fun x hx => hx.1.2⟩
  have hs : sSup S ∈ S := hSc.csSup_mem ⟨x₀, hx₀S⟩ hbdd
  set s := sSup S with hsdef
  have hsx₁ : s ≤ x₁ := hs.1.2
  have hx₀s : x₀ ≤ s := hs.1.1
  have hYs : 0 ≤ Y s := hs.2
  have hs1 : s < x₁ := by
    rcases hsx₁.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h] at hYs
      linarith
  have hneg' : ∀ y ∈ Ioc s x₁, Y y < 0 := by
    intro y hy
    by_contra hy0
    replace hy0 := not_lt.1 hy0
    have : y ≤ s := le_csSup hbdd ⟨⟨hx₀s.trans hy.1.le, hy.2⟩, hy0⟩
    exact absurd hy.1 (not_lt.2 this)
  have hHD : ∀ x ∈ Ioo s x₁, HasDerivAt Y (d x) x := fun x hx =>
    (hd x (hx₀s.trans hx.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt hx₀s hx.1))
  have hmono : MonotoneOn Y (Icc s x₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s x₁)
      (hc.mono fun x hx => hx₀s.trans hx.1)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hHD x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hHD x hx).deriv]
      exact hneg x (hx₀s.trans hx.1.le) (hneg' x ⟨hx.1, hx.2.le⟩)
  have := hmono (left_mem_Icc.2 hs1.le) (right_mem_Icc.2 hs1.le) hs1.le
  linarith

/-- If `d x ≤ c / x²` then `Y x + c / x` is antitone on `[x₀, ∞)`. -/
lemma antitoneOn_add_div {Y d : ℝ → ℝ} {x₀ c : ℝ} (hx₀ : 0 < x₀) (hc : ContinuousOn Y (Ici x₀))
    (hd : ∀ x, x₀ ≤ x → HasDerivWithinAt Y (d x) (Ici x₀) x)
    (hle : ∀ x, x₀ ≤ x → d x ≤ c / x ^ 2) : AntitoneOn (fun x => Y x + c / x) (Ici x₀) := by
  have hD : ∀ x, x₀ ≤ x → HasDerivWithinAt (fun x => Y x + c / x)
      (d x + (0 * x - c * 1) / x ^ 2) (Ici x₀) x := fun x hx =>
    (hd x hx).add
      (((hasDerivAt_const x c).div (hasDerivAt_id' x) (lt_of_lt_of_le hx₀ hx).ne').hasDerivWithinAt)
  apply antitoneOn_of_deriv_nonpos (convex_Ici x₀)
  · exact hc.add (continuousOn_const.div continuousOn_id
      fun x hx => (lt_of_lt_of_le hx₀ hx).ne')
  · intro x hx
    rw [interior_Ici] at hx
    exact ((hD x hx.le).hasDerivAt (Ici_mem_nhds hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [((hD x hx.le).hasDerivAt (Ici_mem_nhds hx)).deriv]
    have h1 := hle x hx.le
    have h2 : (0 * x - c * 1) / x ^ 2 = -(c / x ^ 2) := by ring
    linarith

/-- A nonnegative `Y` with `Y + c/x` antitone (`c ≥ 0`) has a finite limit. -/
lemma exists_tendsto_of_antitoneOn {Y : ℝ → ℝ} {x₀ c : ℝ} (hx₀ : 0 < x₀) (hc : 0 ≤ c)
    (hG : AntitoneOn (fun x => Y x + c / x) (Ici x₀)) (hY : ∀ x, x₀ ≤ x → 0 ≤ Y x) :
    ∃ L, Tendsto Y atTop (𝓝 L) := by
  set G : ℝ → ℝ := fun x => Y (max x x₀) + c / max x x₀ with hGdef
  have hanti : Antitone G := fun a b hab =>
    hG (le_max_right _ _) (le_max_right _ _) (max_le_max hab le_rfl)
  have hbdd : BddBelow (Set.range G) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hpos : 0 < max x x₀ := lt_of_lt_of_le hx₀ (le_max_right _ _)
    have := hY (max x x₀) (le_max_right _ _)
    simp only [hGdef]
    positivity
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hinv : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine ⟨(⨅ i, G i) - 0, (hlim.sub hinv).congr' ?_⟩
  filter_upwards [eventually_ge_atTop x₀] with x hx
  simp only [hGdef, max_eq_left hx]
  ring

/-- The explicit solution for `Y_eq = 0`: `Y₀ / (1 + λ Y₀ (1/x₀ - 1/x))`. -/
noncomputable def Bsol (lam x₀ Y₀ : ℝ) (x : ℝ) : ℝ := Y₀ / (1 + lam * Y₀ * (x₀⁻¹ - x⁻¹))

lemma one_le_denom {lam x₀ Y₀ x : ℝ} (hlam : 0 ≤ lam) (hx₀ : 0 < x₀) (hY₀ : 0 ≤ Y₀)
    (hx : x₀ ≤ x) : 1 ≤ 1 + lam * Y₀ * (x₀⁻¹ - x⁻¹) := by
  have : x⁻¹ ≤ x₀⁻¹ := inv_anti₀ hx₀ hx
  have : 0 ≤ lam * Y₀ * (x₀⁻¹ - x⁻¹) := mul_nonneg (mul_nonneg hlam hY₀) (by linarith)
  linarith

/-- `Bsol` solves `Y' = -(λ/x²) Y²`. -/
lemma hasDerivAt_Bsol {lam x₀ Y₀ x : ℝ} (hlam : 0 ≤ lam) (hx₀ : 0 < x₀) (hY₀ : 0 ≤ Y₀)
    (hx : x₀ ≤ x) : HasDerivAt (Bsol lam x₀ Y₀) (-(lam / x ^ 2) * Bsol lam x₀ Y₀ x ^ 2) x := by
  have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
  have hD := one_le_denom hlam hx₀ hY₀ hx
  have hDpos : (1 + lam * Y₀ * (x₀⁻¹ - x⁻¹)) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => 1 + lam * Y₀ * (x₀⁻¹ - y⁻¹))
      (lam * Y₀ * (0 - -(x ^ 2)⁻¹)) x :=
    (((hasDerivAt_const x x₀⁻¹).sub (hasDerivAt_inv hx0.ne')).const_mul (lam * Y₀)).const_add 1
  have h2 := (hasDerivAt_const x Y₀).div h1 hDpos
  refine (show HasDerivAt (Bsol lam x₀ Y₀) _ x from h2).congr_deriv ?_
  simp only [Bsol]
  field_simp
  ring

lemma continuousOn_Bsol {lam x₀ Y₀ : ℝ} (hlam : 0 ≤ lam) (hx₀ : 0 < x₀) (hY₀ : 0 ≤ Y₀) :
    ContinuousOn (Bsol lam x₀ Y₀) (Ici x₀) := fun _ hx =>
  (hasDerivAt_Bsol hlam hx₀ hY₀ hx).continuousAt.continuousWithinAt

/-- A nonnegative solution lies above the explicit solution `Bsol` (the `Y_eq = 0` solution). -/
theorem IsSol.bsol_le {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ : ℝ} (hx₀ : 0 < x₀)
    (hY₀ : 0 ≤ Y₀) {Y : ℝ → ℝ} (h : IsSol lam e x₀ Y₀ Y) (hnn : ∀ x, x₀ ≤ x → 0 ≤ Y x) :
    ∀ x, x₀ ≤ x → Bsol lam x₀ Y₀ x ≤ Y x := by
  have key := nonneg_of_deriv (Y := fun x => Y x - Bsol lam x₀ Y₀ x)
    (d := fun x => rhs lam e x (Y x) - -(lam / x ^ 2) * Bsol lam x₀ Y₀ x ^ 2)
    (x₀ := x₀) (h.continuousOn.sub (continuousOn_Bsol hlam hx₀ hY₀))
    (by simp [Bsol, h.1])
    (fun x hx => (h.2 x hx).sub (hasDerivAt_Bsol hlam hx₀ hY₀ hx).hasDerivWithinAt)
    (fun x hx hneg => by
      have hB : Y x < Bsol lam x₀ Y₀ x := by simpa using hneg
      have hY := hnn x hx
      have h1 : 0 ≤ Bsol lam x₀ Y₀ x ^ 2 - Y x ^ 2 + e x ^ 2 := by
        nlinarith [sq_nonneg (e x)]
      have h2 : rhs lam e x (Y x) - -(lam / x ^ 2) * Bsol lam x₀ Y₀ x ^ 2
          = lam / x ^ 2 * (Bsol lam x₀ Y₀ x ^ 2 - Y x ^ 2 + e x ^ 2) := by
        simp only [rhs]; ring
      rw [h2]
      have : 0 < x := lt_of_lt_of_le hx₀ hx
      positivity)
  intro x hx
  have := key x hx
  simpa using this

end Lightlike.Rows.G1_034
