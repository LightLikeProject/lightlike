import Lightlike.Upstream.GeodesicExpansion.DistUpper
import Mathlib

/-!
# The expansion of the squared distance to fifth order

Combining the lower bound (`DistLower`) and the upper bound (`DistUpper`) on `d(x, x + w)²`.

## Main declarations

* `IsRiemMetric.dist_sq_expansion`: for a Riemannian coordinate metric `g` on `U` and compact
  `K ⊆ U`, `|d(x, x + w)² - F_x(w)| ≤ C ‖w‖⁵` uniformly for `x ∈ K` and small `w`
* `midJet`: the jet of the squared distance about the midpoint
* `abs_midComb_le`, `abs_jetPoly_mid_le`: the Taylor computation re-centring `F` at the midpoint
-/

open Matrix Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The expansion of the squared distance for nearby points.** For a Riemannian coordinate
metric `g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `x ∈ K` and
`‖w‖ ≤ r`,
`|d(x, x + w)² - F_x(w)| ≤ C ‖w‖⁵`, with
`F_x(w) = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` at `x`
(`distJet`). -/
theorem IsRiemMetric.dist_sq_expansion (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      |chartDist g U x (x + w) ^ 2 - distJet g x w| ≤ C * ‖w‖ ^ 5 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have h₀ := hJ x₀ hx₀
  have hB1 := h₀.one_le
  have hB : 0 < B := by linarith
  have hl := h₀.l_pos
  have hδ := h₀.δ_pos
  set A := 2 * B ^ 3 / l + 1 with hAdef
  have hA : 1 ≤ A := by have : 0 ≤ 2 * B ^ 3 / l := by positivity
                        linarith
  have hA0 : 0 < A := by linarith
  have hAl : 2 * B ^ 3 ≤ l * A := by
    have : l * A = 2 * B ^ 3 + l := by rw [hAdef]; field_simp
    linarith
  set κ := calibConst B l
  have hκ : 0 ≤ κ := calibConst_nonneg hB.le hl
  refine ⟨4 * κ * A ^ 3 * B ^ 3 + 51 * B ^ 6,
    min (min (δ / A) (l / (2 * B ^ 3 * A))) (δ / (2 * B)), by positivity, ?_⟩
  intro x hx w hwr
  have h := hJ x hx
  have hr1 : ‖w‖ ≤ δ / A := (hwr.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hr2 : ‖w‖ ≤ l / (2 * B ^ 3 * A) := (hwr.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hr3 : ‖w‖ ≤ δ / (2 * B) := hwr.trans (min_le_right _ _)
  rw [le_div_iff₀ hA0] at hr1
  rw [le_div_iff₀ (by positivity)] at hr2
  rw [le_div_iff₀ (by positivity)] at hr3
  have hw1 : A * ‖w‖ ≤ δ := by linarith
  have hw2 : B ^ 3 * (A * ‖w‖) ≤ l / 2 := by nlinarith
  have hw3 : 2 * B * ‖w‖ ≤ δ := by linarith
  have hwle1 : ‖w‖ ≤ 1 := h.norm_le_one_of hw3
  -- upper bound
  have hup := h.dist_sq_le hg hw3
  -- lower bound
  have hlow := h.sqrt_distJet_le_dist hg hA hAl hw1 hw2 ⟨_, h.isAdmissible_trial hw3⟩
  have hBw : B ^ 3 * ‖w‖ ≤ l / 2 :=
    le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg w) hA)
      (by positivity)) hw2
  have hF0 : 0 ≤ distJet g x w :=
    le_trans (by positivity) (h.distJet_ge_half hwle1 hBw)
  have hF1 := h.distJet_le hwle1
  have hk : 1 ≤ 1 + κ * (A * ‖w‖) ^ 3 := by
    have : 0 ≤ κ * (A * ‖w‖) ^ 3 := by positivity
    linarith
  have hsub := sub_sq_le_of_sqrt_le hF0 hk hlow
  have hsub' : 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * distJet g x w ≤
      4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 :=
    calc 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * distJet g x w
        ≤ 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * (2 * (B ^ 3 * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hF1 (by positivity)
      _ = 4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 := by ring
  have h51 : 0 ≤ 51 * B ^ 6 * ‖w‖ ^ 5 := by positivity
  have h4 : 0 ≤ 4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The expansion about the midpoint -/

/-- The jet of the squared distance about the midpoint `m` of two points with difference `Δ`:
`g(Δ, Δ) + (1/24) ∂_Δ ∂_Δ g(Δ, Δ) - (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))`, all at `m`. -/
def midJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m Δ : Fin n → ℝ) : ℝ :=
  Δ ⬝ᵥ (g m *ᵥ Δ) + (1 / 24) * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ))
    - (1 / 12) * (chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ))

/-- `p ⬝ (M q) = Σ_i p_i Σ_j q_j M_ij`. -/
theorem dot_mulVec_eq_nest (M : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ) :
    p ⬝ᵥ (M *ᵥ q) = ∑ i, p i * ∑ j, q j * M i j := by
  simp only [dotProduct, Matrix.mulVec]
  exact Finset.sum_congr rfl fun i _ => by
    congr 1; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Differentiating `Σ_k a_k F_k(s)` term by term. -/
theorem hasDerivAt_wsum {a : Fin n → ℝ} {F : Fin n → ℝ → ℝ} {F' : Fin n → ℝ} {s : ℝ}
    (h : ∀ k, HasDerivAt (F k) (F' k) s) :
    HasDerivAt (fun s => ∑ k, a k * F k s) (∑ k, a k * F' k) s :=
  HasDerivAt.fun_sum fun k _ => (h k).const_mul (a k)

/-- `|Σ_k a_k b_k| ≤ n ‖a‖ B` if `|b_k| ≤ B`. -/
theorem abs_wsum_le {a b : Fin n → ℝ} {B : ℝ} (hb : ∀ k, |b k| ≤ B) :
    |∑ k, a k * b k| ≤ n * ‖a‖ * B :=
  abs_sum_mul_le (norm_nonneg a) (abs_le_norm_apply a) hb

/-- The one-variable identity behind the midpoint form: expanding about `0`,
`ψ(-½) + ½ ψ'(-½) + ⅙ ψ''(-½) = ψ(0) + ψ''(0)/24` up to `K/3` if the third derivative is bounded
by `K` on `[-½, 0]` (the coefficient of `ψ''(0)` is `⅛ - ¼ + ⅙ = 1/24`). -/
theorem abs_midComb_le {ψ0 ψ1 ψ2 ψ3 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ0 (ψ1 s) s)
    (d1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ1 (ψ2 s) s)
    (d2 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ2 (ψ3 s) s)
    (hb : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, |ψ3 s| ≤ K) :
    |ψ0 (-1 / 2) + 1 / 2 * ψ1 (-1 / 2) + 1 / 6 * ψ2 (-1 / 2) - ψ0 0 - 1 / 24 * ψ2 0| ≤ K / 3 := by
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, -s / 2 ∈ Icc (-1 / 2 : ℝ) 0 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have c : ∀ (φ φ' : ℝ → ℝ) (c₀ : ℝ), (∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt φ (φ' s) s) →
      ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => c₀ * φ (-t / 2)) (-1 / 2 * c₀ * φ' (-s / 2)) s := by
    intro φ φ' c₀ h s hs
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    exact (((h _ (hm s hs)).comp s h1).const_mul c₀).congr_deriv (by ring)
  have hb' : ∀ (c₀ : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, |c₀ * ψ3 (-s / 2)| ≤ |c₀| * K := fun c₀ s hs => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb _ (hm s hs)) (abs_nonneg _)
  have t3 := taylor_aux_three (c ψ0 ψ1 1 d0) (c ψ1 ψ2 _ d1) (c ψ2 ψ3 _ d2)
    (hb' (-1 / 2 * (-1 / 2 * (-1 / 2 * 1))))
  have t2 := taylor_aux_two (c ψ1 ψ2 1 d1) (c ψ2 ψ3 _ d2) (hb' (-1 / 2 * (-1 / 2 * 1)))
  have t1 := taylor_aux_one (c ψ2 ψ3 1 d2) (hb' (-1 / 2 * 1))
  simp only [neg_zero, zero_div] at t1 t2 t3
  norm_num at t1 t2 t3
  rw [abs_le] at t1 t2 t3 ⊢
  constructor <;> nlinarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

/-- **The polynomial part about the midpoint.** If the third partial derivatives of `g` are
bounded by `M` on the segment from `m - Δ/2` to `m`, then the polynomial part of `distJet` at
`m - Δ/2` differs from `g(Δ, Δ) + (1/24) ∂_Δ ∂_Δ g(Δ, Δ)` at `m` by at most `n⁵ M ‖Δ‖⁵ / 3`. -/
theorem abs_jetPoly_mid_le (hg : IsCoordMetric g U) {m Δ : Fin n → ℝ} {M : ℝ}
    (hseg : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, m + s • Δ ∈ U)
    (hM : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ∀ i j k l p : Fin n,
      |pd p (pd l (pd k (fun y => g y i j))) (m + s • Δ)| ≤ M) :
    |Δ ⬝ᵥ (g (m - (1 / 2 : ℝ) • Δ) *ᵥ Δ)
      + (1 / 2) * (Δ ⬝ᵥ (dmat g (m - (1 / 2 : ℝ) • Δ) Δ *ᵥ Δ))
      + (1 / 6) * (Δ ⬝ᵥ (ddmat g (m - (1 / 2 : ℝ) • Δ) Δ Δ *ᵥ Δ))
      - Δ ⬝ᵥ (g m *ᵥ Δ) - (1 / 24) * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ))| ≤ n ^ 5 * M * ‖Δ‖ ^ 5 / 3 := by
  have e0 : ∀ z, Δ ⬝ᵥ (g z *ᵥ Δ) = ∑ i, Δ i * ∑ j, Δ j * g z i j := fun z =>
    dot_mulVec_eq_nest _ _ _
  have e1 : ∀ z, Δ ⬝ᵥ (dmat g z Δ *ᵥ Δ) =
      ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * pd k (fun y => g y i j) z := fun z => by
    rw [dot_mulVec_eq_nest]; rfl
  have e2 : ∀ z, Δ ⬝ᵥ (ddmat g z Δ Δ *ᵥ Δ) =
      ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * pd l (pd k (fun y => g y i j)) z :=
    fun z => by
      rw [dot_mulVec_eq_nest]
      simp only [ddmat, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  have key := abs_midComb_le
    (ψ0 := fun s => ∑ i, Δ i * ∑ j, Δ j * g (m + s • Δ) i j)
    (ψ1 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * pd k (fun y => g y i j) (m + s • Δ))
    (ψ2 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l *
      pd l (pd k (fun y => g y i j)) (m + s • Δ))
    (ψ3 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * ∑ p, Δ p *
      pd p (pd l (pd k (fun y => g y i j))) (m + s • Δ))
    (K := n ^ 5 * M * ‖Δ‖ ^ 5)
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j =>
      hasDerivAt_line (hg.smooth i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_line (hg.contDiffOn_pdg k i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_wsum fun l =>
        hasDerivAt_line (contDiffOn_pd (hg.contDiffOn_pdg k i j) hg.isOpen l) hg.isOpen
          (hseg s hs))
    (fun s hs => (abs_wsum_le fun i => abs_wsum_le fun j => abs_wsum_le fun k =>
      abs_wsum_le fun l => abs_wsum_le fun p => hM s hs i j k l p).trans_eq (by ring))
  have hx : m + (-1 / 2 : ℝ) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, neg_smul, ← sub_eq_add_neg]
  simp only [hx, zero_smul, add_zero] at key
  simp only [e0, e1, e2]
  exact key

end Lightlike.Upstream.GeodesicExpansion
