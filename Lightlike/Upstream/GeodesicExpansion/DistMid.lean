import Lightlike.Upstream.GeodesicExpansion.DistExpansion
import Mathlib

/-!
# The expansion of the squared distance about the midpoint

## Main declarations

* `abs_chrTerm_sub_le`: the Christoffel term `g(Γ(Δ, Δ), Γ(Δ, Δ))` varies Lipschitz-ly in the base
  point
* `IsRiemMetric.dist_sq_expansion_midpoint`: for `m` in a compact `K ⊆ U` and small `Δ`,
  `d(m - Δ/2, m + Δ/2)² = midJet g m Δ + O(‖Δ‖⁵)`; there is no cubic term about the midpoint
-/

open Matrix Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The Christoffel term at nearby points.** If on the segment from `m` to `m + w` the entries of
`g`, their first partial derivatives, the Christoffel symbols and their first partial derivatives
are bounded by `M`, then `g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m + w` and at `m` differ by at most
`3 n⁷ M³ ‖w‖ ‖Δ‖⁴`. -/
theorem abs_chrTerm_sub_le (hg : IsCoordMetric g U) {m w Δ : Fin n → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hseg : ∀ s ∈ Icc (0 : ℝ) 1, m + s • w ∈ U)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j k l : Fin n,
      |g (m + s • w) i j| ≤ M ∧ |pd k (fun y => g y i j) (m + s • w)| ≤ M ∧
      |christoffel g i j k (m + s • w)| ≤ M ∧
      |pd l (christoffel g i j k) (m + s • w)| ≤ M) :
    |chr g (m + w) Δ Δ ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
      - chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ)| ≤ 3 * n ^ 7 * M ^ 3 * ‖w‖ * ‖Δ‖ ^ 4 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hm0 : m + (0 : ℝ) • w = m := by simp
  have hm1 : m + (1 : ℝ) • w = m + w := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have gx : ∀ i j, |g (m + w) i j| ≤ M := fun i j => by
    simpa [hm1] using (hM 1 h1 i j i i).1
  have cm : ∀ i j k, |christoffel g i j k m| ≤ M := fun i j k => by
    simpa [hm0] using (hM 0 h0 i j k k).2.2.1
  have cx : ∀ i j k, |christoffel g i j k (m + w)| ≤ M := fun i j k => by
    simpa [hm1] using (hM 1 h1 i j k k).2.2.1
  have dg : ∀ i j, |g (m + w) i j - g m i j| ≤ n * M * ‖w‖ := fun i j =>
    taylor_one (hg.smooth i j) hg.isOpen hseg fun s hs k => (hM s hs i j k k).2.1
  have dc : ∀ i j k, |christoffel g i j k (m + w) - christoffel g i j k m| ≤
      n * M * ‖w‖ := fun i j k =>
    taylor_one (hg.contDiffOn_christoffel i j k) hg.isOpen hseg fun s hs l =>
      (hM s hs i j k l).2.2.2
  have nΓm : ‖chr g m Δ Δ‖ ≤ n ^ 2 * M * ‖Δ‖ * ‖Δ‖ := norm_chr_le hM0 cm
  have nΓx : ‖chr g (m + w) Δ Δ‖ ≤ n ^ 2 * M * ‖Δ‖ * ‖Δ‖ := norm_chr_le hM0 cx
  have nΓd : ‖chr g (m + w) Δ Δ - chr g m Δ Δ‖ ≤ n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have e : (chr g (m + w) Δ Δ - chr g m Δ Δ) i = ∑ j, Δ j * ∑ k, Δ k *
        (christoffel g i j k (m + w) - christoffel g i j k m) := by
      simp only [Pi.sub_apply, chr, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact abs_wsum_le fun j => abs_wsum_le fun k => dc i j k
  have bx : ∀ p q, |p ⬝ᵥ (g (m + w) *ᵥ q)| ≤ n ^ 2 * M * ‖p‖ * ‖q‖ := abs_dot_mulVec_le hM0 gx
  have bd : ∀ p q, |p ⬝ᵥ ((g (m + w) - g m) *ᵥ q)| ≤ n ^ 2 * (n * M * ‖w‖) * ‖p‖ * ‖q‖ :=
    abs_dot_mulVec_le (by positivity) fun i j => by rw [Matrix.sub_apply]; exact dg i j
  have e : chr g (m + w) Δ Δ ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
        - chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ)
      = (chr g (m + w) Δ Δ - chr g m Δ Δ) ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
        + chr g m Δ Δ ⬝ᵥ (g (m + w) *ᵥ (chr g (m + w) Δ Δ - chr g m Δ Δ))
        + chr g m Δ Δ ⬝ᵥ ((g (m + w) - g m) *ᵥ chr g m Δ Δ) := by
    simp only [sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub, Matrix.sub_mulVec]
    ring
  have ha : |(chr g (m + w) Δ Δ - chr g m Δ Δ) ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)| ≤
      n ^ 2 * M * (n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖))) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) := by
    refine (bx _ _).trans ?_; gcongr
  have hb : |chr g m Δ Δ ⬝ᵥ (g (m + w) *ᵥ (chr g (m + w) Δ Δ - chr g m Δ Δ))| ≤
      n ^ 2 * M * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) * (n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖))) := by
    refine (bx _ _).trans ?_; gcongr
  have hc : |chr g m Δ Δ ⬝ᵥ ((g (m + w) - g m) *ᵥ chr g m Δ Δ)| ≤
      n ^ 2 * (n * M * ‖w‖) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) := by
    refine (bd _ _).trans ?_; gcongr
  rw [e]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three ha hb hc
    _ = 3 * n ^ 7 * M ^ 3 * ‖w‖ * ‖Δ‖ ^ 4 := by ring

/-- **The expansion of the squared distance about the midpoint.** For a Riemannian coordinate
metric `g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `m ∈ K` and
`‖Δ‖ ≤ r`,
`|d(m - Δ/2, m + Δ/2)² - g(Δ, Δ) - Q_m(Δ)| ≤ C ‖Δ‖⁵`, with the quartic form
`Q_m(Δ) = (1/24) ∂_Δ ∂_Δ g(Δ, Δ) - (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m` (`midJet`). About the
midpoint there is no cubic term. -/
theorem IsRiemMetric.dist_sq_expansion_midpoint (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ m ∈ K, ∀ Δ : Fin n → ℝ, ‖Δ‖ ≤ r →
      |chartDist g U (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2 - midJet g m Δ| ≤
        C * ‖Δ‖ ^ 5 := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := hg.dist_sq_expansion hK' hρU
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound hK' hρU
  refine ⟨C₁ + n ^ 5 * M / 3 + n ^ 7 * M ^ 3 / 8, min r₁ ρ, lt_min hr₁ hρ, fun m hm Δ hΔ => ?_⟩
  have hΔ1 : ‖Δ‖ ≤ r₁ := hΔ.trans (min_le_left _ _)
  have hΔ2 : ‖Δ‖ ≤ ρ := hΔ.trans (min_le_right _ _)
  have hin : ∀ v : Fin n → ℝ, ‖v‖ ≤ ρ → m + v ∈ Metric.cthickening ρ K := fun v hv =>
    Metric.closedBall_subset_cthickening hm _
      (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hv)
  have hs1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ‖s • Δ‖ ≤ ρ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hs.2]
    nlinarith [mul_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s + 1 / 2) (norm_nonneg Δ)]
  have hmw : m + (-(1 / 2 : ℝ)) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [neg_smul, ← sub_eq_add_neg]
  have hnw : ‖(-(1 / 2 : ℝ)) • Δ‖ = ‖Δ‖ / 2 := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hs2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • (-(1 / 2 : ℝ)) • Δ‖ ≤ ρ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, hnw]
    nlinarith [mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) (norm_nonneg Δ)]
  have hx : m - (1 / 2 : ℝ) • Δ ∈ Metric.cthickening ρ K := by
    rw [← hmw]; exact hin _ (by rw [hnw]; linarith [norm_nonneg Δ])
  have hy : m - (1 / 2 : ℝ) • Δ + Δ = m + (1 / 2 : ℝ) • Δ := by module
  have E1 := h₁ _ hx Δ hΔ1
  rw [hy] at E1
  have E2 := abs_jetPoly_mid_le hg.coord (m := m) (Δ := Δ) (M := M)
    (fun s hs => hρU (hin _ (hs1 s hs)))
    (fun s hs i j k l p => (hM _ (hin _ (hs1 s hs)) i j k l p).2.2.2.2.1)
  have E3 := abs_chrTerm_sub_le hg.coord (m := m) (w := (-(1 / 2 : ℝ)) • Δ) (Δ := Δ) hM0
    (fun s hs => hρU (hin _ (hs2 s hs)))
    (fun s hs i j k l => by
      have h := hM _ (hin _ (hs2 s hs)) i j k l l
      exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
  rw [hmw, hnw] at E3
  unfold distJet at E1
  unfold midJet
  rw [abs_le] at E1 E2 E3 ⊢
  constructor <;> nlinarith [E1.1, E1.2, E2.1, E2.2, E3.1, E3.2]

end Lightlike.Upstream.GeodesicExpansion
