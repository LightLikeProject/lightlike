import Lightlike.Geodesic.TwoPoint
import Mathlib.Analysis.Convex.Deriv

/-!
# Convex neighbourhoods

Every point `x` of the domain `U` of a coordinate metric (of any signature) has arbitrarily small
open neighbourhoods `C` that are normal neighbourhoods of each of their points: for every
`q ∈ C` the exponential map at `q` is a diffeomorphism from a star-shaped open set onto `C`
(`Lightlike.Geodesic.exists_convex_neighbourhood`).

The proof follows the source, in the given coordinates instead of normal coordinates: the
function `N q = ∑ i, (q i - x i)²` is convex along geodesics close to `x`
(`IsGeodesicOn.convexOn_sqDist`), because its second derivative along a geodesic with velocity
`w` is `2 ∑ w_i² - 2 ∑ (q_i - x_i) Γ^i(w, w)`, and the Christoffel term is small near `x`.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Definition 2.2.4 (page 47) and
  Theorem 2.2.7 (pages 49–50), equations (2.2.9)–(2.2.11).
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The Euclidean squared distance of `q` from `x` in the coordinates. -/
def sqDist (x q : Fin n → ℝ) : ℝ := ∑ i, (q i - x i) ^ 2

lemma sqDist_self (x : Fin n → ℝ) : sqDist x x = 0 := by simp [sqDist]

lemma continuous_sqDist (x : Fin n → ℝ) : Continuous (sqDist x) := by
  unfold sqDist; fun_prop

/-- A point with `sqDist x q < r²` is within `r` of `x` in the norm. -/
lemma dist_lt_of_sqDist_lt {x q : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (h : sqDist x q < r ^ 2) :
    Dist.dist q x < r := by
  rw [dist_pi_lt_iff hr]
  intro i
  have h1 : (q i - x i) ^ 2 ≤ sqDist x q :=
    Finset.single_le_sum (f := fun i => (q i - x i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt h1 h) hr.le

/-- The squared sup norm is at most the sum of the squares of the coordinates. -/
lemma norm_sq_le_sum_sq (w : Fin n → ℝ) : ‖w‖ ^ 2 ≤ ∑ i, w i ^ 2 := by
  have hS : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : ‖w‖ ≤ Real.sqrt (∑ i, w i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => w i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖w‖ ^ 2 ≤ Real.sqrt (∑ i, w i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ∑ i, w i ^ 2 := Real.sq_sqrt hS

/-- **The squared coordinate distance is convex along geodesics near `x`** (Kunzinger–Steinbauer,
(2.2.10)–(2.2.11)). Let `γ` be a geodesic on `(-1, 2)` with velocity `w` such that on `[0, 1]`
it stays within `ε₀` of `x` and its acceleration is bounded by `A ‖w‖²`, with `n ε₀ A ≤ 1`.
Then `t ↦ ∑ i, (γ t i - x i)²` is convex on `[0, 1]`. -/
theorem IsGeodesicOn.convexOn_sqDist {γ w : ℝ → Fin n → ℝ} {x : Fin n → ℝ} {A ε₀ : ℝ}
    (hgeo : IsGeodesicOn g γ w (Ioo (-1) 2)) (hε₀ : 0 ≤ ε₀)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖accel g (γ t) (w t)‖ ≤ A * ‖w t‖ ^ 2)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - x‖ ≤ ε₀) (hsmall : (n : ℝ) * ε₀ * A ≤ 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => sqDist x (γ t)) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f1 : ℝ → ℝ := fun t => ∑ i, (w t i * (γ t i - x i) + (γ t i - x i) * w t i) with hf1
  set f2 : ℝ → ℝ := fun t => ∑ i, ((accel g (γ t) (w t) i * (γ t i - x i) + w t i * w t i) +
    (w t i * w t i + (γ t i - x i) * accel g (γ t) (w t) i)) with hf2
  have hγi : ∀ t ∈ Ioo (-1 : ℝ) 2, ∀ i, HasDerivAt (fun s => γ s i - x i) (w t i) t :=
    fun t ht i => (hasDerivAt_pi.mp (hgeo.pos t ht) i).sub_const (x i)
  have hwi : ∀ t ∈ Ioo (-1 : ℝ) 2, ∀ i,
      HasDerivAt (fun s => w s i) (accel g (γ t) (w t) i) t :=
    fun t ht i => hasDerivAt_pi.mp (hgeo.vel t ht) i
  have hd1 : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt (fun t => sqDist x (γ t)) (f1 t) t := by
    intro t ht
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hγi t ht i).mul (hγi t ht i)
    have h2 : (fun t => sqDist x (γ t)) = fun s => ∑ i, (γ s i - x i) * (γ s i - x i) := by
      funext s; simp only [sqDist, sq]
    rw [h2]
    exact h1
  have hd2 : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt f1 (f2 t) t := by
    intro t ht
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hwi t ht i).mul (hγi t ht i)).add ((hγi t ht i).mul (hwi t ht i))
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 2, deriv (fun t => sqDist x (γ t)) t = f1 t :=
    fun t ht => (hd1 t ht).deriv
  have hint : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  have hIoo : Ioo (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hev : ∀ t ∈ Ioo (-1 : ℝ) 2, deriv (fun t => sqDist x (γ t)) =ᶠ[𝓝 t] f1 := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hderiv s hs
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 1)
    (fun t ht => (hd1 t (hsub ht)).continuousAt.continuousWithinAt) ?_ ?_ ?_
  · rw [hint]
    exact fun t ht => (hd1 t (hIoo ht)).differentiableAt.differentiableWithinAt
  · rw [hint]
    exact fun t ht => (((hd2 t (hIoo ht)).congr_of_eventuallyEq
      (hev t (hIoo ht))).differentiableAt).differentiableWithinAt
  · rw [hint]
    intro t ht
    have ht' := hIoo ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have h3 : deriv^[2] (fun t => sqDist x (γ t)) t = f2 t := by
      show deriv (deriv (fun t => sqDist x (γ t))) t = f2 t
      exact ((hd2 t ht').congr_of_eventuallyEq (hev t ht')).deriv
    rw [h3]
    set S : ℝ := ∑ i, w t i ^ 2 with hS
    set acc := accel g (γ t) (w t) with hacc
    have hw2 : ‖w t‖ ^ 2 ≤ S := norm_sq_le_sum_sq (w t)
    have hterm : ∀ i, -(ε₀ * (A * ‖w t‖ ^ 2)) ≤ (γ t i - x i) * acc i := by
      intro i
      have h4 : |γ t i - x i| ≤ ε₀ := by
        have := norm_le_pi_norm (γ t - x) i
        rw [Real.norm_eq_abs] at this
        exact this.trans (hclose t htI)
      have h5 : |acc i| ≤ A * ‖w t‖ ^ 2 := by
        have := norm_le_pi_norm acc i
        rw [Real.norm_eq_abs] at this
        exact this.trans (hB t htI)
      have h6 : |(γ t i - x i) * acc i| ≤ ε₀ * (A * ‖w t‖ ^ 2) := by
        rw [abs_mul]
        exact mul_le_mul h4 h5 (abs_nonneg _) hε₀
      exact (abs_le.1 h6).1
    have hsum : -((n : ℝ) * (ε₀ * (A * ‖w t‖ ^ 2))) ≤ ∑ i, (γ t i - x i) * acc i := by
      have h7 : ∑ _i : Fin n, -(ε₀ * (A * ‖w t‖ ^ 2)) ≤ ∑ i, (γ t i - x i) * acc i :=
        Finset.sum_le_sum fun i _ => hterm i
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h7
    have hf2eq : f2 t = 2 * S + 2 * ∑ i, (γ t i - x i) * acc i := by
      simp only [hf2, hS, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hf2eq]
    have h8 : (n : ℝ) * (ε₀ * (A * ‖w t‖ ^ 2)) = (n * ε₀ * A) * ‖w t‖ ^ 2 := by ring
    have h9 : (n * ε₀ * A) * ‖w t‖ ^ 2 ≤ 1 * ‖w t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
    nlinarith

/-- **Existence of convex neighbourhoods** (Kunzinger–Steinbauer, Theorem 2.2.7, for a coordinate
metric of any signature). Every `x ∈ U` has, inside any ball about `x`, an open neighbourhood
`C ⊆ U` that is a normal neighbourhood of each of its points: for every `q ∈ C` there is an open
partial homeomorphism `φ`, smooth with smooth inverse, from a star-shaped open set containing
`0` onto `C`, with `φ 0 = q`, such that for every `v` in its source `t ↦ φ (t • v)` on `[0, 1]`
is a geodesic from `q` with initial velocity `v`. So `φ` is the exponential map at `q`, and any
two points of `C` are joined by a geodesic inside `C`. -/
theorem exists_convex_neighbourhood (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (Fin n → ℝ), IsOpen C ∧ x ∈ C ∧ C ⊆ ball x ε ∧ C ⊆ U ∧
      ∀ q ∈ C, ∃ φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
        (0 : Fin n → ℝ) ∈ φ.source ∧
        (∀ v ∈ φ.source, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ φ.source) ∧
        φ.target = C ∧ φ 0 = q ∧ ContDiffOn ℝ ∞ φ φ.source ∧
        ContDiffOn ℝ ∞ φ.symm φ.target ∧
        ∀ v ∈ φ.source, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = q ∧ w 0 = v ∧
          IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t = φ (t • v) := by
  obtain ⟨ρ, E, Θ, hρ, hE0, hEs, hEU, hEg, hxΘ, hΘsub, hΘeq, hΘs, hΘi⟩ :=
    exists_twoPoint_diffeo hg hx
  obtain ⟨R, hR, hRU⟩ : ∃ R > 0, closedBall x R ⊆ U := by
    obtain ⟨R, hR, hb⟩ := Metric.isOpen_iff.mp hg.isOpen x hx
    exact ⟨R / 2, half_pos hR, (closedBall_subset_ball (half_lt_self hR)).trans hb⟩
  obtain ⟨A, hA, hB⟩ := exists_accel_bound hg (isCompact_closedBall x R) hRU
  have hnA : 0 ≤ (n : ℝ) * A := mul_nonneg (Nat.cast_nonneg n) hA
  have hnA1 : 0 < (n : ℝ) * A + 1 := by linarith
  set ε₀ : ℝ := min (min ε R) (1 / ((n : ℝ) * A + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (lt_min hε hR) (div_pos one_pos hnA1)
  have hε₀ε : ε₀ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀R : ε₀ ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hsmall : (n : ℝ) * ε₀ * A ≤ 1 := by
    have h1 : ε₀ ≤ 1 / ((n : ℝ) * A + 1) := min_le_right _ _
    have h2 : (n : ℝ) * ε₀ * A = (n * A) * ε₀ := by ring
    rw [h2]
    calc (n : ℝ) * A * ε₀ ≤ (n * A) * (1 / ((n : ℝ) * A + 1)) :=
          mul_le_mul_of_nonneg_left h1 hnA
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one hnA1]; linarith
  have hx0ρ : (x, (0 : Fin n → ℝ)) ∈ ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ :=
    ⟨mem_ball_self hρ, mem_ball_self hρ⟩
  have hEcont : ContinuousAt E (x, 0) :=
    (hEs.contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx0ρ)).continuousAt
  have hnh : Θ.source ∩ E ⁻¹' ball x ε₀ ∈ 𝓝 (x, (0 : Fin n → ℝ)) :=
    inter_mem (Θ.open_source.mem_nhds hxΘ)
      (hEcont.preimage_mem_nhds (by rw [hE0 x (mem_ball_self hρ)]; exact ball_mem_nhds x hε₀))
  obtain ⟨ρ₂, hρ₂, hW⟩ := Metric.mem_nhds_iff.1 hnh
  have hWmk : ∀ (p v : Fin n → ℝ), p ∈ ball x ρ₂ → v ∈ ball (0 : Fin n → ℝ) ρ₂ →
      ((p, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball (x, (0 : Fin n → ℝ)) ρ₂ := fun p v hp hv => by
    rw [mem_ball, Prod.dist_eq]; exact max_lt hp hv
  have hWfst : ∀ q ∈ ball (x, (0 : Fin n → ℝ)) ρ₂,
      q.1 ∈ ball x ρ₂ ∧ q.2 ∈ ball (0 : Fin n → ℝ) ρ₂ := fun q hq => by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq; exact hq
  have hWsrc : ball (x, (0 : Fin n → ℝ)) ρ₂ ⊆ Θ.source := fun q hq => (hW hq).1
  have hWE : ∀ q ∈ ball (x, (0 : Fin n → ℝ)) ρ₂, E q ∈ ball x ε₀ := fun q hq => (hW hq).2
  have hWρ : ∀ q ∈ ball (x, (0 : Fin n → ℝ)) ρ₂,
      q.1 ∈ ball x ρ ∧ q.2 ∈ ball (0 : Fin n → ℝ) ρ := fun q hq => hΘsub (hWsrc hq)
  have himg : IsOpen (Θ '' ball (x, (0 : Fin n → ℝ)) ρ₂) :=
    (Θ.isOpen_image_iff_of_subset_source hWsrc).2 isOpen_ball
  have hxx : ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ Θ '' ball (x, (0 : Fin n → ℝ)) ρ₂ := by
    refine ⟨(x, 0), mem_ball_self hρ₂, ?_⟩
    rw [hΘeq _ hxΘ, hE0 x (mem_ball_self hρ)]
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.1 himg _ hxx
  set r₄ : ℝ := min r₃ ε₀ with hr₄def
  have hr₄ : 0 < r₄ := lt_min hr₃ hε₀
  set C : Set (Fin n → ℝ) := {q | sqDist x q < r₄ ^ 2} with hC
  have hCopen : IsOpen C := isOpen_lt (continuous_sqDist x) continuous_const
  have hxC : x ∈ C := by
    show sqDist x x < r₄ ^ 2
    rw [sqDist_self]; positivity
  have hCdist : ∀ q ∈ C, Dist.dist q x < r₄ := fun q hq => dist_lt_of_sqDist_lt hr₄ hq
  -- two points of `C` are joined through `Θ`
  have hpair : ∀ q ∈ C, ∀ b ∈ C, ∃ v : Fin n → ℝ,
      ((q, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball (x, (0 : Fin n → ℝ)) ρ₂ ∧ E (q, v) = b ∧
        Θ.symm (q, b) = (q, v) := by
    intro q hq b hb
    have hmem : ((q, b) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball (x, x) r₃ := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (lt_of_lt_of_le (hCdist q hq) (min_le_left _ _))
        (lt_of_lt_of_le (hCdist b hb) (min_le_left _ _))
    obtain ⟨⟨q', v⟩, hq'v, hΘq⟩ := hr₃sub hmem
    rw [hΘeq _ (hWsrc hq'v)] at hΘq
    have h1 : q' = q := congrArg Prod.fst hΘq
    have h2 : E (q', v) = b := congrArg Prod.snd hΘq
    subst h1
    refine ⟨v, hq'v, h2, ?_⟩
    have h3 := Θ.left_inv (hWsrc hq'v)
    rw [hΘeq _ (hWsrc hq'v), h2] at h3
    exact h3
  -- geodesics with endpoints in `C` stay in `C`
  have hseg : ∀ q ∈ C, ∀ v : Fin n → ℝ,
      ((q, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball (x, (0 : Fin n → ℝ)) ρ₂ →
      sqDist x (E (q, v)) < r₄ ^ 2 → ∀ t ∈ Icc (0 : ℝ) 1, sqDist x (E (q, t • v)) < r₄ ^ 2 := by
    intro q hq v hqv hEv t ht
    obtain ⟨hq2, hv2⟩ := hWfst _ hqv
    have hρq := hWρ _ hqv
    obtain ⟨γ, w, hγ0, hw0, hgeo, hγE⟩ := hEg q hρq.1 v hρq.2
    have htv : ∀ τ ∈ Icc (0 : ℝ) 1,
        ((q, τ • v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball (x, (0 : Fin n → ℝ)) ρ₂ := by
      intro τ hτ
      refine hWmk q _ hq2 ?_
      have hv3 := mem_ball_zero_iff.1 hv2
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      nlinarith [norm_nonneg v, hτ.2, hτ.1]
    have hγτ : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ = E (q, τ • v) := fun τ hτ =>
      hγE τ ⟨by linarith [hτ.1], hτ.2⟩
    have hclose : ∀ τ ∈ Icc (0 : ℝ) 1, ‖γ τ - x‖ ≤ ε₀ := fun τ hτ => by
      rw [hγτ τ hτ, ← dist_eq_norm]; exact (mem_ball.1 (hWE _ (htv τ hτ))).le
    have hBγ : ∀ τ ∈ Icc (0 : ℝ) 1, ‖accel g (γ τ) (w τ)‖ ≤ A * ‖w τ‖ ^ 2 := fun τ hτ =>
      hB _ (by rw [mem_closedBall, dist_eq_norm]; exact (hclose τ hτ).trans hε₀R) _
    have hconv := hgeo.convexOn_sqDist hε₀.le hBγ hclose hsmall
    have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hle := hconv.le_on_segment h01 h11 (z := t) (by rw [segment_eq_Icc zero_le_one]; exact ht)
    rw [← hγτ t ht]
    refine lt_of_le_of_lt hle (max_lt ?_ ?_)
    · show sqDist x (γ 0) < r₄ ^ 2
      rw [hγ0]; exact hq
    · show sqDist x (γ 1) < r₄ ^ 2
      rw [hγτ 1 h11, one_smul]; exact hEv
  refine ⟨C, hCopen, hxC, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · exact mem_ball.2 (lt_of_lt_of_le (hCdist q hq) ((min_le_right _ _).trans hε₀ε))
  · exact hRU (mem_closedBall.2 ((hCdist q hq).le.trans ((min_le_right _ _).trans hε₀R)))
  · -- the exponential chart at `q`
    obtain ⟨v₀, hqv₀, -, -⟩ := hpair q hq q hq
    have hq2 : q ∈ ball x ρ₂ := (hWfst _ hqv₀).1
    have hqρ : q ∈ ball x ρ := (hWρ _ hqv₀).1
    have hmapsρ : MapsTo (fun v : Fin n → ℝ => ((q, v) : (Fin n → ℝ) × (Fin n → ℝ)))
        (ball (0 : Fin n → ℝ) ρ₂) (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) := fun v hv =>
      hWρ _ (hWmk q v hq2 hv)
    have hιq : ContDiff ℝ ∞ (fun v : Fin n → ℝ => ((q, v) : (Fin n → ℝ) × (Fin n → ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have hEq : ContDiffOn ℝ ∞ (fun v : Fin n → ℝ => E (q, v)) (ball (0 : Fin n → ℝ) ρ₂) :=
      hEs.comp hιq.contDiffOn hmapsρ
    have hNq : ContinuousOn (fun v : Fin n → ℝ => sqDist x (E (q, v)))
        (ball (0 : Fin n → ℝ) ρ₂) :=
      (continuous_sqDist x).comp_continuousOn hEq.continuousOn
    have hpairT : ∀ b ∈ C, ((q, b) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ Θ.target := by
      intro b hb
      obtain ⟨v, hqv, hEv, -⟩ := hpair q hq b hb
      have h1 := Θ.map_source (hWsrc hqv)
      rwa [hΘeq _ (hWsrc hqv), hEv] at h1
    have hsymmS : ContDiffOn ℝ ∞ (fun b : Fin n → ℝ => (Θ.symm (q, b)).2) C :=
      contDiff_snd.comp_contDiffOn (hΘi.comp hιq.contDiffOn hpairT)
    set Sq : Set (Fin n → ℝ) :=
      ball (0 : Fin n → ℝ) ρ₂ ∩ (fun v : Fin n → ℝ => sqDist x (E (q, v))) ⁻¹' Iio (r₄ ^ 2)
      with hSq
    let φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
      { toFun := fun v => E (q, v)
        invFun := fun b => (Θ.symm (q, b)).2
        source := Sq
        target := C
        map_source' := fun v hv => hv.2
        map_target' := fun b hb => by
          obtain ⟨v, hqv, hEv, hsymm⟩ := hpair q hq b hb
          show (Θ.symm (q, b)).2 ∈ Sq
          rw [hsymm]
          exact ⟨(hWfst _ hqv).2, by show sqDist x (E (q, v)) < r₄ ^ 2; rw [hEv]; exact hb⟩
        left_inv' := fun v hv => by
          have hqv := hWmk q v hq2 hv.1
          have h1 := Θ.left_inv (hWsrc hqv)
          rw [hΘeq _ (hWsrc hqv)] at h1
          show (Θ.symm (q, E (q, v))).2 = v
          rw [h1]
        right_inv' := fun b hb => by
          obtain ⟨v, hqv, hEv, hsymm⟩ := hpair q hq b hb
          show E (q, (Θ.symm (q, b)).2) = b
          rw [hsymm]; exact hEv
        open_source := hNq.isOpen_inter_preimage isOpen_ball isOpen_Iio
        open_target := hCopen
        continuousOn_toFun := hEq.continuousOn.mono inter_subset_left
        continuousOn_invFun := hsymmS.continuousOn }
    refine ⟨φ, ?_, ?_, rfl, hE0 q hqρ, hEq.mono inter_subset_left, hsymmS, ?_⟩
    · refine ⟨mem_ball_self hρ₂, ?_⟩
      show sqDist x (E (q, 0)) < r₄ ^ 2
      rw [hE0 q hqρ]; exact hq
    · intro v hv t ht
      refine ⟨?_, hseg q hq v (hWmk q v hq2 hv.1) hv.2 t ht⟩
      have hv3 := mem_ball_zero_iff.1 hv.1
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg v, ht.2, ht.1]
    · intro v hv
      obtain ⟨γ, w, hγ0, hw0, hgeo, hγE⟩ := hEg q hqρ v (hWρ _ (hWmk q v hq2 hv.1)).2
      exact ⟨γ, w, hγ0, hw0, hgeo, fun t ht => hγE t ⟨by linarith [ht.1], ht.2⟩⟩

end Lightlike.Geodesic
