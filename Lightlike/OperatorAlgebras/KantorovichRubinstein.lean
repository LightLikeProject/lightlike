import Lightlike.OperatorAlgebras.MongeKantorovich

/-!
# Kantorovich-Rubinstein duality on a compact metric space

W. Huang, R. Wang, Y. Wu, D. Meng, arXiv:2610.21070, Section 3.2.1, p. 5, (KR) (read): for Borel probability measures
`ν`, `η` on a compact metric space `(M, d)`,
`W₁(ν, η) = inf_{γ ∈ Π(ν, η)} ∫ d dγ = sup_{Lip(u) ≤ 1} ∫ u d(ν - η)`.

The proof here goes through the Hahn-Banach theorem and the Riesz-Markov-Kakutani theorem (Monge-Kantorovich duality
for the cost `d`, `exists_optimal_coupling`), then the `c`-transform: for `f(x) + g(y) ≤ d(x, y)` the function
`u(x) = inf_y (d(x, y) - g(y))` is `1`-Lipschitz with `f ≤ u` and `g ≤ -u`.

* `ctrans g`, `lipschitzWith_ctrans`, `le_ctrans`, `ctrans_le_neg`;
* `exists_optimal_coupling_dist`: an optimal coupling, `W₁(μ, ν) = ∫ d dσ`;
* `wasserstein1_eq_sSup`: (KR).
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The `c`-transform** `u(x) = inf_y (d(x, y) - g(y))` of a continuous `g` for the cost `d`. -/
noncomputable def ctrans (g : C(X, ℝ)) (x : X) : ℝ := ⨅ y, (dist x y - g y)

lemma bddBelow_ctrans (g : C(X, ℝ)) (x : X) : BddBelow (Set.range fun y => dist x y - g y) :=
  ⟨-‖g‖, by
    rintro _ ⟨y, rfl⟩
    have := (le_abs_self (g y)).trans (g.norm_coe_le_norm y)
    linarith [dist_nonneg (x := x) (y := y)]⟩

/-- `u(x) ≤ d(x, y) - g(y)`. -/
lemma ctrans_le (g : C(X, ℝ)) (x y : X) : ctrans g x ≤ dist x y - g y :=
  ciInf_le (bddBelow_ctrans g x) y

/-- **The `c`-transform is `1`-Lipschitz.** -/
lemma lipschitzWith_ctrans [Nonempty X] (g : C(X, ℝ)) : LipschitzWith 1 (ctrans g) :=
  LipschitzWith.of_le_add fun x x' => by
    have : ctrans g x - dist x x' ≤ ctrans g x' := le_ciInf fun y => by
      have h1 := ctrans_le g x y
      linarith [dist_triangle x x' y]
    linarith

/-- `f ≤ u` when `f(x) + g(y) ≤ d(x, y)`. -/
lemma le_ctrans [Nonempty X] {f g : C(X, ℝ)} (hfg : ∀ x y, f x + g y ≤ dist x y) (x : X) : f x ≤ ctrans g x :=
  le_ciInf fun y => by linarith [hfg x y]

/-- `u ≤ -g`: take `y = x` in the infimum. -/
lemma ctrans_le_neg (g : C(X, ℝ)) (x : X) : ctrans g x ≤ -g x := by
  have := ctrans_le g x x
  rwa [dist_self, zero_sub] at this

variable {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The distance as a continuous function on `X × X`. -/
def distC : C(X × X, ℝ) := ⟨fun p => dist p.1 p.2, continuous_dist⟩

/-- **An optimal coupling for the cost `d`**: `W₁(μ, ν) = ∫ d dσ`, and `∫ d dσ` is the least upper bound of the dual
values. -/
theorem exists_optimal_coupling_dist :
    ∃ σ ∈ couplings μ ν, wasserstein1 μ ν = ∫ p, dist p.1 p.2 ∂σ ∧
      IsLUB (dualValues μ ν distC) (∫ p, dist p.1 p.2 ∂σ) := by
  obtain ⟨σ, hσ, hmin, hlub⟩ := exists_optimal_coupling (μ := μ) (ν := ν) distC
  refine ⟨σ, hσ, le_antisymm (wasserstein1_le hσ) (le_csInf ⟨_, σ, hσ, rfl⟩ ?_), hlub⟩
  rintro _ ⟨π, hπ, rfl⟩
  exact hmin π hπ

/-- **Kantorovich-Rubinstein** (arXiv:2610.21070, Section 3.2.1, p. 5, (KR)):
`W₁(μ, ν) = sup {∫ u dμ - ∫ u dν | u 1-Lipschitz}`. -/
theorem wasserstein1_eq_sSup :
    wasserstein1 μ ν = sSup {r | ∃ u : X → ℝ, LipschitzWith 1 u ∧ r = ∫ x, u x ∂μ - ∫ x, u x ∂ν} := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain ⟨σ, hσ, hW, hlub⟩ := exists_optimal_coupling_dist (μ := μ) (ν := ν)
  have hlub' : IsLUB {r | ∃ u : X → ℝ, LipschitzWith 1 u ∧ r = ∫ x, u x ∂μ - ∫ x, u x ∂ν} (wasserstein1 μ ν) := by
    refine ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact integral_sub_le_wasserstein1 μ ν hu
    · rw [hW]
      refine hlub.2 fun r ⟨f, g, hfg, hr⟩ => ?_
      have hu := lipschitzWith_ctrans g
      have hint : ∀ m : Measure X, [IsFiniteMeasure m] → Integrable (ctrans g) m := fun m _ =>
        hu.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [hr]
      refine le_trans ?_ (hb ⟨ctrans g, hu, rfl⟩)
      have h1 : ∫ x, f x ∂μ ≤ ∫ x, ctrans g x ∂μ :=
        integral_mono (integrable_cont f) (hint μ) fun x => le_ctrans (fun x y => hfg (x, y)) x
      have h2 : ∫ x, g x ∂ν ≤ -∫ x, ctrans g x ∂ν := by
        rw [← integral_neg]
        exact integral_mono (integrable_cont g) (hint ν).neg fun x => by
          have := ctrans_le_neg g x
          simp only [Pi.neg_apply]; linarith
      linarith
  exact (hlub'.csSup_eq ⟨_, fun _ => (0 : ℝ), (LipschitzWith.const 0).weaken zero_le_one, rfl⟩).symm

end Lightlike.OperatorAlgebras.Transport
