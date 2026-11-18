import Lightlike.OperatorAlgebras.Resolvent

/-!
# The approximants of a self-adjoint operator

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). For a self-adjoint `A` and `t > 0`, the
bounded operators `A_t = (t² / 2) (R (i t) + R (-i t))` are self-adjoint, and `A_t x → A x` as `t → ∞` for `x`
in the domain, where `R z` is the resolvent (`Resolvent.lean`). They are the symmetrized Yosida
approximants `t² A (A² + t²)⁻¹`; for a skew-adjoint operator the one-sided Yosida approximants are only
contractions, which is why these are used.
-/

open scoped InnerProductSpace LinearPMap Topology

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- `R_z (A x) = x + z R_z x` on the domain. -/
lemma resolvent_apply_A (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) (x : A.domain) :
    resolventCLM hA hz (A x : H) = (x : H) + z • resolventCLM hA hz (x : H) := by
  have h := resolvent_shift hA hz x
  rw [map_sub, map_smul] at h
  exact sub_eq_iff_eq_add.1 h

/-- **A uniformly bounded sequence of operators that converges to `c • id` on a dense set converges
everywhere.** -/
lemma tendsto_of_dense_bounded {T : ℕ → H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n y, ‖T n y‖ ≤ C * ‖y‖)
    {D : Set H} (hd : Dense D) (c : ℂ)
    (hD : ∀ y ∈ D, Filter.Tendsto (fun n => T n y) Filter.atTop (𝓝 (c • y))) (y : H) :
    Filter.Tendsto (fun n => T n y) Filter.atTop (𝓝 (c • y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := C + ‖c‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨y', hy', hdist⟩ := hd.exists_dist_lt y (show 0 < ε / (3 * K) by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hD y' hy')) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : ‖y - y'‖ < ε / (3 * K) := by rwa [← dist_eq_norm]
  have h3 : dist (T n y) (c • y) ≤ ‖T n (y - y')‖ + dist (T n y') (c • y') + ‖c‖ * ‖y - y'‖ := by
    have e : T n y - c • y = T n (y - y') + (T n y' - c • y') - c • (y - y') := by
      rw [map_sub, smul_sub]; abel
    rw [dist_eq_norm, dist_eq_norm, e]
    calc ‖T n (y - y') + (T n y' - c • y') - c • (y - y')‖
        ≤ ‖T n (y - y') + (T n y' - c • y')‖ + ‖c • (y - y')‖ := norm_sub_le _ _
      _ ≤ ‖T n (y - y')‖ + ‖T n y' - c • y'‖ + ‖c • (y - y')‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_smul]
  have h4 : ‖T n (y - y')‖ ≤ C * ‖y - y'‖ := hb n _
  have h5 : (C + ‖c‖) * ‖y - y'‖ < ε / 3 := by
    calc (C + ‖c‖) * ‖y - y'‖ ≤ K * ‖y - y'‖ := by gcongr; linarith
      _ < K * (ε / (3 * K)) := by gcongr
      _ = ε / 3 := by field_simp
  nlinarith

end Lightlike.OperatorAlgebras
