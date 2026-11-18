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

/-- The parameters `tn n = n + 1 > 0` of the approximants. -/
def tn (n : ℕ) : ℝ := n + 1

lemma tn_pos (n : ℕ) : 0 < tn n := by unfold tn; positivity

lemma tn_tendsto : Filter.Tendsto tn Filter.atTop Filter.atTop := by
  unfold tn
  exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- The resolvent at `i t`. -/
noncomputable def resP (hA : IsSelfAdjoint A) (n : ℕ) : H →L[ℂ] H :=
  resolventCLM hA (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne')

/-- The resolvent at `-i t`. -/
noncomputable def resM (hA : IsSelfAdjoint A) (n : ℕ) : H →L[ℂ] H :=
  resolventCLM hA (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne')

lemma norm_resP_le (hA : IsSelfAdjoint A) (n : ℕ) (y : H) : ‖resP hA n y‖ ≤ (tn n)⁻¹ * ‖y‖ := by
  have := norm_resolvent_le hA (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne') y
  unfold resP
  simpa [abs_of_pos (tn_pos n)] using this

lemma norm_resM_le (hA : IsSelfAdjoint A) (n : ℕ) (y : H) : ‖resM hA n y‖ ≤ (tn n)⁻¹ * ‖y‖ := by
  have := norm_resolvent_le hA (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne') y
  unfold resM
  simpa [abs_of_pos (tn_pos n)] using this

lemma tendsto_norm_res_zero (hA : IsSelfAdjoint A) (y : H)
    {R : ℕ → H →L[ℂ] H} (hR : ∀ n w, ‖R n w‖ ≤ (tn n)⁻¹ * ‖w‖) :
    Filter.Tendsto (fun n => R n y) Filter.atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n => (hR n y).trans (le_refl _)) ?_
  have h1 : Filter.Tendsto (fun n => (tn n)⁻¹) Filter.atTop (𝓝 0) :=
    tn_tendsto.inv_tendsto_atTop
  simpa using h1.mul_const ‖y‖

lemma tResP_domain (hA : IsSelfAdjoint A) (x : A.domain) :
    Filter.Tendsto (fun n => ((tn n : ℝ) : ℂ) • resP hA n (x : H)) Filter.atTop
      (𝓝 (Complex.I • (x : H))) := by
  have key : ∀ n, ((tn n : ℝ) : ℂ) • resP hA n (x : H) =
      Complex.I • ((x : H) - resP hA n (A x : H)) := by
    intro n
    have h := resolvent_apply_A hA (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne') x
    have h' : resP hA n (A x : H) = (x : H) + (Complex.I * (tn n : ℂ)) • resP hA n (x : H) := h
    rw [h', sub_add_cancel_left, smul_neg, smul_smul, ← neg_smul]
    congr 1
    ring_nf
    simp
  simp only [key]
  have h0 := tendsto_norm_res_zero hA (A x : H) (R := resP hA) (norm_resP_le hA)
  have := ((tendsto_const_nhds (x := (x : H))).sub h0).const_smul Complex.I
  simpa using this

lemma tResM_domain (hA : IsSelfAdjoint A) (x : A.domain) :
    Filter.Tendsto (fun n => ((tn n : ℝ) : ℂ) • resM hA n (x : H)) Filter.atTop
      (𝓝 (-(Complex.I • (x : H)))) := by
  have key : ∀ n, ((tn n : ℝ) : ℂ) • resM hA n (x : H) =
      Complex.I • (resM hA n (A x : H) - (x : H)) := by
    intro n
    have h := resolvent_apply_A hA (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne') x
    have h' : resM hA n (A x : H) = (x : H) + (-(Complex.I * (tn n : ℂ))) • resM hA n (x : H) := h
    rw [h', add_sub_cancel_left, smul_smul]
    congr 1
    ring_nf
    simp
  simp only [key]
  have h0 := tendsto_norm_res_zero hA (A x : H) (R := resM hA) (norm_resM_le hA)
  have := ((h0).sub (tendsto_const_nhds (x := (x : H)))).const_smul Complex.I
  simpa using this

end Lightlike.OperatorAlgebras
