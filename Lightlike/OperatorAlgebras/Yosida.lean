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

lemma norm_tRes_le (hR : ℕ → H →L[ℂ] H) (hb : ∀ n w, ‖hR n w‖ ≤ (tn n)⁻¹ * ‖w‖) (n : ℕ) (w : H) :
    ‖((tn n : ℝ) : ℂ) • hR n w‖ ≤ 1 * ‖w‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tn_pos n)]
  calc tn n * ‖hR n w‖ ≤ tn n * ((tn n)⁻¹ * ‖w‖) := mul_le_mul_of_nonneg_left (hb n w) (tn_pos n).le
    _ = 1 * ‖w‖ := by rw [← mul_assoc, mul_inv_cancel₀ (tn_pos n).ne']

/-- **`t R (i t) y → i y`** for every `y`. -/
lemma tResP_tendsto (hA : IsSelfAdjoint A) (y : H) :
    Filter.Tendsto (fun n => ((tn n : ℝ) : ℂ) • resP hA n y) Filter.atTop (𝓝 (Complex.I • y)) := by
  refine tendsto_of_dense_bounded (T := fun n => ((tn n : ℝ) : ℂ) • resP hA n) (C := 1) zero_le_one
    (fun n w => norm_tRes_le (resP hA) (norm_resP_le hA) n w) hA.dense_domain Complex.I ?_ y
  intro w hw
  exact tResP_domain hA ⟨w, hw⟩

/-- **`t R (-i t) y → -i y`** for every `y`. -/
lemma tResM_tendsto (hA : IsSelfAdjoint A) (y : H) :
    Filter.Tendsto (fun n => ((tn n : ℝ) : ℂ) • resM hA n y) Filter.atTop (𝓝 ((-Complex.I) • y)) := by
  refine tendsto_of_dense_bounded (T := fun n => ((tn n : ℝ) : ℂ) • resM hA n) (C := 1) zero_le_one
    (fun n w => norm_tRes_le (resM hA) (norm_resM_le hA) n w) hA.dense_domain (-Complex.I) ?_ y
  intro w hw
  have := tResM_domain hA ⟨w, hw⟩
  simpa [neg_smul] using this

/-- **The approximants** `A_n = (t² / 2) (R (i t) + R (-i t))`, `t = n + 1`, bounded operators. -/
noncomputable def approx (hA : IsSelfAdjoint A) (n : ℕ) : H →L[ℂ] H :=
  ((((tn n) ^ 2 / 2 : ℝ) : ℂ)) • (resP hA n + resM hA n)

lemma approx_apply (hA : IsSelfAdjoint A) (n : ℕ) (y : H) :
    approx hA n y = ((((tn n) ^ 2 / 2 : ℝ) : ℂ)) • (resP hA n y + resM hA n y) := rfl

/-- On the domain, `A_n x = (i / 2) (t R (-i t) A x - t R (i t) A x)`. -/
lemma approx_apply_domain (hA : IsSelfAdjoint A) (n : ℕ) (x : A.domain) :
    approx hA n (x : H) = (Complex.I / 2) •
      (((tn n : ℝ) : ℂ) • resM hA n (A x : H) - ((tn n : ℝ) : ℂ) • resP hA n (A x : H)) := by
  have h1 : resP hA n (A x : H) = (x : H) + (Complex.I * (tn n : ℂ)) • resP hA n (x : H) :=
    resolvent_apply_A hA (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne') x
  have h2 : resM hA n (A x : H) = (x : H) + (-(Complex.I * (tn n : ℂ))) • resM hA n (x : H) :=
    resolvent_apply_A hA (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne') x
  rw [approx_apply, h1, h2]
  push_cast
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **`A_n x → A x` on the domain.** -/
theorem approx_tendsto (hA : IsSelfAdjoint A) (x : A.domain) :
    Filter.Tendsto (fun n => approx hA n (x : H)) Filter.atTop (𝓝 (A x : H)) := by
  simp only [approx_apply_domain]
  have h := ((tResM_tendsto hA (A x : H)).sub (tResP_tendsto hA (A x : H))).const_smul (Complex.I / 2)
  have e : (Complex.I / 2) • ((-Complex.I) • (A x : H) - Complex.I • (A x : H)) = (A x : H) := by
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  rwa [e] at h

/-- **The approximants are self-adjoint**: `⟪A_n y, w⟫ = ⟪y, A_n w⟫`. -/
theorem approx_selfadjoint (hA : IsSelfAdjoint A) (n : ℕ) (y w : H) :
    ⟪approx hA n y, w⟫_ℂ = ⟪y, approx hA n w⟫_ℂ := by
  have hP : ∀ y w : H, ⟪resP hA n y, w⟫_ℂ = ⟪y, resM hA n w⟫_ℂ := by
    intro y w
    have := resolvent_adjoint hA (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne')
      (by simpa using (tn_pos n).ne') y w
    unfold resP resM
    rw [this]
    congr 3
    simp
  have hM : ∀ y w : H, ⟪resM hA n y, w⟫_ℂ = ⟪y, resP hA n w⟫_ℂ := by
    intro y w
    have := resolvent_adjoint hA (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne')
      (by simpa using (tn_pos n).ne') y w
    unfold resP resM
    rw [this]
    congr 3
    simp
  rw [approx_apply, approx_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    hP, hM]
  simp only [Complex.conj_ofReal, map_div₀, map_pow, map_ofNat, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

end Lightlike.OperatorAlgebras
