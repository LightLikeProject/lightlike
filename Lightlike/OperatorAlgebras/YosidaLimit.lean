import Lightlike.OperatorAlgebras.ResolventIdentity
import Lightlike.OperatorAlgebras.BoundedGroup

/-!
# The strong limit of the approximating unitary groups

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). Let `A` be self-adjoint and
`U_n t = exp (i t A_n)` (`BoundedGroup.lean`) with the commuting bounded self-adjoint approximants `A_n`
(`Yosida.lean`). For `x` in the domain, `‖U_n t x - U_m t x‖ ≤ |t| ‖A_n x - A_m x‖`, and `A_n x` converges, so
`U_n t x` is Cauchy; by density and isometry `U_n t y` is Cauchy for every `y`, and its limit is a unitary
group `U t` with `‖U_n t x - U t x‖ ≤ |t| ‖A_n x - A x‖` on the domain.
-/

open scoped InnerProductSpace LinearPMap Topology
open Filter

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- The approximating unitary `U_n t = exp (i t A_n)`. -/
noncomputable def Un (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  bdUnitary (approx_isSelfAdjoint hA n) t

lemma Un_apply (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) (y : H) :
    Un hA n t y = bdU (approx hA n) t y := rfl

/-- **The Cauchy estimate** for the approximating unitaries on the domain. -/
lemma Un_cauchy (hA : IsSelfAdjoint A) (n m : ℕ) (t : ℝ) (x : A.domain) :
    ‖Un hA n t (x : H) - Un hA m t (x : H)‖ ≤ |t| * ‖approx hA n (x : H) - approx hA m (x : H)‖ := by
  have := bdU_cauchy (approx_isSelfAdjoint hA n) (approx_isSelfAdjoint hA m) (approx_commute hA n m) t (x : H)
  simpa [Un_apply] using this

/-- For `x` in the domain, `U_n t x` is a Cauchy sequence. -/
lemma cauchySeq_Un_domain (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    CauchySeq fun n => Un hA n t (x : H) := by
  have hc : CauchySeq fun n => approx hA n (x : H) := (approx_tendsto hA x).cauchySeq
  rw [Metric.cauchySeq_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / (|t| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := Un_cauchy hA m n t x
  have h2 : ‖approx hA m (x : H) - approx hA n (x : H)‖ < ε / (|t| + 1) := by
    have := hN m hm n hn
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖Un hA m t (x : H) - Un hA n t (x : H)‖ ≤ |t| * ‖approx hA m (x : H) - approx hA n (x : H)‖ := h1
    _ ≤ |t| * (ε / (|t| + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg t]

/-- A sequence of isometries that is Cauchy on a dense set is Cauchy everywhere. -/
lemma cauchySeq_of_dense_isometries {V : ℕ → H ≃ₗᵢ[ℂ] H} {D : Set H} (hd : Dense D)
    (hD : ∀ y ∈ D, CauchySeq fun n => V n y) (y : H) : CauchySeq fun n => V n y := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y', hy', hdist⟩ := hd.exists_dist_lt y (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 (hD y' hy')) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hN m hm n hn
  have h2 : dist (V m y) (V m y') = dist y y' := (V m).dist_map y y'
  have h3 : dist (V n y') (V n y) = dist y' y := (V n).dist_map y' y
  have h4 := dist_triangle (V m y) (V m y') (V n y)
  have h5 := dist_triangle (V m y') (V n y') (V n y)
  rw [dist_comm y' y] at h3
  linarith

/-- For every `y`, `U_n t y` is a Cauchy sequence. -/
lemma cauchySeq_Un (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : CauchySeq fun n => Un hA n t y :=
  cauchySeq_of_dense_isometries (V := fun n => Un hA n t) hA.dense_domain
    (fun w hw => cauchySeq_Un_domain hA t ⟨w, hw⟩) y

/-- **The limit of the approximating unitary groups**: `U t y = lim U_n t y`. -/
noncomputable def Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : H :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_Un hA t y))

lemma tendsto_Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) :
    Tendsto (fun n => Un hA n t y) atTop (𝓝 (Ulim hA t y)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_Un hA t y))

lemma Ulim_zero (hA : IsSelfAdjoint A) (y : H) : Ulim hA 0 y = y := by
  have h := tendsto_Ulim hA 0 y
  have : (fun n => Un hA n 0 y) = fun _ => y := by
    funext n; simp [Un_apply, bdU_zero]
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds |>.symm ▸ rfl

lemma Ulim_add (hA : IsSelfAdjoint A) (t : ℝ) (y w : H) :
    Ulim hA t (y + w) = Ulim hA t y + Ulim hA t w := by
  have h := (tendsto_Ulim hA t y).add (tendsto_Ulim hA t w)
  have h2 := tendsto_Ulim hA t (y + w)
  simp only [map_add] at h2
  exact tendsto_nhds_unique h2 h

lemma Ulim_smul (hA : IsSelfAdjoint A) (t : ℝ) (c : ℂ) (y : H) :
    Ulim hA t (c • y) = c • Ulim hA t y := by
  have h := (tendsto_Ulim hA t y).const_smul c
  have h2 := tendsto_Ulim hA t (c • y)
  simp only [map_smul] at h2
  exact tendsto_nhds_unique h2 h

lemma norm_Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : ‖Ulim hA t y‖ = ‖y‖ := by
  have h := (tendsto_Ulim hA t y).norm
  have : (fun n => ‖Un hA n t y‖) = fun _ => ‖y‖ := by
    funext n; exact (Un hA n t).norm_map y
  rw [this] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds)

lemma Ulim_add_time (hA : IsSelfAdjoint A) (s t : ℝ) (y : H) :
    Ulim hA (s + t) y = Ulim hA s (Ulim hA t y) := by
  -- `U_n s (U_n t y) → U s (U t y)`
  have h1 : Tendsto (fun n => Un hA n (s + t) y) atTop (𝓝 (Ulim hA s (Ulim hA t y))) := by
    have e : ∀ n, Un hA n (s + t) y = Un hA n s (Un hA n t y) := fun n => by
      simp only [Un_apply, bdU_add, ContinuousLinearMap.mul_apply]
    simp only [e]
    -- split `U_n s (U_n t y) - U s (U t y) = U_n s (U_n t y - U t y) + (U_n s - U s) (U t y)`
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hA1 : Tendsto (fun n => ‖Un hA n t y - Ulim hA t y‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_Ulim hA t y)
    have hA2 : Tendsto (fun n => ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_Ulim hA s (Ulim hA t y))
    have hsum := hA1.add hA2
    rw [add_zero] at hsum
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
    have : Un hA n s (Un hA n t y) - Ulim hA s (Ulim hA t y) =
        Un hA n s (Un hA n t y - Ulim hA t y) + (Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)) := by
      rw [map_sub]; abel
    rw [this]
    calc ‖Un hA n s (Un hA n t y - Ulim hA t y) + (Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y))‖
        ≤ ‖Un hA n s (Un hA n t y - Ulim hA t y)‖ + ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖ :=
          norm_add_le _ _
      _ = ‖Un hA n t y - Ulim hA t y‖ + ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖ := by
          rw [(Un hA n s).norm_map]
  exact tendsto_nhds_unique (tendsto_Ulim hA (s + t) y) h1

/-- **The limit unitary** `U t`. -/
noncomputable def Uunit (hA : IsSelfAdjoint A) (t : ℝ) : H ≃ₗᵢ[ℂ] H where
  toFun := Ulim hA t
  invFun := Ulim hA (-t)
  map_add' := Ulim_add hA t
  map_smul' c y := Ulim_smul hA t c y
  left_inv y := by
    show Ulim hA (-t) (Ulim hA t y) = y
    rw [← Ulim_add_time, neg_add_cancel, Ulim_zero]
  right_inv y := by
    show Ulim hA t (Ulim hA (-t) y) = y
    rw [← Ulim_add_time, add_neg_cancel, Ulim_zero]
  norm_map' := norm_Ulim hA t

lemma Uunit_apply (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : Uunit hA t y = Ulim hA t y := rfl

/-- **The estimate** `‖U_n t x - U t x‖ ≤ |t| ‖A_n x - A x‖` for `x` in the domain. -/
lemma Un_sub_Ulim_le (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) (x : A.domain) :
    ‖Un hA n t (x : H) - Ulim hA t (x : H)‖ ≤ |t| * ‖approx hA n (x : H) - A x‖ := by
  have h1 : Tendsto (fun m => ‖Un hA n t (x : H) - Un hA m t (x : H)‖) atTop
      (𝓝 ‖Un hA n t (x : H) - Ulim hA t (x : H)‖) :=
    (tendsto_const_nhds.sub (tendsto_Ulim hA t (x : H))).norm
  have h2 : Tendsto (fun m => |t| * ‖approx hA n (x : H) - approx hA m (x : H)‖) atTop
      (𝓝 (|t| * ‖approx hA n (x : H) - A x‖)) :=
    (tendsto_const_nhds.sub (approx_tendsto hA x)).norm.const_mul _
  exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun m => Un_cauchy hA n m t x)

/-- On the domain, `t ↦ U t x` is continuous. -/
lemma continuous_Ulim_domain (hA : IsSelfAdjoint A) (x : A.domain) :
    Continuous fun t : ℝ => Ulim hA t (x : H) := by
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  set S : Set ℝ := Set.Icc (t0 - 1) (t0 + 1) with hS
  have hSn : S ∈ 𝓝 t0 := Icc_mem_nhds (by linarith) (by linarith)
  have hu : TendstoUniformlyOn (fun n t => Un hA n t (x : H)) (fun t => Ulim hA t (x : H)) atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hT : 0 < |t0| + 1 := by positivity
    have h0 := (Metric.tendsto_atTop.1 (tendsto_iff_norm_sub_tendsto_zero.1 (approx_tendsto hA x)))
      (ε / (|t0| + 1)) (by positivity)
    obtain ⟨N, hN⟩ := h0
    filter_upwards [eventually_ge_atTop N] with n hn t ht
    have hb : |t| ≤ |t0| + 1 := by
      have h1 : |t - t0| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      calc |t| = |t0 + (t - t0)| := by ring_nf
        _ ≤ |t0| + |t - t0| := abs_add_le _ _
        _ ≤ |t0| + 1 := by linarith
    rw [dist_comm, dist_eq_norm]
    have h1 := Un_sub_Ulim_le hA n t x
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖Un hA n t (x : H) - Ulim hA t (x : H)‖ ≤ |t| * ‖approx hA n (x : H) - A x‖ := h1
      _ ≤ (|t0| + 1) * ‖approx hA n (x : H) - A x‖ := by gcongr
      _ < (|t0| + 1) * (ε / (|t0| + 1)) := by gcongr
      _ = ε := by field_simp
  have hcont : ContinuousOn (fun t => Ulim hA t (x : H)) S :=
    hu.continuousOn (Eventually.of_forall fun n =>
      (continuous_bdU_apply (approx hA n) (x : H)).continuousOn).frequently
  exact hcont.continuousAt hSn

end Lightlike.OperatorAlgebras
